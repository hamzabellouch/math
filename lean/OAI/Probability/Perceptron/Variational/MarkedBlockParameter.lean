import Mathlib
import OAI.Probability.Perceptron.Variational.DecoratedTiltTotal

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

lemma markedBlockProbability_parameter_measurable {X S : Type*}
    [MeasurableSpace X] [MeasurableSpace S]
    (ns : List (ℕ × (X×S → ℝ≥0∞)))
    (hm : ∀ nf ∈ ns, Measurable nf.2) (m : ℕ) :
    Measurable (fun p : X×(Measure (ℝ×S)×(Fin m → ℝ)) =>
      markedBlockProbability (ns.map (fun nf => (nf.1,fun s => nf.2 (p.1,s))))
        p.2.1 p.2.2) := by
  induction ns generalizing m with
  | nil => exact measurable_const
  | cons nf ns ih =>
    let κ : Kernel (X×(Measure (ℝ×S)×(Fin m → ℝ))) (ℝ×S) :=
      markedStableMassKernel.comap (fun p => p.2.1) measurable_snd.fst
    have hD : Measurable (fun p : (X×(Measure (ℝ×S)×(Fin m → ℝ)))×(ℝ×S) =>
        markedBlockProbability (ns.map (fun nf => (nf.1,fun s => nf.2 (p.1.1,s))))
          p.1.2.1 (Fin.cons p.2.1 p.1.2.2)) := by
      exact (ih (fun r hr => hm r (List.mem_cons_of_mem nf hr)) (m+1)).comp
        (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk
          (measurable_fin_cons measurable_snd.fst measurable_fst.snd.snd)))
    have ha : Measurable (fun p : (X×(Measure (ℝ×S)×(Fin m → ℝ)))×(ℝ×S) =>
        stableMassKernel (p.1.2.1.map Prod.fst) {p.2.1}) :=
      stableMassAtom_measurable_comp
        ((Measure.measurable_map _ measurable_fst).comp measurable_fst.snd.fst)
        measurable_snd.fst
    have hset : MeasurableSet {p : (X×(Measure (ℝ×S)×(Fin m → ℝ)))×(ℝ×S) |
        ∃ i, p.1.2.2 i = p.2.1} :=
      cascadeMeasurableSet_exists fun i => measurableSet_eq_fun (by fun_prop) measurable_snd.fst
    simp only [List.map_cons,markedBlockProbability]
    exact (measurable_const.ite hset
      (((ha.pow_const (nf.1-1)).mul ((hm nf (by simp)).comp
        (measurable_fst.fst.prodMk measurable_snd.snd))).mul hD)).lintegral_kernel_prod_right' (κ := κ)

@[reducible] def DecoratedVisitShape (X : Type) : ℕ → Type
  | 0 => ℕ × (X → ℝ≥0∞)
  | n+1 => List (DecoratedVisitShape X n)

def DecoratedVisitShape.bare {X : Type} : (n : ℕ) → DecoratedVisitShape X n → CascadeVisitShape n
  | 0, s => s.1
  | n+1, ss => ss.map (DecoratedVisitShape.bare n)

def DecoratedVisitShape.Valid {X : Type} [MeasurableSpace X] :
    (n : ℕ) → DecoratedVisitShape X n → Prop
  | 0, s => 1 ≤ s.1 ∧ Measurable s.2
  | n+1, ss => ss ≠ [] ∧ ∀ s ∈ ss, DecoratedVisitShape.Valid n s

lemma DecoratedVisitShape.bare_valid {X : Type} [MeasurableSpace X]
    (n : ℕ) (s : DecoratedVisitShape X n) (hs : s.Valid n) :
    CascadeVisitShape.Valid n (s.bare n) := by
  induction n with
  | zero => exact hs.1
  | succ n ih =>
    exact ⟨by simpa [DecoratedVisitShape.bare] using hs.1,
      by intro t ht; obtain ⟨s',hm,rfl⟩ := List.mem_map.mp ht; exact ih s' (hs.2 s' hm)⟩

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

def decoratedCenteredRoot (ν : ProbabilityMeasure S) (step : X×S → X)
    (n : ℕ) (z : Fin (n+1) → ℝ) (F : Fin (n+1) → X×S → ℝ)
    (p : X×(S×DecoratedCascade S n)) : ℝ :=
  centeredLogMark ((ν : Measure S).prod (decoratedCascadeLaw ν n (fun i => z i.succ)))
    (z 0) (fun t => decoratedRootPotential step n F (p.1,t)) p.2

lemma decoratedCenteredRoot_measurable (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin (n+1) → ℝ)
    (F : Fin (n+1) → X×S → ℝ) (hF : ∀ i, Measurable (F i)) :
    Measurable (decoratedCenteredRoot ν step n z F) := by
  have hR := decoratedRootPotential_measurable step hs n F hF
  have hE : StronglyMeasurable (fun p : X×(S×DecoratedCascade S n) =>
      Real.exp (z 0*decoratedRootPotential step n F p)) :=
    (hR.const_mul _).exp.stronglyMeasurable
  have hM : Measurable (fun x => ∫ t : S×DecoratedCascade S n,
      Real.exp (z 0*decoratedRootPotential step n F (x,t))
      ∂((ν : Measure S).prod (decoratedCascadeLaw ν n (fun i => z i.succ)))) :=
    (StronglyMeasurable.integral_prod_right
      (f := fun x t => Real.exp (z 0*decoratedRootPotential step n F (x,t))) hE).measurable
  exact hR.sub ((hM.comp measurable_fst).log.div_const _)

def decoratedShapeProbability (ν : ProbabilityMeasure S) (step : X×S → X) :
    (n : ℕ) → (Fin n → ℝ) → (Fin n → X×S → ℝ) →
      DecoratedVisitShape X n → X×DecoratedCascade S n → ℝ≥0∞
  | 0, _, _, s, p => s.2 p.1
  | n+1, z, F, ss, p => markedBlockProbability
      (ss.map (fun s => (cascadeVisitCount n (s.bare n),fun t : S×DecoratedCascade S n =>
        decoratedShapeProbability ν step n (fun i => z i.succ) (fun i => F i.succ) s
          (step (p.1,t.1),t.2))))
      ((markedStableCountKernel p.2).map (fun t : ℝ×(S×DecoratedCascade S n) =>
        (t.1+decoratedCenteredRoot ν step n z F (p.1,t.2),t.2))) (Fin.elim0 : Fin 0 → ℝ)

lemma decoratedShapeProbability_measurable (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (s : DecoratedVisitShape X n) (hs' : s.Valid n) :
    Measurable (decoratedShapeProbability ν step n z F s) := by
  induction n with
  | zero => exact hs'.2.comp measurable_fst
  | succ n ih =>
    let ns : List (ℕ×(X×(S×DecoratedCascade S n) → ℝ≥0∞)) :=
      s.map (fun t => (cascadeVisitCount n (t.bare n),fun p =>
        decoratedShapeProbability ν step n (fun i => z i.succ) (fun i => F i.succ) t
          (step (p.1,p.2.1),p.2.2)))
    have hm : ∀ nf ∈ ns, Measurable nf.2 := by
      intro nf hnf; obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hnf
      exact (ih (fun i => z i.succ) (fun i => F i.succ) (fun i => hF i.succ) t
        (hs'.2 t ht)).comp
        ((hs.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd)
    have hmap := countKernel_parameter_map_measurable
      (fun p : X×(ℝ×(S×DecoratedCascade S n)) =>
        (p.2.1+decoratedCenteredRoot ν step n z F (p.1,p.2.2),p.2.2))
      ((measurable_snd.fst.add ((decoratedCenteredRoot_measurable ν step hs n z F hF).comp
        (measurable_fst.prodMk measurable_snd.snd))).prodMk measurable_snd.snd)
    have hh := (markedBlockProbability_parameter_measurable ns hm 0).comp
      (measurable_fst.prodMk (hmap.prodMk (measurable_const (a := (Fin.elim0 : Fin 0 → ℝ)))))
    convert hh using 1
    funext p
    simp only [decoratedShapeProbability,ns,List.map_map,Function.comp_def]

def decoratedShapeMarkValue (ν : ProbabilityMeasure S) (step : X×S → X) :
    (n : ℕ) → (Fin n → ℝ) → (Fin n → X×S → ℝ) →
      DecoratedVisitShape X n → X → ℝ≥0∞
  | 0, _, _, s, x => s.2 x
  | n+1, z, F, ss, x => (ss.map (fun s => ∫⁻ t,
      ENNReal.ofReal (Real.exp (z 0*F 0 (x,t)))*
        decoratedShapeMarkValue ν step n (fun i => z i.succ) (fun i => F i.succ)
          s (step (x,t)) ∂ν)).prod

omit [Nonempty S] in
lemma decoratedShapeMarkValue_measurable (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (s : DecoratedVisitShape X n) (hs' : s.Valid n) :
    Measurable (decoratedShapeMarkValue ν step n z F s) := by
  induction n with
  | zero => exact hs'.2
  | succ n ih =>
    have hterm (t : DecoratedVisitShape X n) (ht : t ∈ s) :
        Measurable (fun x => ∫⁻ u, ENNReal.ofReal (Real.exp (z 0*F 0 (x,u)))*
          decoratedShapeMarkValue ν step n (fun i => z i.succ) (fun i => F i.succ)
            t (step (x,u)) ∂ν) := by
      have h : Measurable (fun p : X×S => ENNReal.ofReal (Real.exp (z 0*F 0 p))*
          decoratedShapeMarkValue ν step n (fun i => z i.succ) (fun i => F i.succ)
            t (step p)) :=
        ((hF 0).const_mul _).exp.ennreal_ofReal.mul
          ((ih _ _ (fun i => hF i.succ) t (hs'.2 t ht)).comp hs)
      exact h.lintegral_prod_right
    change Measurable (fun x => (s.map (fun t => ∫⁻ u,
      ENNReal.ofReal (Real.exp (z 0*F 0 (x,u)))*
        decoratedShapeMarkValue ν step n (fun i => z i.succ) (fun i => F i.succ)
          t (step (x,u)) ∂ν)).prod)
    clear hs' ih
    induction s with
    | nil => exact measurable_const
    | cons t ts iht =>
      simp only [List.map_cons,List.prod_cons]
      exact (hterm t (by simp)).mul (iht (fun u hu => hterm u (by simp [hu])))

end SphericalPerceptronFreeEnergy

end

end OAI

import Mathlib
import OAI.Probability.Perceptron.Variational.ProductMarkLaw
import OAI.Probability.Perceptron.Variational.MarkedBlockParameter
import OAI.Probability.Perceptron.Variational.MarkTiltKernel

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

section

lemma exponentialMarkTilt_eq_density_of_one {S : Type*} [MeasurableSpace S]
    (ν : Measure S) {b : ℝ} {F : S → ℝ}
    (hI : Integrable (fun s => Real.exp (b*F s)) ν)
    (hM : (∫ s, Real.exp (b*F s) ∂ν) = 1) :
    exponentialMarkTilt ν b F = ν.withDensity (fun s => ENNReal.ofReal (Real.exp (b*F s))) := by
  unfold exponentialMarkTilt normalizedMeasure
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun s => (Real.exp_pos _).le),hM]
  simp

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

theorem decoratedShapeProbability_integral (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1)
    (a : ℝ) (ha : ∀ i, a < z i) (s : DecoratedVisitShape X n)
    (hv : s.Valid n) (x : X) :
    (∫⁻ η, decoratedShapeProbability ν step n z F s (x,η)
      ∂decoratedBiasedLaw ν step n z F x a) =
      cascadeShapeLikelihood n z a (s.bare n)*decoratedShapeMarkValue ν step n z F s x := by
  induction n generalizing a x with
  | zero =>
    have := decoratedBiasedLaw_probability ν step hs 0 z hz hz0 hz1 F hF hI hM x a ha
    simp only [decoratedShapeProbability,cascadeShapeLikelihood,decoratedShapeMarkValue,
      lintegral_const,measure_univ,mul_one,one_mul]
  | succ n ih =>
    have htail : StrictMono (fun i : Fin n => z i.succ) :=
      fun i j h => hz (Fin.succ_lt_succ_iff.mpr h)
    have hrange : ∀ i : Fin n, z 0 < z i.succ := fun i => hz (by simp)
    let ns : List (ℕ×(S×DecoratedCascade S n → ℝ≥0∞)) := s.map (fun t =>
      (cascadeVisitCount n (t.bare n),fun p =>
        decoratedShapeProbability ν step n (fun i => z i.succ) (fun i => F i.succ) t
          (step (x,p.1),p.2)))
    have hne : ns ≠ [] := by simpa [ns] using hv.1
    have hn : ∀ nf ∈ ns, 1 ≤ nf.1 := by
      intro nf hnf; obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hnf
      exact cascadeVisitCount_pos n _ (t.bare_valid n (hv.2 t ht))
    have hm : ∀ nf ∈ ns, Measurable nf.2 := by
      intro nf hnf; obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hnf
      exact (decoratedShapeProbability_measurable ν step hs n (fun i => z i.succ)
        (fun i => F i.succ) (fun i => hF i.succ) t (hv.2 t ht)).comp
        ((hs.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
    have he := decoratedRootBlock_factor ν step hs n z hz hz0 hz1 F hF hI hM x a
      (ha 0) ns hne hn hm
    change (∫⁻ η, markedBlockProbability ns
      ((markedStableCountKernel η).map (logMarkShift
        (centeredLogMark ((ν : Measure S).prod
          (decoratedCascadeLaw ν n (fun i => z i.succ))) (z 0)
          (fun p => decoratedRootPotential step n F (x,p)))))
      (Fin.elim0 : Fin 0 → ℝ) ∂decoratedBiasedLaw ν step (n+1) z F x a) = _
    rw [he,stableBlockProbability_eppf_value (hz0 0) (hz1 0) (ha 0)
      (ns.map Prod.fst) (by simpa using hne)
      (by intro k hk; obtain ⟨nf,hmem,rfl⟩ := List.mem_map.mp hk; exact hn nf hmem)]
    have hchild (t : DecoratedVisitShape X n) (ht : t ∈ s) :
        (∫⁻ u, (∫⁻ C, decoratedShapeProbability ν step n (fun i => z i.succ)
          (fun i => F i.succ) t (step (x,u),C) ∂decoratedBiasedLaw ν step n
          (fun i => z i.succ) (fun i => F i.succ) (step (x,u)) (z 0))
            ∂exponentialMarkTilt ν (z 0) (fun u => F 0 (x,u))) =
        cascadeShapeLikelihood n (fun i => z i.succ) (z 0) (t.bare n)*
          ∫⁻ u, ENNReal.ofReal (Real.exp (z 0*F 0 (x,u)))*
            decoratedShapeMarkValue ν step n (fun i => z i.succ) (fun i => F i.succ)
              t (step (x,u)) ∂ν := by
      have hval : Measurable (fun u => decoratedShapeMarkValue ν step n
          (fun i => z i.succ) (fun i => F i.succ) t (step (x,u))) :=
        (decoratedShapeMarkValue_measurable ν step hs n (fun i => z i.succ)
          (fun i => F i.succ) (fun i => hF i.succ) t (hv.2 t ht)).comp
          (hs.comp (measurable_const.prodMk measurable_id))
      calc
        _ = ∫⁻ u, cascadeShapeLikelihood n (fun i => z i.succ) (z 0) (t.bare n)*
            decoratedShapeMarkValue ν step n (fun i => z i.succ) (fun i => F i.succ)
              t (step (x,u)) ∂exponentialMarkTilt ν (z 0) (fun u => F 0 (x,u)) := by
          apply lintegral_congr
          intro u
          exact ih (fun i => z i.succ) htail (fun i => hz0 i.succ) (fun i => hz1 i.succ)
            (fun i => F i.succ) (fun i => hF i.succ) (fun i => hI i.succ)
            (fun i => hM i.succ) (z 0) hrange t (hv.2 t ht) (step (x,u))
        _ = _ := by
          have hweight : Measurable (fun u : S => ENNReal.ofReal (Real.exp (z 0*F 0 (x,u)))) :=
            (((hF 0).comp (measurable_const.prodMk measurable_id)).const_mul _).exp.ennreal_ofReal
          rw [lintegral_const_mul _ hval,
            exponentialMarkTilt_eq_density_of_one (ν : Measure S) (b := z 0)
              (F := fun u => F 0 (x,u)) (hI 0 x) (hM 0 x),
            lintegral_withDensity_eq_lintegral_mul _ hweight hval]
          rfl
    simp only [ns,List.map_map,Function.comp_def] at *
    rw [show (s.map (fun t => ∫⁻ u, (∫⁻ C, decoratedShapeProbability ν step n
      (fun i => z i.succ) (fun i => F i.succ) t (step (x,u),C)
        ∂decoratedBiasedLaw ν step n (fun i => z i.succ) (fun i => F i.succ)
          (step (x,u)) (z 0)) ∂exponentialMarkTilt ν (z 0) (fun u => F 0 (x,u)))) =
      s.map (fun t => cascadeShapeLikelihood n (fun i => z i.succ) (z 0) (t.bare n)*
        ∫⁻ u, ENNReal.ofReal (Real.exp (z 0*F 0 (x,u)))*
          decoratedShapeMarkValue ν step n (fun i => z i.succ) (fun i => F i.succ)
            t (step (x,u)) ∂ν) by exact List.map_congr_left hchild]
    rw [List.prod_map_mul]
    simp only [cascadeShapeLikelihood,DecoratedVisitShape.bare,decoratedShapeMarkValue,
      List.map_map,Function.comp_def]
    ac_rfl

end

@[reducible] def PairedVisitShape (X Y : Type) : ℕ → Type
  | 0 => ℕ × ((X → ℝ≥0∞) × (Y → ℝ≥0∞))
  | n+1 => List (PairedVisitShape X Y n)

def PairedVisitShape.first {X Y : Type} : (n : ℕ) → PairedVisitShape X Y n → DecoratedVisitShape X n
  | 0, s => (s.1,s.2.1)
  | n+1, s => s.map (PairedVisitShape.first n)

def PairedVisitShape.second {X Y : Type} : (n : ℕ) → PairedVisitShape X Y n → DecoratedVisitShape Y n
  | 0, s => (s.1,s.2.2)
  | n+1, s => s.map (PairedVisitShape.second n)

def PairedVisitShape.product {X Y : Type} : (n : ℕ) → PairedVisitShape X Y n → DecoratedVisitShape (X×Y) n
  | 0, s => (s.1,fun p => s.2.1 p.1*s.2.2 p.2)
  | n+1, s => s.map (PairedVisitShape.product n)

lemma PairedVisitShape.bare_first_second {X Y : Type} (n : ℕ) (s : PairedVisitShape X Y n) :
    (s.first n).bare n = (s.second n).bare n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [first,second,DecoratedVisitShape.bare,List.map_map,Function.comp_def]
    exact List.map_congr_left (fun t _ => ih t)

lemma PairedVisitShape.product_valid {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (n : ℕ) (s : PairedVisitShape X Y n)
    (h₁ : (s.first n).Valid n) (h₂ : (s.second n).Valid n) :
    (s.product n).Valid n := by
  induction n with
  | zero => exact ⟨h₁.1,(h₁.2.comp measurable_fst).mul (h₂.2.comp measurable_snd)⟩
  | succ n ih =>
    refine ⟨by simpa [product,first] using h₁.1,?_⟩
    intro t ht
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
    exact ih u (h₁.2 _ (List.mem_map.mpr ⟨u,hu,rfl⟩))
      (h₂.2 _ (List.mem_map.mpr ⟨u,hu,rfl⟩))

theorem decoratedShapeMarkValue_product {X Y S T : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace S] [MeasurableSpace T]
    [Nonempty S] [Nonempty T]
    (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S → X) (step₂ : Y×T → Y)
    (hs₁ : Measurable step₁) (hs₂ : Measurable step₂)
    (n : ℕ) (z : Fin n → ℝ)
    (F : Fin n → X×S → ℝ) (G : Fin n → Y×T → ℝ)
    (hF : ∀ i, Measurable (F i)) (hG : ∀ i, Measurable (G i))
    (s : PairedVisitShape X Y n) (h₁ : (s.first n).Valid n) (h₂ : (s.second n).Valid n)
    (x : X) (y : Y) :
    decoratedShapeMarkValue (productMarkLaw ν ρ)
      (fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))) n z
      (fun i p => F i (p.1.1,p.2.1)+G i (p.1.2,p.2.2)) (s.product n) (x,y) =
    decoratedShapeMarkValue ν step₁ n z F (s.first n) x *
      decoratedShapeMarkValue ρ step₂ n z G (s.second n) y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
    simp only [PairedVisitShape.product,PairedVisitShape.first,PairedVisitShape.second,
      decoratedShapeMarkValue,List.map_map,Function.comp_def]
    rw [← List.prod_map_mul]
    apply congrArg List.prod
    apply List.map_congr_left
    intro t ht
    have ht₁ := h₁.2 _ (List.mem_map.mpr ⟨t,ht,rfl⟩)
    have ht₂ := h₂.2 _ (List.mem_map.mpr ⟨t,ht,rfl⟩)
    simp_rw [ih (fun i => z i.succ) (fun i => F i.succ) (fun i => G i.succ)
      (fun i => hF i.succ) (fun i => hG i.succ) t ht₁ ht₂]
    have hm₁ : Measurable (fun u => ENNReal.ofReal (Real.exp (z 0*F 0 (x,u)))*
        decoratedShapeMarkValue ν step₁ n (fun i => z i.succ) (fun i => F i.succ)
          (t.first n) (step₁ (x,u))) :=
      ((((hF 0).comp (measurable_const.prodMk measurable_id)).const_mul _).exp.ennreal_ofReal).mul
        ((decoratedShapeMarkValue_measurable ν step₁ hs₁ n (fun i => z i.succ)
          (fun i => F i.succ) (fun i => hF i.succ) _ ht₁).comp
            (hs₁.comp (measurable_const.prodMk measurable_id)))
    have hm₂ : Measurable (fun u => ENNReal.ofReal (Real.exp (z 0*G 0 (y,u)))*
        decoratedShapeMarkValue ρ step₂ n (fun i => z i.succ) (fun i => G i.succ)
          (t.second n) (step₂ (y,u))) :=
      ((((hG 0).comp (measurable_const.prodMk measurable_id)).const_mul _).exp.ennreal_ofReal).mul
        ((decoratedShapeMarkValue_measurable ρ step₂ hs₂ n (fun i => z i.succ)
          (fun i => G i.succ) (fun i => hG i.succ) _ ht₂).comp
            (hs₂.comp (measurable_const.prodMk measurable_id)))
    simp only [mul_add,Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le]
    convert lintegral_prod_mul (μ := (ν : Measure S)) (ν := (ρ : Measure T))
      hm₁.aemeasurable hm₂.aemeasurable using 1
    apply lintegral_congr
    intro p
    exact mul_mul_mul_comm _ _ _ _

end SphericalPerceptronFreeEnergy

end

end OAI

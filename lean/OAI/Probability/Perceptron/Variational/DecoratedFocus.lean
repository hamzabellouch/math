import Mathlib
import OAI.Probability.Perceptron.Variational.Shape

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical ENNReal NNReal BigOperators Topology
namespace SphericalPerceptronFreeEnergy
variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

def decoratedFocusedProbability (ν : ProbabilityMeasure S) (step : X×S → X) :
    (n : ℕ) → (Fin n → ℝ) → (Fin n → X×S → ℝ) → ℕ →
      CascadeVisitShape n → X×DecoratedCascade S n → ℝ≥0∞
  | n, z, F, 0, s, p => decoratedShapeProbability ν step n z F (trivialDecoratedShape X n s) p
  | 0, _, _, _+1, _, _ => 0
  | _+1, _, _, _+1, [], _ => 0
  | n+1, z, F, d+1, s::ss, p => markedBlockProbability
      ((cascadeVisitCount n s+1, fun t : S×DecoratedCascade S n =>
        decoratedFocusedProbability ν step n (fun i => z i.succ) (fun i => F i.succ) d s
          (step (p.1,t.1),t.2)) ::
      ss.map (fun t => (cascadeVisitCount n t,fun u : S×DecoratedCascade S n =>
        decoratedShapeProbability ν step n (fun i => z i.succ) (fun i => F i.succ)
          (trivialDecoratedShape X n t) (step (p.1,u.1),u.2))))
      ((markedStableCountKernel p.2).map (fun t : ℝ×(S×DecoratedCascade S n) =>
        (t.1+decoratedCenteredRoot ν step n z F (p.1,t.2),t.2))) (Fin.elim0 : Fin 0 → ℝ)

lemma decoratedFocusedProbability_measurable (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (d : ℕ) (s : CascadeVisitShape n) (hv : s.Valid n) :
    Measurable (decoratedFocusedProbability ν step n z F d s) := by
  induction n generalizing d with
  | zero =>
    cases d
    · exact decoratedShapeProbability_measurable ν step hs 0 z F hF _
        (trivialDecoratedShape_valid X 0 s hv)
    · exact measurable_const
  | succ n ih =>
    cases d with
    | zero =>
      exact decoratedShapeProbability_measurable ν step hs (n+1) z F hF _
        (trivialDecoratedShape_valid X (n+1) s hv)
    | succ d =>
      cases s with
      | nil => exact measurable_const
      | cons s ss =>
        let ns : List (ℕ×(X×(S×DecoratedCascade S n) → ℝ≥0∞)) :=
          (cascadeVisitCount n s+1,fun p =>
            decoratedFocusedProbability ν step n (fun i => z i.succ) (fun i => F i.succ) d s
              (step (p.1,p.2.1),p.2.2)) ::
          ss.map (fun t => (cascadeVisitCount n t, fun p =>
            decoratedShapeProbability ν step n (fun i => z i.succ) (fun i => F i.succ)
              (trivialDecoratedShape X n t) (step (p.1,p.2.1),p.2.2)))
        have hm : ∀ nf ∈ ns, Measurable nf.2 := by
          intro nf hnf
          rcases List.mem_cons.mp hnf with rfl | ht
          · exact (ih _ _ (fun i => hF i.succ) d s (hv.2 s (by simp))).comp
              ((hs.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd)
          · obtain ⟨t,hmem,rfl⟩ := List.mem_map.mp ht
            exact (decoratedShapeProbability_measurable ν step hs n _ _ (fun i => hF i.succ) _
              (trivialDecoratedShape_valid X n t (hv.2 t (by simp [hmem])))).comp
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
        simp only [decoratedFocusedProbability,ns,List.map_cons,List.map_map,Function.comp_def]

lemma trivialDecoratedShape_integral (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1)
    (a : ℝ) (ha : ∀ i, a < z i) (s : CascadeVisitShape n) (hv : s.Valid n) (x : X) :
    (∫⁻ η, decoratedShapeProbability ν step n z F (trivialDecoratedShape X n s) (x,η)
      ∂decoratedBiasedLaw ν step n z F x a) = cascadeShapeLikelihood n z a s := by
  rw [decoratedShapeProbability_integral ν step hs n z hz hz0 hz1 F hF hI hM a ha _
    (trivialDecoratedShape_valid X n s hv) x,
    trivialDecoratedShape_bare,trivialDecoratedShape_markValue ν step n z F hI hM s x,mul_one]

omit [Nonempty S] in
lemma exponentialMarkTilt_probability_of_one (ν : ProbabilityMeasure S) {b : ℝ} {G : S → ℝ}
    (hI : Integrable (fun s => Real.exp (b*G s)) ν)
    (hM : (∫ s, Real.exp (b*G s) ∂ν) = 1) :
    IsProbabilityMeasure (exponentialMarkTilt ν b G) := by
  rw [exponentialMarkTilt_eq_density_of_one (ν : Measure S) (b := b) (F := G) hI hM]
  exact normalized_mark_density_probability (ν : Measure S) (b := b) (F := G) hI hM

lemma decoratedFocusedProbability_integral_succ_eq (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin (n+1) → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin (n+1) → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1)
    (a : ℝ) (ha : ∀ i, a < z i) (d : ℕ)
    (s : CascadeVisitShape n) (ss : List (CascadeVisitShape n))
    (hv : CascadeVisitShape.Valid (n+1) (s::ss)) (x : X)
    (hchild : ∀ y, (∫⁻ η, decoratedFocusedProbability ν step n (fun i => z i.succ)
      (fun i => F i.succ) d s (y,η) ∂decoratedBiasedLaw ν step n (fun i => z i.succ)
        (fun i => F i.succ) y (z 0)) = ∫⁻ η, focusedShapeProbability n (fun i => z i.succ)
          d s η ∂cascadeBiasedLaw n (fun i => z i.succ) (z 0)) :
    (∫⁻ η, decoratedFocusedProbability ν step (n+1) z F (d+1) (s::ss) (x,η)
      ∂decoratedBiasedLaw ν step (n+1) z F x a) =
      ∫⁻ η, focusedShapeProbability (n+1) z (d+1) (s::ss) η
        ∂cascadeBiasedLaw (n+1) z a := by
  have htail : StrictMono (fun i : Fin n => z i.succ) :=
    fun i j hij => hz (Fin.succ_lt_succ_iff.mpr hij)
  have har : ∀ i : Fin n, z 0 < z i.succ := fun i => hz (by simp)
  let ns : List (ℕ×(S×DecoratedCascade S n → ℝ≥0∞)) :=
    (cascadeVisitCount n s+1,fun t => decoratedFocusedProbability ν step n
      (fun i => z i.succ) (fun i => F i.succ) d s (step (x,t.1),t.2)) ::
    ss.map (fun t => (cascadeVisitCount n t,fun u => decoratedShapeProbability ν step n
      (fun i => z i.succ) (fun i => F i.succ) (trivialDecoratedShape X n t)
        (step (x,u.1),u.2)))
  let ps : List (ℕ×(StableCascade n → ℝ≥0∞)) :=
    (cascadeVisitCount n s+1,focusedShapeProbability n (fun i => z i.succ) d s)::
      ss.map (fun t => (cascadeVisitCount n t,cascadeShapeProbability n (fun i => z i.succ) t))
  have hn : ∀ nf ∈ ns, 1 ≤ nf.1 := by
    intro nf hnf
    rcases List.mem_cons.mp hnf with rfl | ht
    · simp
    · obtain ⟨t,hmem,rfl⟩ := List.mem_map.mp ht
      exact cascadeVisitCount_pos n t (hv.2 t (by simp [hmem]))
  have hpn : ∀ nf ∈ ps, 1 ≤ nf.1 := by
    intro nf hnf
    rcases List.mem_cons.mp hnf with rfl | ht
    · simp
    · obtain ⟨t,hmem,rfl⟩ := List.mem_map.mp ht
      exact cascadeVisitCount_pos n t (hv.2 t (by simp [hmem]))
  have hm : ∀ nf ∈ ns, Measurable nf.2 := by
    intro nf hnf
    rcases List.mem_cons.mp hnf with rfl | ht
    · exact (decoratedFocusedProbability_measurable ν step hs n _ _
        (fun i => hF i.succ) d s (hv.2 s (by simp))).comp
          ((hs.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
    · obtain ⟨t,hmem,rfl⟩ := List.mem_map.mp ht
      exact (decoratedShapeProbability_measurable ν step hs n _ _ (fun i => hF i.succ) _
        (trivialDecoratedShape_valid X n t (hv.2 t (by simp [hmem])))).comp
          ((hs.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
  have hpm : ∀ nf ∈ ps, Measurable nf.2 := by
    intro nf hnf
    rcases List.mem_cons.mp hnf with rfl | ht
    · exact focusedShapeProbability_measurable n _ d s
    · obtain ⟨t,hmem,rfl⟩ := List.mem_map.mp ht
      exact cascadeShapeProbability_measurable n _ t
  change (∫⁻ η, markedBlockProbability ns
    ((markedStableCountKernel η).map (logMarkShift
      (centeredLogMark ((ν : Measure S).prod
        (decoratedCascadeLaw ν n (fun i => z i.succ))) (z 0)
        (fun p => decoratedRootPotential step n F (x,p)))))
    (Fin.elim0 : Fin 0 → ℝ) ∂decoratedBiasedLaw ν step (n+1) z F x a) =
    ∫⁻ η, markedBlockProbability ps _ (Fin.elim0 : Fin 0 → ℝ) ∂cascadeBiasedLaw (n+1) z a
  rw [decoratedRootBlock_factor ν step hs n z hz hz0 hz1 F hF hI hM x a (ha 0)
    ns (by simp [ns]) hn hm,
    cascadeRootBlock_factor z hz hz0 hz1 (ha 0) ps (by simp [ps]) hpn hpm]
  let := exponentialMarkTilt_probability_of_one ν (hI 0 x) (hM 0 x)
  have he : ns.map Prod.fst = ps.map Prod.fst := by
    simp only [ns,ps,List.map_cons,List.map_map,Function.comp_def]
  rw [he]
  apply congrArg (fun q : ℝ≥0∞ => q * _)
  simp only [ns,ps,List.map_cons,List.prod_cons]
  apply congrArg₂ (· * ·)
  · have hh : ∀ u, (∫⁻ C, decoratedFocusedProbability ν step n (fun i => z i.succ)
        (fun i => F i.succ) d s (step (x,u),C) ∂decoratedBiasedLaw ν step n
          (fun i => z i.succ) (fun i => F i.succ) (step (x,u)) (z 0)) =
        ∫⁻ C, focusedShapeProbability n (fun i => z i.succ) d s C
          ∂cascadeBiasedLaw n (fun i => z i.succ) (z 0) := by
      intro u
      exact hchild (step (x,u))
    simp_rw [hh]
    simp
  · congr 1
    simp only [List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro t ht
    simp_rw [trivialDecoratedShape_integral ν step hs n _ htail
      (fun i => hz0 i.succ) (fun i => hz1 i.succ) _ (fun i => hF i.succ)
      (fun i => hI i.succ) (fun i => hM i.succ) (z 0) har t (hv.2 t (by simp [ht])),
      cascadeShapeProbability_integral n _ htail (fun i => hz0 i.succ)
        (fun i => hz1 i.succ) (z 0) har t (hv.2 t (by simp [ht]))]
    simp

lemma decoratedFocusedProbability_integral_eq (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1)
    (a : ℝ) (ha : ∀ i, a < z i) (d : ℕ) (hd : d ≤ n)
    (s : CascadeVisitShape n) (hv : s.Valid n) (x : X) :
    (∫⁻ η, decoratedFocusedProbability ν step n z F d s (x,η)
      ∂decoratedBiasedLaw ν step n z F x a) =
      ∫⁻ η, focusedShapeProbability n z d s η ∂cascadeBiasedLaw n z a := by
  induction d generalizing n a x with
  | zero =>
    simp only [decoratedFocusedProbability,focusedShapeProbability]
    rw [trivialDecoratedShape_integral ν step hs n z hz hz0 hz1 F hF hI hM a ha s hv x,
      cascadeShapeProbability_integral n z hz hz0 hz1 a ha s hv]
  | succ d ih =>
    cases n with
    | zero => omega
    | succ n =>
      cases s with
      | nil => exact (hv.1 rfl).elim
      | cons s ss =>
        apply decoratedFocusedProbability_integral_succ_eq ν step hs n z hz hz0 hz1 F hF hI hM
          a ha d s ss hv x
        intro y
        exact ih n _ (fun i j hij => hz (Fin.succ_lt_succ_iff.mpr hij))
          (fun i => hz0 i.succ) (fun i => hz1 i.succ) _
          (fun i => hF i.succ) (fun i => hI i.succ) (fun i => hM i.succ)
          (z 0) (fun i => hz (by simp)) (by omega) s (hv.2 s (by simp)) y

lemma decoratedFocusedProbability_integral (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1)
    (a : ℝ) (ha1 : a < 1) (ha : ∀ i, a < z i) (d : ℕ) (hd : d ≤ n)
    (s : CascadeVisitShape n) (hv : s.Valid n) (x : X) :
    (∫⁻ η, decoratedFocusedProbability ν step n z F d s (x,η)
      ∂decoratedBiasedLaw ν step n z F x a) =
      cascadeShapeLikelihood n z a s *
        ENNReal.ofReal (focusedShapeNumerator n z a d s/((cascadeVisitCount n s:ℝ)-a)) := by
  rw [decoratedFocusedProbability_integral_eq ν step hs n z hz hz0 hz1 F hF hI hM a ha d hd s hv x,
    focusedShapeProbability_integral n z hz hz0 hz1 a ha1 ha d hd s hv]

end SphericalPerceptronFreeEnergy

end

end OAI

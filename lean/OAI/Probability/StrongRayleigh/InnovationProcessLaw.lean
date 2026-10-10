import Mathlib

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336AdditiveD139

theorem iIndepFun_of_indep_predecessors
    {Ω : Type u_1} {ι : Type u_2} {E : Type u_3} [MeasurableSpace Ω] [LinearOrder ι] [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P] {f : ι → Ω → E}
    (hindep : ∀ i, IndepFun (f i) (fun ω (j : Set.Iio i) => f j ω) P) :
    iIndepFun f P := by
  classical
  rw [iIndepFun_iff]
  intro s
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
      intro A hA
      have has : a ∉ s := fun ha => (lt_irrefl a) (hlt a ha)
      have hpast : MeasurableSet[
          MeasurableSpace.comap (fun ω (j : Set.Iio a) => f j ω) inferInstance]
          (⋂ j ∈ s, A j) := by
        apply MeasurableSet.biInter s.countable_toSet
        intro j hj
        obtain ⟨B, hB, hpre⟩ := hA j (Finset.mem_insert_of_mem hj)
        refine ⟨(fun z : Set.Iio a → E => z ⟨j, hlt j hj⟩) ⁻¹' B,
          hB.preimage (measurable_pi_apply _), ?_⟩
        exact hpre
      rw [Finset.set_biInter_insert, Finset.prod_insert has,
        (hindep a).meas_inter (hA a (Finset.mem_insert_self a s)) hpast,
        ih (fun j hj => hA j (Finset.mem_insert_of_mem hj))]

theorem hasIndepIncrements_of_indep_history
    {Ω : Type u_4} {T : Type u_5} {E : Type u_6} [MeasurableSpace Ω] [Preorder T]
    [MeasurableSpace E] [Sub E] [MeasurableSub₂ E]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : T → Ω → E}
    (hindep : ∀ u v, u ≤ v → IndepFun
      (fun ω => X v ω - X u ω)
      (fun ω (s : Set.Iic u) => X s ω) P) :
    HasIndepIncrements X P := by
  intro n t ht
  apply iIndepFun_of_indep_predecessors
  intro i
  have htime : t i.castSucc ≤ t i.succ := ht (Fin.castSucc_le_succ i)
  have hleft (j : Set.Iio i) : t j.1.castSucc ≤ t i.castSucc :=
    ht (by change j.1.val ≤ i.val; exact le_of_lt j.2)
  have hright (j : Set.Iio i) : t j.1.succ ≤ t i.castSucc :=
    ht (by change j.1.val + 1 ≤ i.val; exact j.2)
  let ψ : (Set.Iic (t i.castSucc) → E) → (Set.Iio i → E) :=
    fun z j => z ⟨t j.1.succ, hright j⟩ - z ⟨t j.1.castSucc, hleft j⟩
  have hψ : Measurable ψ := Measurable.of_eval fun j =>
    (measurable_pi_apply (⟨t j.1.succ, hright j⟩ : Set.Iic (t i.castSucc))).sub
      (measurable_pi_apply (⟨t j.1.castSucc, hleft j⟩ : Set.Iic (t i.castSucc)))
  exact (hindep _ _ htime).comp measurable_id hψ

theorem isPreBrownianReal_of_gaussian_increments_indep_history
    {Ω : Type u_7} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → ℝ}
    (hzero : ∀ᵐ ω ∂P, X 0 ω = 0)
    (hlaw : ∀ u v, u ≤ v → HasLaw
      (fun ω => X v ω - X u ω) (gaussianReal 0 (v - u)) P)
    (hindep : ∀ u v, u ≤ v → IndepFun
      (fun ω => X v ω - X u ω)
      (fun ω (s : Set.Iic u) => X s ω) P) :
    IsPreBrownianReal X P := by
  apply HasIndepIncrements.isPreBrownianReal_of_hasLaw
    (incr := hasIndepIncrements_of_indep_history hindep)
  intro t
  have h := hlaw 0 t (show 0 ≤ t from zero_le)
  simp only [tsub_zero] at h
  apply h.congr
  filter_upwards [hzero] with ω hω
  simp [hω]

theorem iIndepFun_coordinates_of_gaussian_indep_increments
    {Ω : Type u_8} {F : Type u_9} [MeasurableSpace Ω] [Fintype F]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → (F → ℝ)}
    (hzero : ∀ᵐ ω ∂P, X 0 ω = 0)
    (hgauss : ∀ t, HasGaussianLaw (X t) P)
    (hcoords : ∀ t, iIndepFun (fun i ω => X t ω i) P)
    (hincr : HasIndepIncrements X P) :
    iIndepFun (fun i ω t => X t ω i) P := by
  have hprocess : IsGaussianProcess X P :=
    hincr.isGaussianProcess hgauss hzero
  have hjoint : IsGaussianProcess
      (fun (p : (i : F) × ℝ≥0) ω => X p.2 ω p.1) P :=
    (hprocess.comp_right (fun p : (i : F) × ℝ≥0 => p.2)).comp_left
      (fun p => ContinuousLinearMap.proj p.1)
  have hmem (i : F) (t : ℝ≥0) : MemLp (fun ω => X t ω i) 2 P :=
    (hgauss t |>.eval i).memLp_two
  apply hjoint.iIndepFun_of_covariance_eq_zero
    (fun i t => (hgauss t |>.eval i).aemeasurable)
  intro i j hij s t
  wlog hst : s ≤ t generalizing i j s t
  · rw [covariance_comm]
    exact this j i hij.symm t s (le_of_not_ge hst)
  have hind : IndepFun (fun ω => X s ω i) (fun ω => X t ω j - X s ω j) P :=
    (hincr.indepFun_eval_sub (show 0 ≤ s from zero_le) hst hzero).comp
      (measurable_pi_apply i) (measurable_pi_apply j)
  have hsplit : (fun ω => X t ω j) =
      (fun ω => X s ω j) + (fun ω => X t ω j - X s ω j) := by
    ext ω
    simp
  rw [hsplit]
  change cov[fun ω => X s ω i,
    (fun ω => X s ω j) + ((fun ω => X t ω j) - (fun ω => X s ω j)); P] = 0
  rw [covariance_add_right (hmem i s) (hmem j s)
    ((hmem j t).sub (hmem j s)),
    ((hcoords s).indepFun hij).covariance_eq_zero (hmem i s) (hmem j s), zero_add]
  exact hind.covariance_eq_zero (hmem i s) ((hmem j t).sub (hmem j s))

theorem finite_independent_preBrownian_of_gaussian_increments
    {Ω : Type u_10} {F : Type u_11} [MeasurableSpace Ω] [Fintype F]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → (F → ℝ)}
    (hzero : ∀ᵐ ω ∂P, X 0 ω = 0)
    (hlaw : ∀ u v, u ≤ v → HasLaw
      (fun ω i => X v ω i - X u ω i)
      (Measure.pi (fun _ : F => gaussianReal 0 (v - u))) P)
    (hindep : ∀ u v, u ≤ v → IndepFun
      (fun ω => X v ω - X u ω)
      (fun ω (s : Set.Iic u) => X s ω) P) :
    (∀ i, IsPreBrownianReal (fun t ω => X t ω i) P) ∧
      iIndepFun (fun i ω t => X t ω i) P := by
  have hincr : HasIndepIncrements X P :=
    hasIndepIncrements_of_indep_history hindep
  have heval (t : ℝ≥0) : HasLaw (X t)
      (Measure.pi (fun _ : F => gaussianReal 0 t)) P := by
    have h := hlaw 0 t (show 0 ≤ t from zero_le)
    simp only [tsub_zero] at h
    apply h.congr
    filter_upwards [hzero] with ω hω
    ext i
    simp [hω]
  have hcoord (t : ℝ≥0) (i : F) : HasLaw (fun ω => X t ω i)
      (gaussianReal 0 t) P :=
    (measurePreserving_eval (fun _ : F => gaussianReal 0 t) i).hasLaw.comp (heval t)
  have hcoords (t : ℝ≥0) : iIndepFun (fun i ω => X t ω i) P :=
    (iIndepFun_iff_hasLaw_pi_pi (hcoord t)).mpr (heval t)
  constructor
  · intro i
    exact HasIndepIncrements.isPreBrownianReal_of_hasLaw
      (fun t => hcoord t i) (hincr.map (ContinuousLinearMap.proj i : (F → ℝ) →L[ℝ] ℝ))
  · exact iIndepFun_coordinates_of_gaussian_indep_increments hzero
      (fun t => (hcoords t).hasGaussianLaw (fun i => (hcoord t i).hasGaussianLaw))
      hcoords hincr

theorem independent_preBrownian_of_finite_gaussian_increments
    {Ω : Type u_12} {I : Type u_13} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : I → ℝ≥0 → Ω → ℝ}
    (hzero : ∀ i, ∀ᵐ ω ∂P, X i 0 ω = 0)
    (hlaw : ∀ (S : Finset I) u v, u ≤ v → HasLaw
      (fun ω (i : S) => X i v ω - X i u ω)
      (Measure.pi (fun _ : S => gaussianReal 0 (v - u))) P)
    (hindep : ∀ (S : Finset I) u v, u ≤ v → IndepFun
      (fun ω (i : S) => X i v ω - X i u ω)
      (fun ω (s : Set.Iic u) (i : S) => X i s ω) P) :
    (∀ i, IsPreBrownianReal (X i) P) ∧
      iIndepFun (fun i ω t => X i t ω) P := by
  classical
  have hfinite (S : Finset I) :
      (∀ i : S, IsPreBrownianReal (X i) P) ∧
        iIndepFun (fun (i : S) ω t => X i t ω) P := by
    apply finite_independent_preBrownian_of_gaussian_increments
      (X := fun t ω (i : S) => X i t ω) _ (hlaw S) (hindep S)
    filter_upwards [ae_all_iff.mpr (fun i : S => hzero i)] with ω hω
    exact funext hω
  constructor
  · intro i
    exact (hfinite {i}).1 ⟨i, Finset.mem_singleton_self i⟩
  · exact iIndepFun_iff_finset.mpr (fun S => (hfinite S).2)

theorem independent_preBrownian_of_adapted_gaussian_increments
    {Ω : Type u_14} {I : Type u_15} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (H : Filtration ℝ≥0 mΩ) {X : I → ℝ≥0 → Ω → ℝ}
    (hX : ∀ i, Adapted H (X i))
    (hzero : ∀ i, ∀ᵐ ω ∂P, X i 0 ω = 0)
    (hlaw : ∀ (S : Finset I) u v, u ≤ v → HasLaw
      (fun ω (i : S) => X i v ω - X i u ω)
      (Measure.pi (fun _ : S => gaussianReal 0 (v - u))) P)
    (hindep : ∀ (S : Finset I) u v, u ≤ v → Indep
      (MeasurableSpace.comap (fun ω (i : S) => X i v ω - X i u ω) inferInstance)
      (H u) P) :
    (∀ i, IsPreBrownianReal (X i) P) ∧
      iIndepFun (fun i ω t => X i t ω) P := by
  apply independent_preBrownian_of_finite_gaussian_increments hzero hlaw
  intro S u v huv
  have hpast : Measurable[H u]
      (fun ω (s : Set.Iic u) (i : S) => X i s ω) := by
    let : MeasurableSpace Ω := H u
    apply Measurable.of_eval
    intro s
    apply Measurable.of_eval
    intro i
    exact (hX i).measurable_le s.2
  rw [IndepFun_iff_Indep, Indep_iff]
  intro A B hA hB
  exact (Indep_iff _ _ _).mp (hindep S u v huv) A B hA (hpast.comap_le _ hB)

end Problem336AdditiveD139

end

end OAI

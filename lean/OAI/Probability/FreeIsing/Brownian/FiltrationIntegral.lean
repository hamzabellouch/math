import OAI.Probability.FreeIsing.Brownian.SimpleIntegral

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.BrownianFiltration

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

theorem increment_indep_of_past
    {s t : ℝ≥0}
    (hind : Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    {H : Ω → ℝ} (hH : StronglyMeasurable[F s] H) :
    IndepFun (fun ω => B t ω - B s ω) H P :=
  indep_of_indep_of_le_right hind hH.measurable.comap_le

theorem increment_condExp_zero
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    {s t : ℝ≥0}
    (hind : Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) :
    P[(fun ω => B t ω - B s ω) | F s] =ᵐ[P] fun _ => 0 := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hm : Measurable (fun ω => B t ω - B s ω) :=
    ((hAd t).mono (F.le t)).measurable.sub ((hAd s).mono (F.le s)).measurable
  have hce := condExp_indep_eq hm.comap_le (F.le s)
    (show StronglyMeasurable[MeasurableSpace.comap
      (fun ω => B t ω - B s ω) inferInstance] (fun ω => B t ω - B s ω) from
      (measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable) hind
  have hmean : (∫ ω, B t ω - B s ω ∂P) = 0 := by
    rw [integral_sub (hB.integrable_eval t) (hB.integrable_eval s),
      hB.integral_eval, hB.integral_eval, sub_self]
  simpa only [hmean] using hce

theorem increment_sq_condExp
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    {s t : ℝ≥0} (hst : s ≤ t)
    (hind : Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) :
    P[(fun ω => (B t ω - B s ω) ^ 2) | F s] =ᵐ[P]
      fun _ => (t : ℝ) - (s : ℝ) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hm : Measurable (fun ω => B t ω - B s ω) :=
    ((hAd t).mono (F.le t)).measurable.sub ((hAd s).mono (F.le s)).measurable
  have hd : StronglyMeasurable[MeasurableSpace.comap
      (fun ω => B t ω - B s ω) inferInstance] (fun ω => B t ω - B s ω) :=
    (measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable
  have hce := condExp_indep_eq hm.comap_le (F.le s) (hd.pow 2) hind
  have hmean : (∫ ω, (B t ω - B s ω) ^ 2 ∂P) = (t : ℝ) - (s : ℝ) := by
    have h := preBrownian_integral_sq (hB.shift s) (t - s)
    simpa [add_tsub_cancel_of_le hst, NNReal.coe_sub hst] using h
  change P[(fun ω => (B t ω - B s ω) ^ 2) | F s] =ᵐ[P]
    fun _ => ∫ ω, (B t ω - B s ω) ^ 2 ∂P at hce
  simpa only [hmean] using hce

theorem predictable_mul_memLp_two
    (hB : IsPreBrownianReal B P) {s t : ℝ≥0}
    (hind : Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    {H : Ω → ℝ} (hH : StronglyMeasurable[F s] H) (hH2 : MemLp H 2 P) :
    MemLp (fun ω => H ω * (B t ω - B s ω)) 2 P := by
  have hD2 : MemLp (fun ω => B t ω - B s ω) 2 P :=
    (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two.sub
      (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  have hi := (increment_indep_of_past hind hH).symm
  have hint := (hi.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)).integrable_mul
    hH2.integrable_sq hD2.integrable_sq
  apply (memLp_two_iff_integrable_sq (hH2.aestronglyMeasurable.mul hD2.aestronglyMeasurable)).2
  simpa only [Function.comp_def, Pi.mul_def, mul_pow, id_eq] using hint

theorem predictable_sum_isometry
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[F (t i)] (H i))
    (hH2 : ∀ i, MemLp (H i) 2 P) (s : Finset ℕ) :
    (∫ ω, (∑ i ∈ s, H i ω * (B (t (i + 1)) ω - B (t i) ω)) ^ 2 ∂P) =
      ∑ i ∈ s, ((t (i + 1) : ℝ) - (t i : ℝ)) * ∫ ω, H i ω ^ 2 ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let G : Filtration ℕ mΩ :=
    ⟨fun i => F (t i), fun _ _ hij => F.mono (ht hij), fun i => F.le (t i)⟩
  let D : ℕ → Ω → ℝ := fun i ω => B (t (i + 1)) ω - B (t i) ω
  have hD (i : ℕ) : StronglyMeasurable[G (i + 1)] (D i) :=
    (hAd (t (i + 1))).sub ((hAd (t i)).mono (F.mono (ht (Nat.le_succ i))))
  have hD2 (i : ℕ) : MemLp (D i) 2 P :=
    (hB.isGaussianProcess.hasGaussianLaw_eval (t (i + 1))).memLp_two.sub
      (hB.isGaussianProcess.hasGaussianLaw_eval (t i)).memLp_two
  exact SimpleIntegral.predictable_sum_isometry G H D
    (fun i => (t (i + 1) : ℝ) - (t i : ℝ)) hH hD hD2
    (fun i => predictable_mul_memLp_two hB
      (hind (t i) (t (i + 1)) (ht (Nat.le_succ i))) (hH i) (hH2 i))
    (fun i => increment_condExp_zero hB hAd
      (hind (t i) (t (i + 1)) (ht (Nat.le_succ i))))
    (fun i => increment_sq_condExp hB hAd (ht (Nat.le_succ i))
      (hind (t i) (t (i + 1)) (ht (Nat.le_succ i)))) s

theorem increments_indep_natural
    (hB : IsPreBrownianReal B P) (hm : ∀ t, StronglyMeasurable (B t))
    {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance)
      (Filtration.natural B hm s) P := by
  rw [Filtration.natural_eq_comap]
  exact preBrownian_increment_indep_past hB hst

end Problem367.BrownianFiltration

end

end OAI

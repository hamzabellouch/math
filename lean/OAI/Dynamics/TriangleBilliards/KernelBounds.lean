import OAI.Dynamics.TriangleBilliards.DoubleFlow

namespace OAI

universe uAlpha uBeta uE uG uGamma

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section

/-! The positive-kernel L² bound for chartwise smoothing, including
the integral inequality and Tonelli. -/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace TriangularBilliards.Analytic

private lemma sqrt_sq (a : ℝ≥0∞) : (a ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = a := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- Cauchy–Schwarz against the constant one, including infinite measures. -/
lemma lintegral_sq_le_mass {α : Type uAlpha} [MeasurableSpace α]
    (μ : Measure α) {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    (∫⁻ x, f x ∂μ) ^ (2 : ℕ) ≤ (∫⁻ x, f x ^ (2 : ℕ) ∂μ) * μ univ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    hf (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    one_mul] at h
  have hr (x : ℝ≥0∞) : x ^ (2 : ℝ) = x ^ (2 : ℕ) := ENNReal.rpow_natCast x 2
  simp only [hr] at h
  calc
    (∫⁻ x, f x ∂μ) ^ (2 : ℕ) ≤
        ((∫⁻ x, f x ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) *
          (μ univ) ^ (1 / 2 : ℝ)) ^ (2 : ℕ) := pow_le_pow_left' h 2
    _ = _ := by rw [mul_pow, sqrt_sq, sqrt_sq]

/-- Weighted Cauchy–Schwarz in a form that does not need integrability
assumptions: any infinite expressions remain in ℝ≥0∞. -/
lemma lintegral_kernel_sq {α : Type uAlpha} [MeasurableSpace α]
    (μ : Measure α) {k f : α → ℝ≥0∞} (hk : AEMeasurable k μ)
    (hf : AEMeasurable f μ) :
    (∫⁻ x, k x * f x ∂μ) ^ (2 : ℕ) ≤
      (∫⁻ x, k x ∂μ) * (∫⁻ x, k x * f x ^ (2 : ℕ) ∂μ) := by
  have h := lintegral_sq_le_mass (μ.withDensity k)
    (hf.mono_ac (withDensity_absolutelyContinuous μ k))
  rw [lintegral_withDensity_eq_lintegral_mul₀ hk hf,
    lintegral_withDensity_eq_lintegral_mul₀ hk (hf.pow_const 2),
    withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at h
  simpa only [Pi.mul_apply, mul_comm] using h

/-- Schur's L² bound. Bounds for the absolute kernel integral in each
variable control the squared L² seminorm of its positive majorant. -/
lemma kernel_schur_sq {α : Type uAlpha} {β : Type uBeta} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    {K : α → β → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {f : β → ℝ≥0∞} (hf : Measurable f) {A B : ℝ≥0∞}
    (hrow : ∀ x, ∫⁻ y, K x y ∂ν ≤ A)
    (hcol : ∀ y, ∫⁻ x, K x y ∂μ ≤ B) :
    ∫⁻ x, (∫⁻ y, K x y * f y ∂ν) ^ (2 : ℕ) ∂μ ≤
      A * B * ∫⁻ y, f y ^ (2 : ℕ) ∂ν := by
  have hKx (x : α) : Measurable (K x) := hK.comp (measurable_const.prodMk measurable_id)
  have hKy (y : β) : Measurable (fun x => K x y) :=
    hK.comp (measurable_id.prodMk measurable_const)
  have hprod : Measurable (fun p : α × β => K p.1 p.2 * f p.2 ^ (2 : ℕ)) :=
    hK.mul ((hf.comp measurable_snd).pow_const 2)
  calc
    ∫⁻ x, (∫⁻ y, K x y * f y ∂ν) ^ (2 : ℕ) ∂μ ≤
        ∫⁻ x, A * ∫⁻ y, K x y * f y ^ (2 : ℕ) ∂ν ∂μ := by
      apply lintegral_mono
      intro x
      apply (lintegral_kernel_sq ν (hKx x).aemeasurable hf.aemeasurable).trans
      exact mul_le_mul_left (hrow x) _
    _ = A * ∫⁻ y, (∫⁻ x, K x y ∂μ) * f y ^ (2 : ℕ) ∂ν := by
      rw [lintegral_const_mul A hprod.lintegral_prod_right,
        lintegral_lintegral_swap hprod.aemeasurable]
      congr 1
      apply lintegral_congr
      intro y
      exact lintegral_mul_const _ (hKy y)
    _ ≤ A * ∫⁻ y, B * f y ^ (2 : ℕ) ∂ν := by
      gcongr with y
      exact hcol y
    _ = _ := by rw [lintegral_const_mul B (hf.pow_const 2), mul_assoc]

/-- The Schur bound for a vector-valued integral with a scalar kernel
majorant. It also covers norm-preserving parallel transports between fibers. -/
lemma kernel_integral_schur_sq {α : Type uAlpha} {β : Type uBeta} {E : Type uE}
    [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    {K : α → β → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {f : β → ℝ≥0∞} (hf : Measurable f) {A B : ℝ≥0∞}
    (hrow : ∀ x, ∫⁻ y, K x y ∂ν ≤ A)
    (hcol : ∀ y, ∫⁻ x, K x y ∂μ ≤ B)
    {F : α → β → E} (hF : ∀ x y, ‖F x y‖ₑ ≤ K x y * f y) :
    ∫⁻ x, ‖∫ y, F x y ∂ν‖ₑ ^ (2 : ℕ) ∂μ ≤
      A * B * ∫⁻ y, f y ^ (2 : ℕ) ∂ν := by
  apply le_trans _ (kernel_schur_sq μ ν hK hf hrow hcol)
  apply lintegral_mono
  intro x
  apply pow_le_pow_left'
  exact (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono (hF x))

/-- Fiberwise Schur with the genuine product measure. The kernel acts
only on the spatial variable, while the additional fiber variable is kept
parallel. A measure-preserving fiber substitution can subsequently be used
for unfolded reflected terms. -/
lemma fiber_kernel_integral_schur_sq {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} {E : Type uE}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) (ν : Measure β) (σ : Measure γ)
    [SFinite μ] [SFinite ν] [SFinite σ]
    {K : α → β → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {f : β × γ → ℝ≥0∞} (hf : Measurable f) {A B : ℝ≥0∞}
    (hrow : ∀ x, ∫⁻ y, K x y ∂ν ≤ A)
    (hcol : ∀ y, ∫⁻ x, K x y ∂μ ≤ B)
    {F : (α × γ) → β → E} (hFm : StronglyMeasurable (Function.uncurry F))
    (hF : ∀ x c y, ‖F (x, c) y‖ₑ ≤ K x y * f (y, c)) :
    ∫⁻ p, ‖∫ y, F p y ∂ν‖ₑ ^ (2 : ℕ) ∂μ.prod σ ≤
      A * B * ∫⁻ p, f p ^ (2 : ℕ) ∂ν.prod σ := by
  rw [lintegral_prod_symm _ (hFm.integral_prod_right.enorm.pow_const 2).aemeasurable]
  calc
    _ ≤ ∫⁻ c, A * B * ∫⁻ y, f (y, c) ^ (2 : ℕ) ∂ν ∂σ := by
      apply lintegral_mono
      intro c
      exact kernel_integral_schur_sq μ ν hK
        (hf.comp (measurable_id.prodMk measurable_const)) hrow hcol (fun x y => hF x c y)
    _ = _ := by
      have hm : Measurable (Function.uncurry (fun c y => f (y, c) ^ (2 : ℕ))) :=
        (hf.pow_const 2).comp measurable_swap
      rw [lintegral_const_mul _ hm.lintegral_prod_right,
        ← lintegral_prod_symm _ (hf.pow_const 2).aemeasurable]

/-- In particular, genuine strongly measurable kernel integrals map L²
to L² whenever both Schur constants are finite. -/
lemma memLp_kernel_integral {α : Type uAlpha} {β : Type uBeta} {E : Type uE} {G : Type uG}
    [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    {K : α → β → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {f : β → G} (hf : StronglyMeasurable f) (hf₂ : MemLp f 2 ν)
    {A B : ℝ≥0∞} (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (hrow : ∀ x, ∫⁻ y, K x y ∂ν ≤ A)
    (hcol : ∀ y, ∫⁻ x, K x y ∂μ ≤ B)
    {F : α → β → E} (hFm : StronglyMeasurable (Function.uncurry F))
    (hF : ∀ x y, ‖F x y‖ₑ ≤ K x y * ‖f y‖ₑ) :
    MemLp (fun x => ∫ y, F x y ∂ν) 2 μ := by
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num)
    (by norm_num) hFm.integral_prod_right.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  have hfint : ∫⁻ y, ‖f y‖ₑ ^ (2 : ℕ) ∂ν < ⊤ := by
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hf₂.eLpNorm_lt_top
  exact lt_of_le_of_lt (kernel_integral_schur_sq μ ν hK hf.enorm hrow hcol hF)
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top hA.lt_top hB.lt_top) hfint)

/-- The row integrals used above genuinely exist almost everywhere;
the preceding L² estimate is not exploiting the default value of an
undefined Bochner integral. -/
lemma integrable_kernel_ae {α : Type uAlpha} {β : Type uBeta} {E : Type uE} {G : Type uG}
    [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    {K : α → β → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {f : β → G} (hf : StronglyMeasurable f) (hf₂ : MemLp f 2 ν)
    {A B : ℝ≥0∞} (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (hrow : ∀ x, ∫⁻ y, K x y ∂ν ≤ A)
    (hcol : ∀ y, ∫⁻ x, K x y ∂μ ≤ B)
    {F : α → β → E} (hFm : StronglyMeasurable (Function.uncurry F))
    (hF : ∀ x y, ‖F x y‖ₑ ≤ K x y * ‖f y‖ₑ) :
    ∀ᵐ x ∂μ, Integrable (F x) ν := by
  have hfint : ∫⁻ y, ‖f y‖ₑ ^ (2 : ℕ) ∂ν < ⊤ := by
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hf₂.eLpNorm_lt_top
  have hm : Measurable (fun x => (∫⁻ y, K x y * ‖f y‖ₑ ∂ν) ^ (2 : ℕ)) :=
    (hK.mul (hf.enorm.comp measurable_snd)).lintegral_prod_right.pow_const 2
  have hi : ∫⁻ x, (∫⁻ y, K x y * ‖f y‖ₑ ∂ν) ^ (2 : ℕ) ∂μ < ⊤ :=
    lt_of_le_of_lt (kernel_schur_sq μ ν hK hf.enorm hrow hcol)
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top hA.lt_top hB.lt_top) hfint)
  filter_upwards [ae_lt_top hm hi.ne] with x hx
  refine ⟨(hFm.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  apply lt_of_le_of_lt (lintegral_mono (hF x))
  by_contra hn
  have ht : (∫⁻ y, K x y * ‖f y‖ₑ ∂ν) = ⊤ := top_unique (not_lt.mp hn)
  simp only [ht, ENNReal.top_pow (by norm_num : (2 : ℕ) ≠ 0), lt_self_iff_false] at hx

end TriangularBilliards.Analytic

end
end
end

end OAI

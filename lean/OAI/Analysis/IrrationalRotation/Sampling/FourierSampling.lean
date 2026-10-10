import Mathlib

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace Invariant233.FourierSampling

theorem norm_tensor_sum_le {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (a : ι → ℂ) (b : κ → ℂ) (M : ι → κ → ℂ) (ε : ℝ)
    (hM : ∀ i ∈ s, ∀ j ∈ t, ‖M i j‖ ≤ ε) :
    ‖∑ i ∈ s, ∑ j ∈ t, a i * b j * M i j‖ ≤
      (∑ i ∈ s, ‖a i‖) * (∑ j ∈ t, ‖b j‖) * ε := by
  calc
    _ ≤ ∑ i ∈ s, ‖∑ j ∈ t, a i * b j * M i j‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ∑ j ∈ t, ‖a i * b j * M i j‖ :=
      Finset.sum_le_sum fun i hi => norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ∑ j ∈ t, ‖a i‖ * ‖b j‖ * ε := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (hM i hi j hj) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
      rw [← Finset.sum_mul]

noncomputable def polynomial (s : Finset ℤ) (a : ℤ → ℂ)
    (x : UnitAddCircle) : ℂ := ∑ i ∈ s, a i * fourier i x

theorem integrable_fourier_pair {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X Y : Ω → UnitAddCircle} (hX : Measurable X) (hY : Measurable Y)
    (i j : ℤ) : Integrable (fun ω => fourier i (X ω) * fourier j (Y ω)) μ := by
  apply Integrable.of_bound
    (((fourier i).continuous.measurable.comp hX).mul
      ((fourier j).continuous.measurable.comp hY)).aestronglyMeasurable 1
  filter_upwards with ω
  change ‖fourier i (X ω) * fourier j (Y ω)‖ ≤ 1
  rw [norm_mul]
  have hi : ‖fourier i (X ω)‖ ≤ 1 := by
    simpa only [fourier_norm] using (fourier i).norm_coe_le_norm (X ω)
  have hj : ‖fourier j (Y ω)‖ ≤ 1 := by
    simpa only [fourier_norm] using (fourier j).norm_coe_le_norm (Y ω)
  nlinarith [norm_nonneg (fourier i (X ω)), norm_nonneg (fourier j (Y ω))]

theorem integral_polynomial_mul {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X Y : Ω → UnitAddCircle} (hX : Measurable X) (hY : Measurable Y)
    (s t : Finset ℤ) (a b : ℤ → ℂ) :
    (∫ ω, polynomial s a (X ω) * polynomial t b (Y ω) ∂μ) =
      ∑ i ∈ s, ∑ j ∈ t, a i * b j *
        ∫ ω, fourier i (X ω) * fourier j (Y ω) ∂μ := by
  have hterm : ∀ i j, Integrable
      (fun ω => a i * b j * (fourier i (X ω) * fourier j (Y ω))) μ :=
    fun i j => (integrable_fourier_pair hX hY i j).const_mul _
  have hexpand : ∀ ω,
      polynomial s a (X ω) * polynomial t b (Y ω) =
      ∑ i ∈ s, ∑ j ∈ t, a i * b j * (fourier i (X ω) * fourier j (Y ω)) := by
    intro ω
    rw [polynomial, polynomial, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [hexpand]
  rw [integral_finsetSum s (fun i hi => integrable_finsetSum t (fun j hj => hterm i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum t (fun j hj => hterm i j)]
  simp_rw [integral_const_mul]

theorem polynomial_error_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → UnitAddCircle} (hX : Measurable X) (hY : Measurable Y)
    (s t : Finset ℤ) (hs : 0 ∈ s) (ht : 0 ∈ t) (a b : ℤ → ℂ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hchar : ∀ i ∈ s, ∀ j ∈ t, (i, j) ≠ (0, 0) →
      ‖∫ ω, fourier i (X ω) * fourier j (Y ω) ∂μ‖ ≤ ε) :
    ‖(∫ ω, polynomial s a (X ω) * polynomial t b (Y ω) ∂μ) - a 0 * b 0‖ ≤
      (∑ i ∈ s, ‖a i‖) * (∑ j ∈ t, ‖b j‖) * ε := by
  classical
  let M : ℤ → ℤ → ℂ := fun i j =>
    (∫ ω, fourier i (X ω) * fourier j (Y ω) ∂μ) - if i = 0 ∧ j = 0 then 1 else 0
  have hM : ∀ i ∈ s, ∀ j ∈ t, ‖M i j‖ ≤ ε := by
    intro i hi j hj
    by_cases h : i = 0 ∧ j = 0
    · rcases h with ⟨rfl, rfl⟩
      simpa [M] using hε
    · simpa [M, h] using hchar i hi j hj (by simpa using h)
  have hconstant : (∑ i ∈ s, ∑ j ∈ t,
      a i * b j * (if i = 0 ∧ j = 0 then (1 : ℂ) else 0)) = a 0 * b 0 := by
    rw [Finset.sum_eq_single 0]
    · simp [ht]
    · intro i hi hi0
      simp [hi0]
    · exact fun h => (h hs).elim
  rw [integral_polynomial_mul hX hY s t a b, ← hconstant]
  have heq : (∑ i ∈ s, ∑ j ∈ t, a i * b j *
      ∫ ω, fourier i (X ω) * fourier j (Y ω) ∂μ) -
      (∑ i ∈ s, ∑ j ∈ t, a i * b j * (if i = 0 ∧ j = 0 then (1 : ℂ) else 0)) =
      ∑ i ∈ s, ∑ j ∈ t, a i * b j * M i j := by
    simp only [M, mul_sub, Finset.sum_sub_distrib]
  rw [heq]
  exact norm_tensor_sum_le s t a b M ε hM

theorem polynomial_error_le_card {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → UnitAddCircle} (hX : Measurable X) (hY : Measurable Y)
    (s t : Finset ℤ) (hs : 0 ∈ s) (ht : 0 ∈ t) (a b : ℤ → ℂ)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) (hb : ∀ j ∈ t, ‖b j‖ ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hchar : ∀ i ∈ s, ∀ j ∈ t, (i, j) ≠ (0, 0) →
      ‖∫ ω, fourier i (X ω) * fourier j (Y ω) ∂μ‖ ≤ ε) :
    ‖(∫ ω, polynomial s a (X ω) * polynomial t b (Y ω) ∂μ) - a 0 * b 0‖ ≤
      (s.card : ℝ) * t.card * ε := by
  apply (polynomial_error_le hX hY s t hs ht a b hε hchar).trans
  apply mul_le_mul_of_nonneg_right _ hε
  have has : (∑ i ∈ s, ‖a i‖) ≤ (s.card : ℝ) := by
    simpa using Finset.sum_le_sum ha
  have hbs : (∑ j ∈ t, ‖b j‖) ≤ (t.card : ℝ) := by
    simpa using Finset.sum_le_sum hb
  exact mul_le_mul has hbs (Finset.sum_nonneg fun j hj => norm_nonneg _) (by positivity)

theorem integral_product_replacement {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f g p q : Ω → ℂ}
    (hfg : Integrable (fun ω => f ω * g ω) μ)
    (hpq : Integrable (fun ω => p ω * q ω) μ)
    (hfp : Integrable (fun ω => f ω - p ω) μ)
    (hgq : Integrable (fun ω => g ω - q ω) μ)
    (hg : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ 1) (hp : ∀ᵐ ω ∂μ, ‖p ω‖ ≤ 1) :
    ‖(∫ ω, f ω * g ω ∂μ) - ∫ ω, p ω * q ω ∂μ‖ ≤
      (∫ ω, ‖f ω - p ω‖ ∂μ) + ∫ ω, ‖g ω - q ω‖ ∂μ := by
  rw [← integral_sub hfg hpq, ← integral_add hfp.norm hgq.norm]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae (hfg.sub hpq).norm (hfp.norm.add hgq.norm)
  filter_upwards [hg, hp] with ω hgω hpω
  calc
    ‖f ω * g ω - p ω * q ω‖ = ‖(f ω - p ω) * g ω + p ω * (g ω - q ω)‖ := by
      congr 1
      ring
    _ ≤ ‖(f ω - p ω) * g ω‖ + ‖p ω * (g ω - q ω)‖ := norm_add_le _ _
    _ ≤ ‖f ω - p ω‖ + ‖g ω - q ω‖ := by
      rw [norm_mul, norm_mul]
      have h₁ := mul_le_mul_of_nonneg_left hgω (norm_nonneg (f ω - p ω))
      have h₂ := mul_le_mul_of_nonneg_right hpω (norm_nonneg (g ω - q ω))
      simpa only [mul_one, one_mul] using add_le_add h₁ h₂

theorem test_error_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → UnitAddCircle} (hX : Measurable X) (hY : Measurable Y)
    (s t : Finset ℤ) (hs : 0 ∈ s) (ht : 0 ∈ t) (a b : ℤ → ℂ)
    {f g : Ω → ℂ}
    (hfg : Integrable (fun ω => f ω * g ω) μ)
    (hpq : Integrable (fun ω => polynomial s a (X ω) * polynomial t b (Y ω)) μ)
    (hfp : Integrable (fun ω => f ω - polynomial s a (X ω)) μ)
    (hgq : Integrable (fun ω => g ω - polynomial t b (Y ω)) μ)
    (hg : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ 1)
    (hp : ∀ᵐ ω ∂μ, ‖polynomial s a (X ω)‖ ≤ 1)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) (hb : ∀ j ∈ t, ‖b j‖ ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hchar : ∀ i ∈ s, ∀ j ∈ t, (i, j) ≠ (0, 0) →
      ‖∫ ω, fourier i (X ω) * fourier j (Y ω) ∂μ‖ ≤ ε) :
    ‖(∫ ω, f ω * g ω ∂μ) - a 0 * b 0‖ ≤
      (∫ ω, ‖f ω - polynomial s a (X ω)‖ ∂μ) +
      (∫ ω, ‖g ω - polynomial t b (Y ω)‖ ∂μ) +
      (s.card : ℝ) * t.card * ε := by
  apply (norm_sub_le_norm_sub_add_norm_sub _ (∫ ω, polynomial s a (X ω) * polynomial t b (Y ω) ∂μ) _).trans
  exact add_le_add
    (integral_product_replacement hfg hpq hfp hgq hg hp)
    (polynomial_error_le_card hX hY s t hs ht a b ha hb hε hchar)

theorem sampled_fourier_pair (v w n n' : ℤ) (z : ℝ) :
    fourier v (((n : ℝ) * z : ℝ) : UnitAddCircle) *
      fourier w (((n' : ℝ) * z : ℝ) : UnitAddCircle) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((v * n + w * n' : ℤ) : ℂ) * (z : ℂ)) := by
  rw [fourier_coe_apply, fourier_coe_apply, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem sampled_fourier_pair_fract (v w n n' : ℤ) (z : ℝ) :
    fourier v ((Int.fract ((n : ℝ) * z) : ℝ) : UnitAddCircle) *
      fourier w ((Int.fract ((n' : ℝ) * z) : ℝ) : UnitAddCircle) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((v * n + w * n' : ℤ) : ℂ) * (z : ℂ)) := by
  simpa only [AddCircle.coe_fract] using sampled_fourier_pair v w n n' z

theorem marginal_integral_le {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} {F : Ω → X} (hF : Measurable F)
    {C : ℝ} (hC : 0 ≤ C) (hmap : μ.map F ≤ ENNReal.ofReal C • ν)
    {f : X → ℝ} (hf : Integrable f ν) (hf0 : ∀ x, 0 ≤ f x) :
    (∫ ω, f (F ω) ∂μ) ≤ C * ∫ x, f x ∂ν := by
  have hfi := hf.smul_measure (c := ENNReal.ofReal C) ENNReal.ofReal_ne_top
  rw [← integral_map hF.aemeasurable (hfi.mono_measure hmap).aestronglyMeasurable]
  calc
    _ ≤ ∫ x, f x ∂(ENNReal.ofReal C • ν) :=
      integral_mono_measure hmap (Filter.Eventually.of_forall hf0) hfi
    _ = _ := by rw [integral_smul_measure, ENNReal.toReal_ofReal hC, smul_eq_mul]

theorem marginal_l1_error_le {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} {F : Ω → X} (hF : Measurable F)
    {C : ℝ} (hC : 0 ≤ C) (hmap : μ.map F ≤ ENNReal.ofReal C • ν)
    {f p : X → ℂ} (hfp : Integrable (fun x => f x - p x) ν) :
    (∫ ω, ‖f (F ω) - p (F ω)‖ ∂μ) ≤ C * ∫ x, ‖f x - p x‖ ∂ν :=
  marginal_integral_le hF hC hmap hfp.norm (fun _ => norm_nonneg _)

end Invariant233.FourierSampling

end OAI

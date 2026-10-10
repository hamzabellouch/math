import OAI.MathematicalPhysics.Boltzmann.Branching.MarginalUniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrability

namespace OAI

/-! # Uniform integrability of products of bounded velocity averages -/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace BoltzmannNonuniqueness.Compactness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem uniformIntegrable_average_product
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [IsFiniteMeasure ν]
    {f : ℕ → X × Y → ℝ} (hf : ∀ n, Measurable (f n))
    (hui : UniformIntegrable (fun (n : ℕ) (z : X × (Y × Y)) =>
      f n (z.1,z.2.1)*f n (z.1,z.2.2)) 1 (μ.prod (ν.prod ν)))
    {k l : X × Y → ℝ} (hk : Measurable k) (hl : Measurable l)
    (C D : ℝ≥0) (hC : ∀ z, |k z| ≤ C) (hD : ∀ z, |l z| ≤ D) :
    UniformIntegrable (fun n x => (∫ v, k (x,v)*f n (x,v) ∂ν)*
      (∫ w, l (x,w)*f n (x,w) ∂ν)) 1 μ := by
  let a : X × (Y × Y) → ℝ := fun z => k (z.1,z.2.1)*l (z.1,z.2.2)
  have ha : Measurable a := by dsimp [a]; fun_prop
  have haB : ∀ z, |a z| ≤ (C*D : ℝ≥0) := by
    intro z
    dsimp [a]
    rw [abs_mul]
    exact mul_le_mul (hC _) (hD _) (abs_nonneg _) C.coe_nonneg
  have hmul := uniformIntegrable_of_bounded_multiplier hui ha (C*D) haB
  have hm (n) : Measurable (fun z : X × (Y × Y) =>
      a z*(f n (z.1,z.2.1)*f n (z.1,z.2.2))) := by fun_prop
  have hint := uniformIntegrable_integral hm hmul
  have he (n) (x) : (∫ y : Y × Y, a (x,y)*(f n (x,y.1)*f n (x,y.2)) ∂ν.prod ν) =
      (∫ v, k (x,v)*f n (x,v) ∂ν)*(∫ w, l (x,w)*f n (x,w) ∂ν) := by
    rw [← integral_prod_mul]
    congr 1
    ext y
    dsimp [a]
    ring
  simpa only [he] using hint

/-- Compact velocity support reduces the infinite velocity measure to finite fibres. -/
theorem uniformIntegrable_average_product_of_support
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {s : Set Y} [IsFiniteMeasure (ν.restrict s)]
    {f : ℕ → X × Y → ℝ} (hf : ∀ n, Measurable (f n))
    (hui : UniformIntegrable (fun (n : ℕ) (z : X × (Y × Y)) =>
      f n (z.1,z.2.1)*f n (z.1,z.2.2)) 1 (μ.prod (ν.prod ν)))
    {k l : X × Y → ℝ} (hk : Measurable k) (hl : Measurable l)
    (C D : ℝ≥0) (hC : ∀ z, |k z| ≤ C) (hD : ∀ z, |l z| ≤ D)
    (hks : ∀ x y, y ∉ s → k (x,y) = 0) (hls : ∀ x y, y ∉ s → l (x,y) = 0) :
    UniformIntegrable (fun n x => (∫ v, k (x,v)*f n (x,v) ∂ν)*
      (∫ w, l (x,w)*f n (x,w) ∂ν)) 1 μ := by
  have hp := uniformIntegrable_restrict hui (univ ×ˢ (s ×ˢ s))
  rw [← Measure.prod_restrict,Measure.restrict_univ,← Measure.prod_restrict] at hp
  have h := uniformIntegrable_average_product hf hp hk hl C D hC hD
  have he (n) (x) : (∫ v in s, k (x,v)*f n (x,v) ∂ν) = ∫ v, k (x,v)*f n (x,v) ∂ν :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [hks x y hy,zero_mul])
  have he' (n) (x) : (∫ v in s, l (x,v)*f n (x,v) ∂ν) = ∫ v, l (x,v)*f n (x,v) ∂ν :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [hls x y hy,zero_mul])
  simpa only [he,he'] using h

end BoltzmannNonuniqueness.Compactness

end

end OAI

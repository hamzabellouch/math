import OAI.MeasureTheory.Falconer.Estimates.DescriptorScaledKernel
import OAI.MeasureTheory.Falconer.Estimates.GlobalDescriptorBounds

namespace OAI

/-! # Bounds for the actual two-endpoint descriptor amplitude -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
variable {d : ℕ}

theorem descriptorAmbientProduct_global_bounds (Q : DyadicCube d)
    (ρ : Measure (Space d)) (f : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)) (x w : Space d) :
    0 ≤ descriptorAmbientProduct Q ρ f N σ J i B S x w ∧
      descriptorAmbientProduct Q ρ f N σ J i B S x w ≤ 1 := by
  constructor
  · exact Finset.prod_nonneg (fun b _ => (descriptorAmbientMask_global_bounds Q ρ f N σ J i b (S b) x w).1)
  · exact Finset.prod_le_one₀
      (fun b _ => (descriptorAmbientMask_global_bounds Q ρ f N σ J i b (S b) x w).1)
      (fun b _ => (descriptorAmbientMask_global_bounds Q ρ f N σ J i b (S b) x w).2)

theorem descriptorPairAmplitude_norm_le (Q : DyadicCube d)
    (ρ : Measure (Space d)) (f : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)) (x y w : Space d) :
    ‖descriptorPairAmplitude Q ρ f N σ J i B S x y w‖ ≤ 1 := by
  have hx := descriptorAmbientProduct_global_bounds Q ρ f N σ J i B S x w
  have hy := descriptorAmbientProduct_global_bounds Q ρ f N σ J i B S y w
  simp only [descriptorPairAmplitude,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hx.1,abs_of_nonneg hy.1]
  exact (mul_le_mul hx.2 hy.2 hy.1 (by norm_num)).trans_eq (one_mul 1)

theorem descriptorPairAmplitude_contDiff (Q : DyadicCube d)
    (ρ : Measure (Space d)) (f : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)) (x y : Space d) :
    ContDiff ℝ ∞ (descriptorPairAmplitude Q ρ f N σ J i B S x y) :=
  (Complex.ofRealCLM.contDiff.comp (descriptorAmbientProduct_contDiff Q ρ f N σ J i B S x)).mul
    (Complex.ofRealCLM.contDiff.comp (descriptorAmbientProduct_contDiff Q ρ f N σ J i B S y))

end Falconer

end OAI

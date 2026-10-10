import Mathlib
import OAI.Geometry.WeakHessian.Entropy.WeightedParallelogramIntegral
import OAI.Geometry.WeakHessian.Sobolev.LocalSobolevLipschitz

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [MeasurableSpace X] [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma lipschitz_inv_of_one_le {η : X → ℝ} {L : ℝ≥0}
    (hη : LipschitzWith L η) (h1 : ∀ x, 1 ≤ η x) :
    LipschitzWith L (fun x => (η x)⁻¹) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hx : 0 < η x := lt_of_lt_of_le zero_lt_one (h1 x)
  have hy : 0 < η y := lt_of_lt_of_le zero_lt_one (h1 y)
  have he : (η x)⁻¹ - (η y)⁻¹ = (η y - η x)/(η x*η y) := by
    field_simp
  rw [Real.dist_eq, he, abs_div, abs_of_pos (mul_pos hx hy)]
  calc
    _ ≤ |η y - η x| := div_le_self (abs_nonneg _) (one_le_mul_of_one_le_of_one_le (h1 x) (h1 y))
    _ = dist (η x) (η y) := by rw [Real.dist_eq, abs_sub_comm]
    _ ≤ _ := hη.dist_le_mul x y

def gradientParallelogramDefect (m : Measure X) (f g : X → ℝ) (x : X) : ℝ :=
  (weakGradient m (fun y => f y+g y) x)^2 +
    (weakGradient m (fun y => f y-g y) x)^2 -
    2*(weakGradient m f x)^2 - 2*(weakGradient m g x)^2

lemma gradientParallelogramDefect_integrable (hfinite : FiniteOnBoundedSets m)
    {f g : X → ℝ} (hf : Sobolev m f) (hg : Sobolev m g) :
    Integrable (gradientParallelogramDefect m f g) m :=
  (((hf.add hfinite hg).2.2.integrable_sq.add (hf.sub hfinite hg).2.2.integrable_sq).sub
    (hf.2.2.integrable_sq.const_mul 2)).sub (hg.2.2.integrable_sq.const_mul 2)

lemma integral_gradientParallelogramDefect_mul_sq (hfinite : FiniteOnBoundedSets m)
    {f g : X → ℝ} (hf : Sobolev m f) (hg : Sobolev m g)
    {η : X → ℝ} (hη : AEStronglyMeasurable η m) {A : ℝ}
    (hA : ∀ᵐ x ∂m, |η x| ≤ A) :
    (∫ x, gradientParallelogramDefect m f g x * (η x)^2 ∂m) =
    ((∫ x, (weakGradient m (fun y => f y+g y) x*η x)^2 ∂m) +
      (∫ x, (weakGradient m (fun y => f y-g y) x*η x)^2 ∂m)) -
    2*(∫ x, (weakGradient m f x*η x)^2 ∂m) - 2*(∫ x, (weakGradient m g x*η x)^2 ∂m) := by
  have hp := (memLp_mul_bounded (hf.add hfinite hg).2.2 hη hA).integrable_sq
  have hm := (memLp_mul_bounded (hf.sub hfinite hg).2.2 hη hA).integrable_sq
  have hf' := (memLp_mul_bounded hf.2.2 hη hA).integrable_sq
  have hg' := (memLp_mul_bounded hg.2.2 hη hA).integrable_sq
  calc
    _ = ∫ x, ((weakGradient m (fun y => f y+g y) x*η x)^2 +
        (weakGradient m (fun y => f y-g y) x*η x)^2) -
        2*(weakGradient m f x*η x)^2 - 2*(weakGradient m g x*η x)^2 ∂m := by
      congr 1
      funext x
      dsimp [gradientParallelogramDefect]
      ring
    _ = _ := by
      have E := integral_sub ((hp.add hm).sub (hf'.const_mul 2)) (hg'.const_mul 2)
      have E₂ := integral_sub (hp.add hm) (hf'.const_mul 2)
      have E₃ := integral_add hp hm
      dsimp only [Pi.add_apply, Pi.sub_apply] at E E₂ E₃
      rw [E, E₂, E₃, integral_const_mul, integral_const_mul]

lemma weighted_parallelogram_defect_zero (hfinite : FiniteOnBoundedSets m)
    (hpar : ∀ u v : X → ℝ, Sobolev m u → Sobolev m v →
      (∫ x, (weakGradient m (fun y => u y+v y) x)^2 ∂m) +
        (∫ x, (weakGradient m (fun y => u y-v y) x)^2 ∂m) =
      2*(∫ x, (weakGradient m u x)^2 ∂m) + 2*(∫ x, (weakGradient m v x)^2 ∂m))
    {f g : X → ℝ} (hf : Sobolev m f) (hg : Sobolev m g) {η : X → ℝ} {L : ℝ≥0}
    (hη : LipschitzWith L η) (h1 : ∀ x, 1 ≤ η x) {A : ℝ}
    (hA : 0 ≤ A) (hbound : ∀ x, |η x| ≤ A) :
    (∫ x, gradientParallelogramDefect m f g x * (η x)^2 ∂m) = 0 := by
  have hξ := lipschitz_inv_of_one_le hη h1
  have h0 (x : X) : 0 < η x := lt_of_lt_of_le zero_lt_one (h1 x)
  have H := weighted_parallelogram_of_integral hfinite hpar hf hg
    (localSobolev_of_lipschitz hfinite hη) (localSobolev_of_lipschitz hfinite hξ)
    (fun x => mul_inv_cancel₀ (h0 x).ne')
    (ae_of_all _ fun x => (h0 x).le) (ae_of_all _ fun x => inv_nonneg.mpr (h0 x).le)
    hA L.coe_nonneg L.coe_nonneg (ae_of_all _ hbound)
    (by filter_upwards [weakGradient_le_lipschitz hfinite hη, weakGradient_nonneg (m := m) η] with x hL hn
        rwa [abs_of_nonneg hn])
    (C := 1) (ae_of_all _ fun x => by
      rw [abs_of_nonneg (inv_nonneg.mpr (h0 x).le)]
      exact (inv_le_one₀ (h0 x)).mpr (h1 x))
    (by filter_upwards [weakGradient_le_lipschitz hfinite hξ,
          weakGradient_nonneg (m := m) (fun x => (η x)⁻¹)] with x hL hn
        rwa [abs_of_nonneg hn])
  rw [integral_gradientParallelogramDefect_mul_sq hfinite hf hg hη.continuous.aestronglyMeasurable
    (ae_of_all _ hbound)]
  linarith
end WeakHessian

end
end InlinedFile0

end OAI

import Mathlib
import OAI.Geometry.WeakHessian.Calculus.CompactThickenedIndicator
import OAI.Geometry.WeakHessian.Entropy.GradientParallelogramDefect

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

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
variable [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma ae_eq_zero_of_integral_positive_lipschitz_sq {H : X → ℝ}
    (hH : Integrable H m)
    (hzero : ∀ (η : X → ℝ) (L : ℝ≥0), LipschitzWith L η →
      (∀ x, 1 ≤ η x) → ∀ A : ℝ, 0 ≤ A → (∀ x, |η x| ≤ A) →
      (∫ x, H x * (η x)^2 ∂m) = 0) : H =ᵐ[m] 0 := by
  apply WeakHessianCalculus.ae_eq_zero_of_integral_lipschitz_compact hH.locallyIntegrable
  intro φ hφc ⟨L,hφL⟩
  obtain ⟨M,hM⟩ := hφc.exists_bound_of_continuous hφL.continuous
  let C := |M|+1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hφ (x : X) : |φ x| ≤ |M| := by
    have hx : |φ x| ≤ M := by simpa only [Real.norm_eq_abs] using hM x
    exact hx.trans (le_abs_self M)
  have hp : LipschitzWith L (fun x => C+φ x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_add_left] using hφL.dist_le_mul x y
  have hm : LipschitzWith L (fun x => C-φ x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_sub_left] using hφL.dist_le_mul x y
  have hp1 (x : X) : 1 ≤ C+φ x := by
    dsimp only [C]
    linarith [(abs_le.mp (hφ x)).1]
  have hm1 (x : X) : 1 ≤ C-φ x := by
    dsimp only [C]
    linarith [(abs_le.mp (hφ x)).2]
  have hpb (x : X) : |C+φ x| ≤ C+|M| := by
    rw [abs_of_nonneg (by linarith [hp1 x])]
    linarith [(abs_le.mp (hφ x)).2]
  have hmb (x : X) : |C-φ x| ≤ C+|M| := by
    rw [abs_of_nonneg (by linarith [hm1 x])]
    linarith [(abs_le.mp (hφ x)).1]
  have Ap : 0 ≤ C+|M| := by positivity
  have hzp := hzero _ L hp hp1 _ Ap hpb
  have hzm := hzero _ L hm hm1 _ Ap hmb
  have hip : Integrable (fun x => H x*(C+φ x)^2) m :=
    hH.mul_bdd (hp.continuous.pow 2).aestronglyMeasurable (c := (C+|M|)^2)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) Ap).mpr (hpb x))
  have him : Integrable (fun x => H x*(C-φ x)^2) m :=
    hH.mul_bdd (hm.continuous.pow 2).aestronglyMeasurable (c := (C+|M|)^2)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) Ap).mpr (hmb x))
  have he : (∫ x, H x*(C+φ x)^2 ∂m) - (∫ x, H x*(C-φ x)^2 ∂m) =
      (4*C) * (∫ x, H x*φ x ∂m) := by
    rw [← integral_sub hip him, ← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hzp,hzm,sub_self] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (mul_ne_zero (by norm_num) hC.ne')

lemma weakGradient_pointwise_parallelogram (hfinite : FiniteOnBoundedSets m)
    (hpar : ∀ u v : X → ℝ, Sobolev m u → Sobolev m v →
      (∫ x, (weakGradient m (fun y => u y+v y) x)^2 ∂m) +
        (∫ x, (weakGradient m (fun y => u y-v y) x)^2 ∂m) =
      2*(∫ x, (weakGradient m u x)^2 ∂m) + 2*(∫ x, (weakGradient m v x)^2 ∂m))
    {f g : X → ℝ} (hf : Sobolev m f) (hg : Sobolev m g) :
    ∀ᵐ x ∂m, (weakGradient m (fun y => f y+g y) x)^2 +
      (weakGradient m (fun y => f y-g y) x)^2 =
      2*(weakGradient m f x)^2 + 2*(weakGradient m g x)^2 := by
  have H := ae_eq_zero_of_integral_positive_lipschitz_sq
    (gradientParallelogramDefect_integrable hfinite hf hg)
    (fun η _L hL h1 _A hA hb => weighted_parallelogram_defect_zero hfinite hpar hf hg hL h1 hA hb)
  filter_upwards [H] with x hx
  change gradientParallelogramDefect m f g x = 0 at hx
  dsimp only [gradientParallelogramDefect] at hx
  linarith
end WeakHessian

end
end InlinedFile0

end OAI

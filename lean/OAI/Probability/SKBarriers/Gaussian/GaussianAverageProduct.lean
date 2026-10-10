import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyMomentLevels

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section AverageProduct
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem gaussianAverage_prefix_mul (m : ℝ) (f g : E × ℝ → ℝ) (h : E → ℝ) :
    gaussianAverage m f (fun z => h z.1*g z) = fun z => h z*gaussianAverage m f g z := by
  funext z
  exact integral_const_mul (h z) (fun y : ℝ => g (z,y))
end AverageProduct

theorem hierarchyMomentLevel_mul (n : ℕ) (m : Fin n → ℝ)
    (f g h : ParameterSpace n → ℝ) (j : Fin (n+1)) :
    hierarchyMomentLevel n m f (fun z => hierarchyMomentLevel n m f h j z*g z) j =
      fun z => hierarchyMomentLevel n m f h j z*hierarchyMomentLevel n m f g j z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [hierarchyMomentLevel,Fin.lastCases_last]
    · simp only [hierarchyMomentLevel,Fin.lastCases_castSucc]
      rw [gaussianAverage_prefix_mul]
      simp_rw [ih (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f)
        (gaussianAverage (m (Fin.last n)) f g) (gaussianAverage (m (Fin.last n)) f h) j]

theorem hierarchyAverage_prefix_mul (n : ℕ) (m : Fin n → ℝ)
    (f g h : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (j : Fin (n+1)) (x : ℝ) :
    hierarchyAverage n m f (fun z => hierarchyMomentLevel n m f h j z*g z) x =
      hierarchyAverage n m f
        (fun z => hierarchyMomentLevel n m f h j z*hierarchyMomentLevel n m f g j z) x := by
  rw [← hierarchyAverage_momentLevel n m f _ hf j,hierarchyMomentLevel_mul]

theorem hierarchyPathLaw_prefix_mul (n : ℕ) (m : Fin n → ℝ)
    (f g h : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (hg : Continuous g) (hh : Continuous h)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hgb : ∀ z, ‖g z‖ ≤ C) (hhb : ∀ z, ‖h z‖ ≤ D)
    (j : Fin (n+1)) (x : ℝ) :
    (∫ z, hierarchyMomentLevel n m f h j z*g z ∂hierarchyPathLaw n m f x) =
      ∫ z, hierarchyMomentLevel n m f h j z*hierarchyMomentLevel n m f g j z
        ∂hierarchyPathLaw n m f x := by
  have H := hierarchyMomentLevel_bounded_continuous n m f h hf hh hD hhb j
  have G := hierarchyMomentLevel_bounded_continuous n m f g hf hg hC hgb j
  have hb₁ (z) : ‖hierarchyMomentLevel n m f h j z*g z‖ ≤ D*C := by
    rw [norm_mul]
    exact mul_le_mul (H.2 z) (hgb z) (norm_nonneg _) hD
  have hb₂ (z) : ‖hierarchyMomentLevel n m f h j z*hierarchyMomentLevel n m f g j z‖ ≤ D*C := by
    rw [norm_mul]
    exact mul_le_mul (H.2 z) (G.2 z) (norm_nonneg _) hD
  have hcont₁ : Continuous (fun z => hierarchyMomentLevel n m f h j z*g z) := H.1.mul hg
  have hcont₂ : Continuous (fun z => hierarchyMomentLevel n m f h j z*hierarchyMomentLevel n m f g j z) := H.1.mul G.1
  rw [← hierarchyAverage_eq_integral n m f hf _ hcont₁ (mul_nonneg hD hC) hb₁,
    ← hierarchyAverage_eq_integral n m f hf _ hcont₂ (mul_nonneg hD hC) hb₂]
  exact hierarchyAverage_prefix_mul n m f g h hf j x

end SK.Analytic

end
end
end
end
end
end
end

end OAI

import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianAverageProduct
import OAI.Probability.SKBarriers.Scalar.PathExponentialAverage

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyMomentLevel_exp_regular (n : ℕ) (m : Fin n → ℝ)
    {f g : ParameterSpace n → ℝ} (hf : BoundedDerivs f)
    (hg : Continuous g) (hG : HasExpGrowth g) (j : Fin (n+1)) :
    Continuous (hierarchyMomentLevel n m f g j) ∧
      HasExpGrowth (hierarchyMomentLevel n m f g j) := by
  induction n with
  | zero => exact ⟨hg,hG⟩
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [hierarchyMomentLevel,Fin.lastCases_last] using And.intro hg hG
    · have H := ih (fun i => m i.castSucc) (hf.gaussianStep (m (Fin.last n)))
        (gaussianAverage_continuous_of_expGrowth hf (m (Fin.last n)) hG hg)
        (gaussianAverage_expGrowth hf (m (Fin.last n)) hG) j
      simp only [hierarchyMomentLevel,Fin.lastCases_castSucc]
      refine ⟨H.1.comp continuous_fst,?_⟩
      obtain ⟨C,M,hC,hM,hb⟩ := H.2
      refine ⟨C,M,hC,hM,fun z => (hb z.1).trans ?_⟩
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (norm_fst_le z) hM)) hC

theorem hierarchyPathLaw_prefix_mul_exp (n : ℕ) (m : Fin n → ℝ)
    {f g h : ParameterSpace n → ℝ} (hf : BoundedDerivs f)
    (hg : Continuous g) (hh : Continuous h) (hG : HasExpGrowth g) (hH : HasExpGrowth h)
    (j : Fin (n+1)) (x : ℝ) :
    (∫ z, hierarchyMomentLevel n m f h j z*g z ∂hierarchyPathLaw n m f x) =
      ∫ z, hierarchyMomentLevel n m f h j z*hierarchyMomentLevel n m f g j z ∂hierarchyPathLaw n m f x := by
  have G := hierarchyMomentLevel_exp_regular n m hf hg hG j
  have H := hierarchyMomentLevel_exp_regular n m hf hh hH j
  rw [← hierarchyAverage_eq_integral_exp n m f hf (fun z => hierarchyMomentLevel n m f h j z*g z) (H.1.mul hg) (H.2.mul hG),
    ← hierarchyAverage_eq_integral_exp n m f hf (fun z => hierarchyMomentLevel n m f h j z*hierarchyMomentLevel n m f g j z) (H.1.mul G.1) (H.2.mul G.2)]
  exact hierarchyAverage_prefix_mul n m f g h hf j x

theorem hierarchyPathLaw_fixed_mul_exp (n : ℕ) (m : Fin n → ℝ)
    {f g h : ParameterSpace n → ℝ} (hf : BoundedDerivs f)
    (hg : Continuous g) (hh : Continuous h) (hG : HasExpGrowth g) (hH : HasExpGrowth h)
    (j : Fin (n+1)) (hj : hierarchyMomentLevel n m f h j=h) (x : ℝ) :
    (∫ z, h z*g z ∂hierarchyPathLaw n m f x) =
      ∫ z, h z*hierarchyMomentLevel n m f g j z ∂hierarchyPathLaw n m f x := by
  have H := hierarchyPathLaw_prefix_mul_exp n m hf hg hh hG hH j x
  rwa [hj] at H

theorem hierarchyMomentLevel_coordinate_fixed (n : ℕ) (m : Fin n → ℝ)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (i : Fin n) (j : Fin (n+1))
    (hij : i.val < j.val) :
    hierarchyMomentLevel n m f (coordinateProjection n i) j=coordinateProjection n i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    revert hij
    refine Fin.lastCases (fun _ => ?_) (fun j hij => ?_) j
    · simp only [hierarchyMomentLevel,Fin.lastCases_last]
    · revert hij
      refine Fin.lastCases (fun hij => ?_) (fun i hij => ?_) i
      · simp only [Fin.val_last,Fin.val_castSucc] at hij
        omega
      · have he : (coordinateProjection (n+1) i.castSucc : ParameterSpace (n+1) → ℝ)=
            fun z => coordinateProjection n i z.1 := by funext z; exact coordinateProjection_castSucc n i z
        rw [he]
        simp only [hierarchyMomentLevel,Fin.lastCases_castSucc]
        rw [gaussianAverage_const_prefix hf,ih (fun i => m i.castSucc) (hf.gaussianStep _) i j hij]

end SK.Analytic

end
end

end OAI

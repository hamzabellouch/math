import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyPathLaw
import OAI.Probability.SKBarriers.Gaussian.ExponentialAverage

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
theorem hierarchyPath_integral_succ_exp (n : ℕ) (m : Fin (n+1) → ℝ)
    (f : ParameterSpace (n+1) → ℝ) (hf : BoundedDerivs f) (x : ℝ)
    (g : ParameterSpace (n+1) → ℝ) (hg : Continuous g) (hb : HasExpGrowth g) :
    (∫ z, g z ∂hierarchyPathLaw (n+1) m f x) =
      ∫ z, gaussianAverage (m (Fin.last n)) f g z
        ∂hierarchyPathLaw n (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f) x := by
  rw [hierarchyPathLaw_integral (n+1) m f hf,
    hierarchyPathLaw_integral n _ _ (hf.gaussianStep _),fiberGaussian,
    integral_prod _ (hierarchyPath_exp_integrable (n+1) m f hf x g hg hb)]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [hierarchyPathWeight]
  have he (y : ℝ) : Real.exp (m (Fin.last n)*(f (z,y)-gaussianStep (m (Fin.last n)) f z)) *
      hierarchyPathWeight n (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f) z*g (z,y) =
      hierarchyPathWeight n (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f) z *
      (Real.exp (m (Fin.last n)*(f (z,y)-gaussianStep (m (Fin.last n)) f z))*g (z,y)) := by ring
  simp_rw [he]
  rw [integral_const_mul]
  congr 1
  simp_rw [gaussianTransition_density hf]
  rw [gaussianAverage,gaussianStepLaw_integral_inv_smul]
  simp only [smul_eq_mul,div_eq_mul_inv,mul_assoc,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  ring

theorem hierarchyAverage_eq_integral_exp (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (g : ParameterSpace n → ℝ)
    (hg : Continuous g) (hb : HasExpGrowth g) (x : ℝ) :
    hierarchyAverage n m f g x = ∫ z, g z ∂hierarchyPathLaw n m f x := by
  induction n with
  | zero =>
    rw [hierarchyPathLaw_integral 0 m f hf]
    simp only [hierarchyAverage,hierarchyPathWeight,one_mul,fiberGaussian,integral_dirac]
  | succ n ih =>
    rw [hierarchyPath_integral_succ_exp n m f hf x g hg hb]
    exact ih (fun i => m i.castSucc) _ (hf.gaussianStep _) _
      (gaussianAverage_continuous_of_expGrowth hf _ hb hg) (gaussianAverage_expGrowth hf _ hb)

end SK.Analytic

end
end

end

end OAI

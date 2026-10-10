import Mathlib
import OAI.Probability.SKBarriers.Gaussian.FiberGaussian
import OAI.Probability.SKBarriers.Gaussian.GaussianAverage

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

def hierarchyPathLaw (n : ℕ) (m : Fin n → ℝ) (f : ParameterSpace n → ℝ) (x : ℝ) :
    Measure (ParameterSpace n) := (fiberGaussian n x).withDensity
      (fun z => ENNReal.ofReal (hierarchyPathWeight n m f z))

theorem hierarchyPathLaw_probability (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (x : ℝ) :
    IsProbabilityMeasure (hierarchyPathLaw n m f x) := by
  have h := hierarchyPathWeight_normalized n m f hf x
  constructor
  rw [hierarchyPathLaw,withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal h.1 (ae_of_all _ (fun z => (hierarchyPathWeight_pos n m f z).le)),
    h.2,ENNReal.ofReal_one]

theorem hierarchyPathLaw_integral (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (x : ℝ) (g : ParameterSpace n → ℝ) :
    (∫ z, g z ∂hierarchyPathLaw n m f x) =
      ∫ z, hierarchyPathWeight n m f z*g z ∂fiberGaussian n x := by
  rw [hierarchyPathLaw,integral_withDensity_eq_integral_toReal_smul
    (hierarchyPathWeight_continuous n m f hf).measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hierarchyPathWeight_pos _ _ _ _).le,smul_eq_mul]

theorem hierarchyPath_bounded_integrable (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (x : ℝ)
    (g : ParameterSpace n → ℝ) (hg : Continuous g) {C : ℝ} (hb : ∀ z, ‖g z‖ ≤ C) :
    Integrable (fun z => hierarchyPathWeight n m f z*g z) (fiberGaussian n x) := by
  have hw := (hierarchyPathWeight_normalized n m f hf x).1
  apply (hw.mul_const C).mono' ((hierarchyPathWeight_continuous n m f hf).mul hg).aestronglyMeasurable
  filter_upwards [] with z
  change ‖hierarchyPathWeight n m f z*g z‖ ≤ _
  rw [norm_mul,Real.norm_eq_abs,abs_of_pos (hierarchyPathWeight_pos _ _ _ _)]
  exact mul_le_mul_of_nonneg_left (hb z) (hierarchyPathWeight_pos _ _ _ _).le

theorem hierarchyPath_integral_succ (n : ℕ) (m : Fin (n+1) → ℝ)
    (f : ParameterSpace (n+1) → ℝ) (hf : BoundedDerivs f) (x : ℝ)
    (g : ParameterSpace (n+1) → ℝ) (hg : Continuous g) {C : ℝ} (hb : ∀ z, ‖g z‖ ≤ C) :
    (∫ z, g z ∂hierarchyPathLaw (n+1) m f x) =
      ∫ z, gaussianAverage (m (Fin.last n)) f g z
        ∂hierarchyPathLaw n (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f) x := by
  rw [hierarchyPathLaw_integral (n+1) m f hf,
    hierarchyPathLaw_integral n _ _ (hf.gaussianStep _),fiberGaussian,
    integral_prod _ (hierarchyPath_bounded_integrable (n+1) m f hf x g hg hb)]
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

def hierarchyAverage : (n : ℕ) → (Fin n → ℝ) → (ParameterSpace n → ℝ) →
    (ParameterSpace n → ℝ) → ℝ → ℝ
  | 0,_,_,g => g
  | n+1,m,f,g => hierarchyAverage n (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f)
      (gaussianAverage (m (Fin.last n)) f g)

theorem hierarchyAverage_eq_integral (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (g : ParameterSpace n → ℝ)
    (hg : Continuous g) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ z, ‖g z‖ ≤ C) (x : ℝ) :
    hierarchyAverage n m f g x = ∫ z, g z ∂hierarchyPathLaw n m f x := by
  induction n with
  | zero =>
    rw [hierarchyPathLaw_integral 0 m f hf]
    simp only [hierarchyAverage,hierarchyPathWeight,one_mul,fiberGaussian,integral_dirac]
  | succ n ih =>
    rw [hierarchyPath_integral_succ n m f hf x g hg hb]
    exact ih (fun i => m i.castSucc) _ (hf.gaussianStep _) _
      (gaussianAverage_continuous hf _ hg hC hb) (fun z => gaussianAverage_norm_le hf _ hb z)

end SK.Analytic

end
end
end
end
end
end
end

end OAI

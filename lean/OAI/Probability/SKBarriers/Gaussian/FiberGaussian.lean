import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyPenalty
import OAI.Probability.SKBarriers.Gaussian.GaussianStepCalculus

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
namespace SK.Analytic

def fiberGaussian : (n : ℕ) → ℝ → Measure (ParameterSpace n)
  | 0, x => Measure.dirac x
  | n+1, x => (fiberGaussian n x).prod (gaussianReal 0 1)

instance fiberGaussian_probability : (n : ℕ) → (x : ℝ) → IsProbabilityMeasure (fiberGaussian n x)
  | 0, x => inferInstanceAs (IsProbabilityMeasure (Measure.dirac x))
  | n+1, x => by
      let := fiberGaussian_probability n x
      exact inferInstanceAs (IsProbabilityMeasure ((fiberGaussian n x).prod (gaussianReal 0 1)))

theorem hierarchyPathWeight_pos (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (z : ParameterSpace n) :
    0 < hierarchyPathWeight n m f z := by
  rw [hierarchyPathWeight_eq n m f 1]
  exact Real.exp_pos _

theorem hierarchyPathWeight_continuous (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) :
    Continuous (hierarchyPathWeight n m f) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have hs := hf.gaussianStep (m (Fin.last n))
    exact (Real.continuous_exp.comp (continuous_const.mul
      (hf.1.continuous.sub (hs.1.continuous.comp continuous_fst)))).mul
      ((ih (fun i => m i.castSucc) _ hs).comp continuous_fst)

theorem hierarchyPathWeight_normalized (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (x : ℝ) :
    Integrable (hierarchyPathWeight n m f) (fiberGaussian n x) ∧
      (∫ z, hierarchyPathWeight n m f z ∂fiberGaussian n x) = 1 := by
  induction n with
  | zero =>
    constructor
    · change Integrable (fun _ : ℝ => (1 : ℝ)) (Measure.dirac x)
      exact integrable_const _
    · simp [fiberGaussian,hierarchyPathWeight]
  | succ n ih =>
    have ih' := ih (fun i => m i.castSucc) _ (hf.gaussianStep (m (Fin.last n)))
    let w : ParameterSpace n → ℝ := hierarchyPathWeight n (fun i => m i.castSucc)
      (gaussianStep (m (Fin.last n)) f)
    have hi (z : ParameterSpace n) : Integrable
        (fun y => hierarchyPathWeight (n+1) m f (z,y)) (gaussianReal 0 1) := by
      change Integrable (fun y => Real.exp (m (Fin.last n)*
        (f (z,y)-gaussianStep (m (Fin.last n)) f z))*w z) _
      simp_rw [gaussianTransition_density hf]
      exact ((hf.exp_integrable (m (Fin.last n)) z).div_const _).mul_const _
    have he (z : ParameterSpace n) :
        (∫ y, hierarchyPathWeight (n+1) m f (z,y) ∂gaussianReal 0 1) = w z := by
      change (∫ y, Real.exp (m (Fin.last n)*(f (z,y)-gaussianStep (m (Fin.last n)) f z))*w z
        ∂gaussianReal 0 1) = w z
      rw [integral_mul_const,gaussianTransition_integral_one hf,one_mul]
    have hnorm (z : ParameterSpace n) :
        (∫ y, ‖hierarchyPathWeight (n+1) m f (z,y)‖ ∂gaussianReal 0 1) = w z := by
      simp only [Real.norm_eq_abs,abs_of_pos (hierarchyPathWeight_pos _ _ _ _)]
      exact he z
    have hprod : Integrable (hierarchyPathWeight (n+1) m f) (fiberGaussian (n+1) x) := by
      apply (integrable_prod_iff (hierarchyPathWeight_continuous _ _ _ hf).aestronglyMeasurable).2
      refine ⟨ae_of_all _ hi,?_⟩
      simpa only [hnorm] using ih'.1
    refine ⟨hprod,?_⟩
    rw [fiberGaussian,integral_prod _ hprod]
    simp only [he]
    exact ih'.2

def fiberGaussianDensity (n : ℕ) (z : ParameterSpace n) : ℝ :=
  (Real.sqrt (2*Real.pi))⁻¹^n * Real.exp (-coordinateSquare n z/2)

theorem fiberGaussianDensity_pos (n : ℕ) (z : ParameterSpace n) :
    0 < fiberGaussianDensity n z := by
  unfold fiberGaussianDensity
  positivity

theorem fiberGaussianDensity_continuous (n : ℕ) : Continuous (fiberGaussianDensity n) := by
  exact continuous_const.mul (Real.continuous_exp.comp
    ((continuous_coordinateSquare n).neg.div_const 2))

theorem fiberGaussianDensity_succ (n : ℕ) (z : ParameterSpace (n+1)) :
    fiberGaussianDensity (n+1) z = fiberGaussianDensity n z.1*gaussianPDFReal 0 1 z.2 := by
  unfold fiberGaussianDensity gaussianPDFReal
  simp only [NNReal.coe_one,mul_one,sub_zero,coordinateSquare]
  rw [pow_succ _ n]
  rw [show -(coordinateSquare n z.1+z.2^2)/2 = -coordinateSquare n z.1/2 + -z.2^2/2 by ring,
    Real.exp_add]
  ring

theorem fiberGaussian_eq_withDensity (n : ℕ) (x : ℝ) :
    fiberGaussian n x = (fiberMeasure n x).withDensity
      (fun z => ENNReal.ofReal (fiberGaussianDensity n z)) := by
  induction n with
  | zero => simp [fiberGaussian,fiberMeasure,fiberGaussianDensity,coordinateSquare]
  | succ n ih =>
    rw [fiberGaussian,ih,gaussianReal_of_var_ne_zero _ (by norm_num : (1 : NNReal) ≠ 0),
      prod_withDensity (fiberGaussianDensity_continuous n).measurable.ennreal_ofReal
        (measurable_gaussianPDF _ _)]
    apply congrArg ((fiberMeasure (n+1) x).withDensity)
    funext z
    rw [fiberGaussianDensity_succ,ENNReal.ofReal_mul (fiberGaussianDensity_pos n z.1).le]
    rfl

end SK.Analytic

end
end
end
end
end
end

end OAI

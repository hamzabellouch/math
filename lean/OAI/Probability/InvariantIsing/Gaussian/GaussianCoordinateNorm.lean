import OAI.Probability.InvariantIsing.Gaussian.GaussianSingularFluctuation

namespace OAI

/-! Exact second moments and the square-root dimension bound for coordinate Gaussian norms. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace InvariantIsing
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def gaussianCoordinateVector (e : κ → ι) (g : ι → ℝ) : EuclideanSpace ℝ κ :=
  WithLp.toLp 2 (fun j => g (e j))

lemma gaussianCoordinate_memLp (i : ι) :
    MemLp (fun g : ι → ℝ => g i) 2 (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  exact (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).hasLaw.memLp
    (IsGaussian.memLp_id _ 2 (by norm_num))

lemma gaussianCoordinate_sq_integral (i : ι) :
    (∫ g : ι → ℝ, (g i)^2 ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) = 1 := by
  have he : (∫ g : ι → ℝ, (g i)^2 ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      ∫ x : ℝ, x^2 ∂gaussianReal 0 1 := by
    simpa only [Function.comp_def,Function.eval] using
      (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).hasLaw.integral_comp
        (f := fun x : ℝ => x^2) (by fun_prop)
  rw [he]
  have hv := variance_of_integral_eq_zero (μ := gaussianReal 0 1)
    (X := id) (by fun_prop) (by simp)
  simpa only [variance_id_gaussianReal,NNReal.coe_one,id_eq] using hv.symm

lemma gaussianCoordinateVector_sq_integrable (e : κ → ι) :
    Integrable (fun g => ‖gaussianCoordinateVector e g‖^2)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  simpa only [gaussianCoordinateVector,EuclideanSpace.real_norm_sq_eq,PiLp.toLp_apply]
    using integrable_finsetSum Finset.univ (fun j _ => (gaussianCoordinate_memLp (e j)).integrable_sq)

lemma gaussianCoordinateVector_memLp (e : κ → ι) :
    MemLp (gaussianCoordinateVector e) 2 (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  have hm : Continuous (gaussianCoordinateVector e) := by
    unfold gaussianCoordinateVector
    exact (PiLp.continuous_toLp 2 (fun _ : κ => ℝ)).comp
      (continuous_pi (fun j => continuous_apply (e j)))
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  exact gaussianCoordinateVector_sq_integrable e

lemma gaussianCoordinateVector_sq_integral (e : κ → ι) :
    (∫ g, ‖gaussianCoordinateVector e g‖^2
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) = Fintype.card κ := by
  simp only [gaussianCoordinateVector,EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum _ (fun j _ => (gaussianCoordinate_memLp (e j)).integrable_sq)]
  simp only [gaussianCoordinate_sq_integral,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]

lemma gaussianCoordinateVector_norm_integral_le (e : κ → ι) :
    (∫ g, ‖gaussianCoordinateVector e g‖
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) ≤ Real.sqrt (Fintype.card κ) := by
  have hvar := variance_nonneg (fun g => ‖gaussianCoordinateVector e g‖)
    (Measure.pi (fun _ : ι => gaussianReal 0 1))
  rw [variance_eq_sub (gaussianCoordinateVector_memLp e).norm] at hvar
  change 0 ≤ (∫ g, ‖gaussianCoordinateVector e g‖^2
    ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) - _ at hvar
  rw [gaussianCoordinateVector_sq_integral] at hvar
  have hs : (Real.sqrt (Fintype.card κ))^2 = (Fintype.card κ : ℝ) := Real.sq_sqrt (by positivity)
  have hp := Real.sqrt_nonneg (Fintype.card κ)
  nlinarith

end InvariantIsing

end

end OAI

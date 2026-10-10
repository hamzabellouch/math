import OAI.Probability.InvariantIsing.Gaussian.MPAngularTransform
import Mathlib.MeasureTheory.Function.JacobianOneDim

namespace OAI

/-! The exact change of variables for the displayed Marchenko--Pastur density. -/
noncomputable section
open Real Set
namespace InvariantIsing

def mpDensity (α x : ℝ) : ℝ :=
  sqrt ((marchenkoPasturB α-x)*(x-marchenkoPasturA α))/(2*Real.pi*x)

def mpAngle (α x : ℝ) : ℝ := 1+α+2*sqrt α*cos x

lemma mpAngle_endpoints {α : ℝ} (hα : 0 ≤ α) :
    mpAngle α 0 = marchenkoPasturB α ∧ mpAngle α Real.pi = marchenkoPasturA α := by
  obtain ⟨ha,hb⟩ := mp_edge_centre_radius hα
  constructor
  · simp only [mpAngle,cos_zero,mul_one,hb]
  · simp only [mpAngle,cos_pi,mul_neg_one,ha,sub_eq_add_neg]

lemma mpAngle_hasDerivAt (α x : ℝ) :
    HasDerivAt (mpAngle α) (-(2*sqrt α)*sin x) x := by
  unfold mpAngle
  convert ((hasDerivAt_cos x).const_mul (2*sqrt α)).const_add (1+α) using 1
  simp only [mul_neg, neg_mul]

lemma mpAngle_sqrt {α x : ℝ} (hα : 0 ≤ α) (hx : x ∈ Icc 0 Real.pi) :
    sqrt ((marchenkoPasturB α-mpAngle α x)*(mpAngle α x-marchenkoPasturA α)) =
      2*sqrt α*sin x := by
  obtain ⟨ha,hb⟩ := mp_edge_centre_radius hα
  have he : (marchenkoPasturB α-mpAngle α x)*(mpAngle α x-marchenkoPasturA α) =
      (2*sqrt α*sin x)^2 := by
    rw [ha,hb]
    unfold mpAngle
    linear_combination -(2*sqrt α)^2*(sin_sq_add_cos_sq x)
  rw [he,sqrt_sq]
  exact mul_nonneg (by positivity) (sin_nonneg_of_nonneg_of_le_pi hx.1 hx.2)

lemma mpAngle_density_jacobian {α x : ℝ} (hα : 0 ≤ α) (hx : x ∈ Icc 0 Real.pi) :
    (2*sqrt α*sin x)*mpDensity α (mpAngle α x) =
      (2*α/Real.pi)*((sin x)^2/mpAngle α x) := by
  unfold mpDensity
  rw [mpAngle_sqrt hα hx]
  ring_nf
  rw [sq_sqrt hα]
  ring

end InvariantIsing

end

end OAI

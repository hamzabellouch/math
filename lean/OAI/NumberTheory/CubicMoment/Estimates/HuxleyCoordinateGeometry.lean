import OAI.NumberTheory.CubicMoment.Estimates.HuxleyPhase
import OAI.NumberTheory.CubicGram.EuclideanDomain

namespace OAI

/-! Coordinates for the Gaussian majorant in the additive large sieve. -/
noncomputable section
namespace CubicFirstMoment

def huxleyXi₀ (x : ℂ) : ℝ := 2*x.im/Real.sqrt 3
def huxleyXi₁ (x : ℂ) : ℝ := x.re-x.im/Real.sqrt 3

lemma huxley_frequency_coordinates (x : ℂ) (a b : ℤ) :
    tracePair (ofCoords a b : ℂ) (x/traceLambda) =
      (a:ℝ)*huxleyXi₀ x+(b:ℝ)*huxleyXi₁ x := by
  have hs : Real.sqrt (3:ℝ) ≠ 0 := by positivity
  have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  rw [traceLambda_eq]
  simp only [tracePair,ofCoords_coe,Complex.mul_re,Complex.mul_im,
    Complex.add_re,Complex.add_im,Complex.intCast_re,Complex.intCast_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    omega_re,omega_im,Complex.div_re,Complex.div_im,Complex.normSq_apply,
    huxleyXi₀,huxleyXi₁]
  field_simp
  nlinarith

lemma huxley_frequency_phase_coordinates (x : ℂ) (a b : ℤ) :
    huxleyFrequencyPhase x (ofCoords a b) =
      Complex.exp (((2*Real.pi*(a:ℝ)*huxleyXi₀ x:ℝ):ℂ)*Complex.I)*
      Complex.exp (((2*Real.pi*(b:ℝ)*huxleyXi₁ x:ℝ):ℂ)*Complex.I) := by
  unfold huxleyFrequencyPhase
  rw [huxley_frequency_coordinates,Real.fourierChar_apply,← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma huxley_dual_coordinate_distance (x : ℂ) (m n : ℤ) :
    ‖(ofCoords (m+n) m : ℂ)-x‖^2 ≤
      (3/2:ℝ)*(((m:ℝ)-huxleyXi₀ x)^2+((n:ℝ)-huxleyXi₁ x)^2) := by
  have hs : Real.sqrt (3:ℝ) ≠ 0 := by positivity
  let u := (m:ℝ)-huxleyXi₀ x
  let v := (n:ℝ)-huxleyXi₁ x
  have hd : (ofCoords (m+n) m : ℂ)-x = ((u+v:ℝ):ℂ)+(u:ℂ)*omega := by
    apply Complex.ext <;>
      simp [ofCoords_coe,u,v,huxleyXi₀,huxleyXi₁,Complex.mul_re,Complex.mul_im] <;>
      field_simp
    all_goals ring
  rw [← Complex.normSq_eq_norm_sq]
  rw [hd,real_coordinates_norm]
  change (u+v)^2-(u+v)*u+u^2 ≤ (3/2:ℝ)*(u^2+v^2)
  nlinarith [sq_nonneg (u-v)]

lemma huxley_coordinate_energy (a b : ℤ) :
    (a:ℝ)^2+(b:ℝ)^2 ≤ 2*norm (ofCoords a b) := by
  rw [norm,ofCoords_coe,coordinates_norm]
  push_cast
  nlinarith [sq_nonneg ((a:ℝ)-(b:ℝ))]

end CubicFirstMoment

end

end OAI

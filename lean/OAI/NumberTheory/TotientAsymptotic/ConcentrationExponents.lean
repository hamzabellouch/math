import OAI.NumberTheory.TotientAsymptotic.RenewalRatios

namespace OAI

/-! The numerical exponent saving for fixed one-fortieth deviations. -/
noncomputable section
namespace TotientAsymptotic

def concentrationTilt (M : ℝ) : ℝ := 1/(320*M)

lemma concentrationTilt_pos {M : ℝ} (hM : 1 ≤ M) : 0 < concentrationTilt M := by
  unfold concentrationTilt
  positivity

lemma concentrationTilt_mul {M : ℝ} (hM : 1 ≤ M) : concentrationTilt M*M = 1/320 := by
  unfold concentrationTilt
  field_simp

lemma concentrationTilt_le {M : ℝ} (hM : 1 ≤ M) : concentrationTilt M ≤ 1/320 := by
  have hs := concentrationTilt_pos hM
  have hm := concentrationTilt_mul hM
  nlinarith

lemma concentration_exponents {M K m S Q : ℝ} (hM : 1 ≤ M) (hK : 0 ≤ K)
    (hm : 1 ≤ m) (hS : |S-m| ≤ K) (hQ : Q ≤ M*(m+K)) :
    let s := concentrationTilt M
    (s*(39/40)*(m-1)-s*S+2*s^2*Q ≤ 3*s*(K+1)-(s/100)*(m-1)) ∧
    (-s*(41/40)*(m-1)+s*S+2*s^2*Q ≤ 3*s*(K+1)-(s/100)*(m-1)) := by
  dsimp only
  let s := concentrationTilt M
  have hs : 0 < s := concentrationTilt_pos hM
  have hsm : s*M = 1/320 := concentrationTilt_mul hM
  have hquad : 2*s^2*Q ≤ (s/160)*(m+K) := by
    have hh := mul_le_mul_of_nonneg_left hQ (show 0 ≤ 2*s^2 by positivity)
    have he : 2*s^2*(M*(m+K)) = (s/160)*(m+K) := by
      calc
        _ = 2*s*(s*M)*(m+K) := by ring
        _ = _ := by rw [hsm]; ring
    exact hh.trans_eq he
  have hSm := abs_le.mp hS
  have hSl := mul_le_mul_of_nonneg_left hSm.1 hs.le
  have hSu := mul_le_mul_of_nonneg_left hSm.2 hs.le
  have hsk : 0 ≤ s*K := mul_nonneg hs.le hK
  have hsm' : s ≤ s*m := le_mul_of_one_le_right hs.le hm
  constructor <;> dsimp only [s] at * <;> nlinarith

end TotientAsymptotic

end

end OAI

import OAI.NumberTheory.TotientAsymptotic.Basic

namespace OAI

/-! The square-root tilt giving the saving in the normality tail. -/
noncomputable section
namespace TotientAsymptotic

def normalityTilt (A B : ℝ) : ℝ := Real.sqrt A/(4*Real.sqrt B)

lemma normalityTilt_pos {A B : ℝ} (hA : 0<A) (hAB : A≤B) :
    0<normalityTilt A B := by
  have hB : 0<B := hA.trans_le hAB
  unfold normalityTilt
  exact div_pos (Real.sqrt_pos.mpr hA) (by positivity)

lemma normalityTilt_le {A B : ℝ} (hA : 0<A) (hAB : A≤B) :
    normalityTilt A B≤1/4 := by
  have hB : 0<B := hA.trans_le hAB
  unfold normalityTilt
  apply (div_le_iff₀ (by positivity : 0<4*Real.sqrt B)).mpr
  have hh := Real.sqrt_le_sqrt hAB
  nlinarith

lemma normalityTilt_exponent {A B M : ℝ} (hA : 0<A) (hAB : A≤B) (hM : M≤B) :
    (normalityTilt A B)^2*M-normalityTilt A B*(Real.sqrt (A*B)-4) ≤ 1-A/6 := by
  have hB : 0<B := hA.trans_le hAB
  have hsqA := Real.sq_sqrt hA.le
  have hsqB := Real.sq_sqrt hB.le
  have hsB : Real.sqrt B≠0 := (Real.sqrt_pos.mpr hB).ne'
  have h1 : normalityTilt A B * Real.sqrt (A*B) = A/4 := by
    rw [Real.sqrt_mul hA.le]
    unfold normalityTilt
    field_simp
    nlinarith
  have h2 : (normalityTilt A B)^2*B = A/16 := by
    unfold normalityTilt
    field_simp
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hM (sq_nonneg (normalityTilt A B))
  have ht := normalityTilt_le hA hAB
  rw [h2] at hm
  nlinarith

end TotientAsymptotic

end

end OAI

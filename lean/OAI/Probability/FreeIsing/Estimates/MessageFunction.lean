import OAI.Probability.FreeIsing.Energy.Attenuation

namespace OAI

noncomputable section

namespace Problem367

def cavityMessage (theta z : ℝ) : ℝ :=
  Real.artanh (theta * Real.tanh z)

lemma hasDerivAt_artanh_interval {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.artanh (1 / (1 - x ^ 2)) x := by
  have hminus : 0 < 1 - x := sub_pos.mpr hx.2
  have hplus : 0 < 1 + x := by linarith [hx.1]
  have hratio : 0 < (1 + x) / (1 - x) := div_pos hplus hminus
  have hsqrt : 0 < Real.sqrt ((1 + x) / (1 - x)) := Real.sqrt_pos.mpr hratio
  have hsq : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hr := ((hasDerivAt_id x).const_add 1).div
    ((hasDerivAt_id x).const_sub 1) hminus.ne'
  have hh := (hr.sqrt hratio.ne').log hsqrt.ne'
  change HasDerivAt Real.artanh _ x at hh
  apply hh.congr_deriv
  dsimp
  have hs := Real.sq_sqrt hratio.le
  field_simp
  rw [hs]
  field_simp
  ring

lemma cavityMessage_argument_mem {theta : ℝ} (hθ : theta ^ 2 ≤ 1) (z : ℝ) :
    theta * Real.tanh z ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hmul := mul_le_mul_of_nonneg_right hθ (sq_nonneg (Real.tanh z))
  have hs : (theta * Real.tanh z) ^ 2 < 1 := by
    nlinarith [Real.tanh_sq_lt_one z]
  exact abs_lt.mp ((sq_lt_one_iff_abs_lt_one _).mp hs)

lemma hasDerivAt_cavityMessage {theta : ℝ} (hθ : theta ^ 2 ≤ 1) (z : ℝ) :
    HasDerivAt (cavityMessage theta) (theta * responseAttenuation theta z) z := by
  have ha := hasDerivAt_artanh_interval (cavityMessage_argument_mem hθ z)
  have ht := (hasDerivAt_tanh_response z).const_mul theta
  have hh := ha.comp z ht
  change HasDerivAt (cavityMessage theta) _ z at hh
  apply hh.congr_deriv
  unfold responseAttenuation
  ring

@[simp] lemma cavityMessage_zero (theta : ℝ) : cavityMessage theta 0 = 0 := by
  simp [cavityMessage]

lemma artanh_neg_of_mem {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Real.artanh (-x) = -Real.artanh x := by
  have hn : -x ∈ Set.Ioo (-1 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  apply Real.tanh_injective
  rw [Real.tanh_artanh hn, Real.tanh_neg, Real.tanh_artanh hx]

lemma cavityMessage_neg {theta : ℝ} (hθ : theta ^ 2 ≤ 1) (z : ℝ) :
    cavityMessage theta (-z) = -cavityMessage theta z := by
  simp only [cavityMessage, Real.tanh_neg, mul_neg]
  exact artanh_neg_of_mem (cavityMessage_argument_mem hθ z)

lemma abs_deriv_cavityMessage_le {theta : ℝ} (hθ0 : 0 ≤ theta) (hθ1 : theta ≤ 1) (z : ℝ) :
    |deriv (cavityMessage theta) z| ≤ theta := by
  have hsq : theta ^ 2 ≤ 1 := by nlinarith
  rw [(hasDerivAt_cavityMessage hsq z).deriv, abs_mul,
    abs_of_nonneg hθ0, abs_of_pos (responseAttenuation_pos hsq z)]
  simpa using mul_le_mul_of_nonneg_left (responseAttenuation_le_one hsq z) hθ0

lemma lipschitzWith_cavityMessage {theta : ℝ} (hθ0 : 0 ≤ theta) (hθ1 : theta ≤ 1) :
    LipschitzWith ⟨theta, hθ0⟩ (cavityMessage theta) := by
  have hsq : theta ^ 2 ≤ 1 := by nlinarith
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro z
    exact (hasDerivAt_cavityMessage hsq z).differentiableAt
  · intro z
    exact_mod_cast abs_deriv_cavityMessage_le hθ0 hθ1 z

lemma cavityMessage_abs_le_mul {theta : ℝ} (hθ0 : 0 ≤ theta) (hθ1 : theta ≤ 1) (z : ℝ) :
    |cavityMessage theta z| ≤ theta * |z| := by
  have h := (lipschitzWith_cavityMessage hθ0 hθ1).dist_le_mul z 0
  change dist (cavityMessage theta z) (cavityMessage theta 0) ≤ theta * dist z 0 at h
  simpa only [Real.dist_eq, cavityMessage_zero, sub_zero] using h

lemma cavityMessage_monotone {theta : ℝ} (hθ0 : 0 ≤ theta) (hθ1 : theta ≤ 1) :
    Monotone (cavityMessage theta) := by
  have hsq : theta ^ 2 ≤ 1 := by nlinarith
  apply monotone_of_deriv_nonneg
  · intro z
    exact (hasDerivAt_cavityMessage hsq z).differentiableAt
  · intro z
    rw [(hasDerivAt_cavityMessage hsq z).deriv]
    exact mul_nonneg hθ0 (responseAttenuation_pos hsq z).le

lemma cavityMessage_le_artanh {theta : ℝ} (hθ0 : 0 ≤ theta) (hθ1 : theta < 1) (z : ℝ) :
    cavityMessage theta z ≤ Real.artanh theta := by
  have hsq : theta ^ 2 ≤ 1 := by nlinarith
  apply Real.artanh_le_artanh (cavityMessage_argument_mem hsq z).1 hθ1
  simpa using mul_le_mul_of_nonneg_left (Real.tanh_lt_one z).le hθ0

lemma cavityMessage_abs_le_artanh {theta : ℝ} (hθ0 : 0 ≤ theta) (hθ1 : theta < 1) (z : ℝ) :
    |cavityMessage theta z| ≤ Real.artanh theta := by
  have hsq : theta ^ 2 ≤ 1 := by nlinarith
  apply abs_le.mpr
  constructor
  · have h := cavityMessage_le_artanh hθ0 hθ1 (-z)
    rw [cavityMessage_neg hsq z] at h
    linarith
  · exact cavityMessage_le_artanh hθ0 hθ1 z

lemma cavityMessage_abs_ge_tanh {theta : ℝ} (hθ : theta ^ 2 ≤ 1) (z : ℝ) :
    |theta| * |Real.tanh z| ≤ |cavityMessage theta z| := by
  have h := abs_tanh_le_abs_response (Real.artanh (theta * Real.tanh z))
  rw [Real.tanh_artanh (cavityMessage_argument_mem hθ z), abs_mul] at h
  exact h

end Problem367

end

end OAI

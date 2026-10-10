import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleWeightedEnergy

namespace OAI

/-! A fixed-radius dilation boundary form is bounded by its weighted
Cauchy energy whenever its real coefficients obey uniform bounds. -/

namespace DefocusingNLS

theorem spectralDilationBoundary_estimate (M V J omega W Q S A s q : ℝ) (f df : ℂ)
    (hM : 0 ≤ M) (ho : 1 ≤ omega) (hW : 0 ≤ W) (hQ : 0 ≤ Q)
    (hS : 0 ≤ S) (hA : 0 ≤ A)
    (hV : |V| ≤ W*M) (hJ : |J| ≤ W*A*omega*M) (hs : |s| ≤ S) (hq : |q| ≤ Q) :
    |V/2*(q*‖f‖^2-‖df‖^2)-M*s*(star f*df).re+J/2*‖f‖^2| ≤
      (W*(Q+1)+S+W*A)*M*(omega*‖f‖^2+‖df‖^2) := by
  let E := omega*‖f‖^2+‖df‖^2
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hv : ‖f‖^2 ≤ E := by dsimp only [E]; nlinarith [sq_nonneg ‖f‖,sq_nonneg ‖df‖]
  have hd : ‖df‖^2 ≤ E := by dsimp only [E]; nlinarith [mul_nonneg (show 0 ≤ omega by linarith) (sq_nonneg ‖f‖)]
  have hwv : omega*‖f‖^2 ≤ E := by dsimp only [E]; nlinarith [sq_nonneg ‖df‖]
  have hc : |(star f*df).re| ≤ E := by
    have hr := Complex.abs_re_le_norm (star f*df)
    rw [norm_mul,norm_star] at hr
    have hp : ‖f‖*‖df‖ ≤ E := by nlinarith [sq_nonneg (‖f‖-‖df‖)]
    exact hr.trans hp
  have hqf : |q*‖f‖^2-‖df‖^2| ≤ (Q+1)*E := by
    calc
      _ ≤ |q*‖f‖^2|+|‖df‖^2| := abs_sub _ _
      _ = |q| *‖f‖^2+‖df‖^2 := by rw [abs_mul,abs_of_nonneg (sq_nonneg ‖f‖),abs_of_nonneg (sq_nonneg ‖df‖)]
      _ ≤ Q*E+E := add_le_add (mul_le_mul hq hv (sq_nonneg _) hQ) hd
      _ = _ := by ring
  have h1 : |V/2*(q*‖f‖^2-‖df‖^2)| ≤ W*M/2*((Q+1)*E) := by
    rw [abs_mul,abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)]
    exact mul_le_mul (div_le_div_of_nonneg_right hV (by norm_num)) hqf (abs_nonneg _) (by positivity)
  have h2 : |M*s*(star f*df).re| ≤ M*S*E := by
    simp only [abs_mul,abs_of_nonneg hM]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hs hM) hc (abs_nonneg _) (mul_nonneg hM hS)
  have h3 : |J/2*‖f‖^2| ≤ W*A*M/2*E := by
    rw [abs_mul,abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2),abs_of_nonneg (sq_nonneg ‖f‖)]
    calc
      _ ≤ W*A*omega*M/2*‖f‖^2 := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hJ (by norm_num)) (sq_nonneg _)
      _ = W*A*M/2*(omega*‖f‖^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hwv (by positivity)
  have ht := (abs_add_le (V/2*(q*‖f‖^2-‖df‖^2)-M*s*(star f*df).re) (J/2*‖f‖^2)).trans
    (add_le_add (abs_sub _ _) le_rfl)
  have hpos : 0 ≤ W*M*(Q+1)*E+W*A*M*E := by positivity
  change _ ≤ (W*(Q+1)+S+W*A)*M*E
  nlinarith only [ht,h1,h2,h3,hpos]

end DefocusingNLS

end OAI

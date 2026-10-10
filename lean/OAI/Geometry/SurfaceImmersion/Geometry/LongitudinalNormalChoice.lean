import OAI.Geometry.SurfaceImmersion.Primitive.CrossingNormalPath

namespace OAI

/-! Away from turns, the two pure normal directions have positive pairing and
lie in the same open half-plane.  This supplies the crossing normal path. -/
noncomputable section
namespace ClosedSurfaceR4.GeometryPreservation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma mixed_difference_norm_bound {n m : E} (hn : ‖n‖ = 1) (hm : ‖m‖ = 1)
    {S D N L k t u sHi d T : ℝ} (hS : 0 < S) (hShi : S ≤ sHi)
    (hD : |D| ≤ d) (ht : |t| ≤ T) (hu : |u| ≤ T) :
    ‖frameVector n m (slopeMixed S D N L k t u)-
      frameVector n m (slopePure S D N L k t)‖ ≤ 2*T*(d+sHi*T+|N|) := by
  rw [← frameVector_sub,mixed_sub_left hS.ne',frameVector_smul,norm_smul,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (frameVector_norm_le hn hm _) (abs_nonneg _)).trans
    (crossing_slope_bound hS.le hShi hD ht hu)

lemma slopeMixed_symm (S D N L k t u : ℝ) :
    slopeMixed S D N L k t u = slopeMixed S D N L k u t := by
  ext <;> dsimp [slopeMixed] <;> ring

lemma pure_difference_norm_bound {n m : E} (hn : ‖n‖ = 1) (hm : ‖m‖ = 1)
    {S D N L k t u sHi d T : ℝ} (hS : 0 < S) (hShi : S ≤ sHi)
    (hD : |D| ≤ d) (ht : |t| ≤ T) (hu : |u| ≤ T) :
    ‖frameVector n m (slopePure S D N L k u)-
      frameVector n m (slopePure S D N L k t)‖ ≤ 4*T*(d+sHi*T+|N|) := by
  let P := frameVector n m (slopePure S D N L k t)
  let Q := frameVector n m (slopePure S D N L k u)
  let Z := frameVector n m (slopeMixed S D N L k t u)
  have hP : ‖Z-P‖ ≤ 2*T*(d+sHi*T+|N|) := mixed_difference_norm_bound hn hm hS hShi hD ht hu
  have hQ : ‖Z-Q‖ ≤ 2*T*(d+sHi*T+|N|) := by
    dsimp [Z,Q]
    rw [slopeMixed_symm]
    exact mixed_difference_norm_bound hn hm hS hShi hD hu ht
  have hsplit : Q-P = (Q-Z)+(Z-P) := by abel
  have hh := norm_add_le (Q-Z) (Z-P)
  rw [← hsplit,norm_sub_rev Q Z] at hh
  change ‖Q-P‖ ≤ _
  linarith

lemma inner_pos_of_difference_lt_norm {P Q : E} (h : ‖Q-P‖ < ‖P‖) :
    0 < inner ℝ P Q := by
  have hP : P ≠ 0 := by intro hz; rw [hz,norm_zero] at h; exact (not_lt_of_ge (norm_nonneg _) h)
  have hb := mixed_projection_lower (Z := Q) hP
  have hp : 0 < inner ℝ Q (‖P‖⁻¹ • P) := by linarith
  rw [real_inner_smul_right] at hp
  have hi : 0 < ‖P‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hP)
  rw [real_inner_comm]
  nlinarith

lemma double_product_bound {N t B T : ℝ} (hB : 0 ≤ B) (hN : |N| ≤ B) (ht : |t| ≤ T) :
    |2*N*t| ≤ 2*B*T := by
  simp only [abs_mul,show |(2 : ℝ)| = 2 by norm_num]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hN (by norm_num)) ht
    (abs_nonneg _) (by positivity)

theorem longitudinal_normal_choice (sHi d B T : ℝ) (hsHi : 0 ≤ sHi)
    (hd : 0 ≤ d) (hB : 0 ≤ B) (hT : 0 ≤ T) :
    ∃ J : ℝ, 0 < J ∧ ∀ n m : E, ‖n‖ = 1 → ‖m‖ = 1 → inner ℝ m n = 0 →
    ∀ S D N L k t u : ℝ, 0 < S → S ≤ sHi → |D| ≤ d → |N| ≤ B →
      |t| ≤ T → |u| ≤ T → J < |L| →
      let P := frameVector n m (slopePure S D N L k t)
      let Q := frameVector n m (slopePure S D N L k u)
      0 < inner ℝ P Q ∧ ∃ w : E, inner ℝ n w = 0 ∧ 0 < inner ℝ P w ∧ 0 < inner ℝ Q w := by
  let J := 2*B*T+4*T*(d+sHi*T+B)+1
  have hJ : 0 < J := by dsimp [J]; positivity
  refine ⟨J,hJ,?_⟩
  intro n m hn hm hmn S D N L k t u hS hShi hD hN ht hu hL
  dsimp only
  let P := frameVector n m (slopePure S D N L k t)
  let Q := frameVector n m (slopePure S D N L k u)
  have hpn := longitudinal_norm_lower (S := S) (D := D) (N := N) (L := L) (k := k) hm hmn hB hN ht
  have hdiff := pure_difference_norm_bound (N := N) (L := L) (k := k) hn hm hS hShi hD ht hu
  have hdiff' : ‖Q-P‖ ≤ 4*T*(d+sHi*T+B) := hdiff.trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hN) (by positivity))
  have hnear : ‖Q-P‖ < ‖P‖ := by dsimp [J] at hL; linarith
  refine ⟨inner_pos_of_difference_lt_norm hnear,?_⟩
  have htm : inner ℝ P m = L+2*N*t := frameVector_inner_second hm hmn _
  have hum : inner ℝ Q m = L+2*N*u := frameVector_inner_second hm hmn _
  have htb := abs_le.mp (double_product_bound hB hN ht)
  have hub := abs_le.mp (double_product_bound hB hN hu)
  have hbig : 2*B*T < |L| := by
    dsimp [J] at hL
    have hh : 0 ≤ 4*T*(d+sHi*T+B) := by positivity
    linarith
  have hnm : inner ℝ n m = 0 := by rw [real_inner_comm]; exact hmn
  by_cases hL0 : 0 ≤ L
  · refine ⟨m,hnm,?_,?_⟩
    · change 0 < inner ℝ P m
      change inner ℝ P m = L+2*N*t at htm
      rw [abs_of_nonneg hL0] at hbig
      linarith
    · change 0 < inner ℝ Q m
      change inner ℝ Q m = L+2*N*u at hum
      rw [abs_of_nonneg hL0] at hbig
      linarith
  · refine ⟨-m,by simp [hnm],?_,?_⟩
    · change 0 < inner ℝ P (-m)
      change inner ℝ P m = L+2*N*t at htm
      rw [inner_neg_right]
      rw [abs_of_neg (lt_of_not_ge hL0)] at hbig
      linarith
    · change 0 < inner ℝ Q (-m)
      change inner ℝ Q m = L+2*N*u at hum
      rw [inner_neg_right]
      rw [abs_of_neg (lt_of_not_ge hL0)] at hbig
      linarith

end ClosedSurfaceR4.GeometryPreservation

end

end OAI

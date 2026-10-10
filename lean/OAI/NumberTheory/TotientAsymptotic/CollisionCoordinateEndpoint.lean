import OAI.NumberTheory.TotientAsymptotic.NormalFactorBands

namespace OAI

/-! The original prime coordinate differs from a dyadic endpoint by at most one. -/

noncomputable section

namespace TotientAsymptotic

lemma prime_coordinate_endpoint_bound {p : ℕ} {y : ℝ}
    (hp : 3 ≤ p) (hy : Real.exp 1 ≤ y) (hpy : (p-1 : ℕ) ≤ y) :
    B p ≤ B y+1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1<p)
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp1
  have hy1 : 1 ≤ Real.log y := by
    have he := Real.log_le_log (Real.exp_pos 1) hy
    simpa only [Real.log_exp] using he
  have hy0 : 0<y := (Real.exp_pos 1).trans_le hy
  have hyge1 : (1 : ℝ) ≤ y := by
    have he := Real.add_one_le_exp (1 : ℝ)
    linarith
  have he : (p : ℝ)=(p-1 : ℕ)+1 := by exact_mod_cast (Nat.sub_add_cancel (by omega : 1≤p)).symm
  have hp2y : (p : ℝ) ≤ 2*y := by rw [he]; linarith
  have hl := Real.log_le_log hp0 hp2y
  rw [Real.log_mul (by norm_num : (2 : ℝ)≠0) hy0.ne'] at hl
  have hl2 : Real.log (p : ℝ) ≤ 2*Real.log y := by
    have hc := Real.log_two_lt_d9
    linarith
  have hb := Real.log_le_log (Real.log_pos hp1) hl2
  rw [Real.log_mul (by norm_num : (2 : ℝ)≠0) (by linarith : Real.log y≠0)] at hb
  change B (p : ℝ)≤B y+1
  change Real.log (Real.log (p : ℝ))≤Real.log (Real.log y)+1
  linarith [Real.log_two_lt_d9]

lemma remainder_coordinate_endpoint_bound {x y : ℝ} {H i : ℕ}
    {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η)
    (hL : L x H < m x) (hi : i ∈ Finset.Icc 1 (L x H))
    (hy : Real.exp 1 ≤ y) (hpy : (remainderPrime η i-1 : ℕ) ≤ y) :
    remainderCoord x η i ≤ B y+1 := by
  have hi0 : i≠0 := by have := (Finset.mem_Icc.mp hi).1; omega
  simpa only [remainderCoord,ite_eq_right hi0,B] using
    prime_coordinate_endpoint_bound (basic_remainder_prime_ge_three hη hi ((Finset.mem_Icc.mp hi).2.trans_lt hL)) hy hpy

end TotientAsymptotic

end

end OAI

import OAI.NumberTheory.Ostmann.QuadraticCenter.InverseWeylEstimate

namespace OAI

namespace Ostmann.QuadraticCenter

theorem inverse_quadratic_weyl (alpha beta start : ℝ) (N : ℕ) (delta B : ℝ)
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hB : 1 ≤ B) (hBN : B ≤ (N+1:ℝ))
    (hscale : 256*(1+Real.log (N+1:ℝ)) ≤ delta^2*B)
    (hlarge : delta*(N+1:ℝ) ≤ ‖quadraticWeylSum alpha beta start (N+1)‖) :
    ∃ q : ℕ, 1 ≤ q ∧ (q:ℝ) ≤ 2*B ∧
      integerDistance ((q:ℝ)*alpha) ≤ B/(N+1:ℝ)^2 := by
  let M : ℝ := N+1
  let H : ℝ := 1+Real.log M
  have hM : 1 ≤ M := by dsimp [M]; linarith [Nat.cast_nonneg (α:=ℝ) N]
  have hMp : 0 < M := by linarith
  have hBp : 0 < B := hd.trans_le (hd1.trans hB)
  have hH : 0 < H := by
    dsimp [H]
    linarith [Real.log_nonneg hM]
  have hMsq : 0 < M^2 := sq_pos_of_pos hMp
  let Q : ℕ := ⌊M^2/B⌋₊
  have hQp : 0 < Q := by
    apply Nat.floor_pos.mpr
    apply (le_div_iff₀ hBp).mpr
    change B ≤ M at hBN
    nlinarith
  obtain ⟨a,ha,har⟩ := Real.exists_rat_abs_sub_le_and_den_le (2*alpha) hQp
  let r := a.den
  let b := a.num
  have hr : 0 < r := a.pos
  have hrp : (0:ℝ) < r := by exact_mod_cast hr
  have hrQ : r ≤ Q := har
  have hrQR : (r:ℝ) ≤ Q := by exact_mod_cast hrQ
  have hQle : (Q:ℝ) ≤ M^2/B := Nat.floor_le (by positivity)
  have hrB : (r:ℝ) ≤ M^2/B := hrQR.trans hQle
  have hrM : (r:ℝ) ≤ M^2 := hrB.trans (div_le_self (sq_nonneg M) hB)
  have hcop : Int.gcd (r:ℤ) b = 1 := Int.isCoprime_iff_gcd_eq_one.mp a.isCoprime_num_den.symm
  have ha' : |2*alpha-(b:ℝ)/r| ≤ 1/(((Q:ℝ)+1)*r) := by
    simpa only [Rat.cast_def] using ha
  have happ : |2*alpha-(b:ℝ)/r| ≤ 1/(r:ℝ)^2 := by
    apply ha'.trans
    apply one_div_le_one_div_of_le (sq_pos_of_pos hrp)
    nlinarith
  have hweyl := quadratic_weyl_rational_bound alpha beta start N b r hr hcop happ hrM
  have hrsmall : (r:ℝ) ≤ B := by
    by_contra! hrlarge
    have hmB : M ≤ M^2/B := (le_div_iff₀ hBp).mpr (by
      change B ≤ M at hBN
      nlinarith)
    have hrat : M^2/(r:ℝ) ≤ M^2/B :=
      div_le_div_of_nonneg_left (sq_nonneg M) hBp hrlarge.le
    have htotal : M^2/(r:ℝ)+M+r ≤ 3*(M^2/B) := by linarith
    have hupper : ‖quadraticWeylSum alpha beta start (N+1)‖^2 ≤ 96*H*M^2/B := by
      change _ ≤ 32*H*(M^2/r+M+r) at hweyl
      have hm := mul_le_mul_of_nonneg_left htotal (show 0 ≤ 32*H by positivity)
      calc
        _ ≤ 32*H*(M^2/r+M+r) := hweyl
        _ ≤ 32*H*(3*(M^2/B)) := hm
        _ = _ := by ring
    have hlower : delta^2*M^2 ≤ ‖quadraticWeylSum alpha beta start (N+1)‖^2 := by
      have := pow_le_pow_left₀ (mul_pos hd hMp).le hlarge 2
      simpa only [mul_pow] using this
    have hmul := (le_div_iff₀ hBp).mp (hlower.trans hupper)
    have hcancel : delta^2*B ≤ 96*H := (mul_le_mul_iff_right₀ hMsq).mp (by
      nlinarith only [hmul])
    change 256*H ≤ delta^2*B at hscale
    linarith
  have herr : |(r:ℝ)*(2*alpha)-(b:ℝ)| ≤ B/M^2 := by
    have hmul := mul_le_mul_of_nonneg_left ha' hrp.le
    have heleft : (r:ℝ)*|2*alpha-(b:ℝ)/r| = |(r:ℝ)*(2*alpha)-(b:ℝ)| := by
      calc
        _ = |(r:ℝ)*(2*alpha-(b:ℝ)/r)| := by rw [abs_mul,abs_of_pos hrp]
        _ = _ := by congr 1; field_simp
    rw [heleft] at hmul
    have heright : (r:ℝ)*(1/(((Q:ℝ)+1)*r)) = 1/((Q:ℝ)+1) := by field_simp
    rw [heright] at hmul
    have hQlt : M^2/B < (Q:ℝ)+1 := Nat.lt_floor_add_one _
    have hrecip : 1/((Q:ℝ)+1) ≤ B/M^2 := by
      apply (div_le_div_iff₀ (by positivity) hMsq).mpr
      have hh := (div_lt_iff₀ hBp).mp hQlt
      nlinarith
    exact hmul.trans hrecip
  refine ⟨2*r, by omega, ?_, ?_⟩
  · push_cast
    linarith
  · have hdist := integerDistance_le (((2*r:ℕ):ℝ)*alpha) b
    apply hdist.trans
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc, mul_left_comm] using herr

end Ostmann.QuadraticCenter

end OAI

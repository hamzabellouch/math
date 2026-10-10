import OAI.Probability.SignedSweeps.OccupiedSweep

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Topology
open Filter

def sweepColors (d : ℕ) : ℕ := ⌈((2^d : ℕ) : ℝ)^((1:ℝ)/64)⌉₊

lemma sweepColors_pos (d : ℕ) : 0 < sweepColors d := by
  apply Nat.ceil_pos.mpr
  positivity

lemma sweepColors_le_size (d : ℕ) : sweepColors d ≤ 2^d := by
  apply Nat.ceil_le.mpr
  have hn : (1:ℝ) ≤ (2^d : ℕ) := by exact_mod_cast Nat.one_le_pow d 2 (by decide)
  simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hn (by norm_num : (1:ℝ)/64 ≤ 1)

lemma sweepColors_le_twice (d : ℕ) :
    (sweepColors d : ℝ) ≤ 2*((2^d : ℕ) : ℝ)^((1:ℝ)/64) := by
  have hn : (1:ℝ) ≤ (2^d : ℕ) := by exact_mod_cast Nat.one_le_pow d 2 (by decide)
  have h := Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (2^d : ℕ)) ((1:ℝ)/64))
  have h1 := Real.one_le_rpow hn (by norm_num : (0:ℝ) ≤ 1/64)
  dsimp [sweepColors]
  linarith

lemma two_pow_rpow (d : ℕ) (a : ℝ) :
    ((2^d : ℕ) : ℝ)^a = Real.exp ((d:ℝ)*Real.log 2*a) := by
  rw [Real.rpow_def_of_pos (by positivity : (0:ℝ) < (2^d : ℕ)), nat_two_pow_log]

lemma two_pow_le_depth_rpow {k d : ℕ} {a : ℝ} (h : (k:ℝ) ≤ (d:ℝ)*a) :
    ((2^k : ℕ) : ℝ) ≤ ((2^d : ℕ) : ℝ)^a := by
  rw [two_pow_rpow, ← Real.exp_log (by positivity : (0:ℝ) < (2^k : ℕ)), nat_two_pow_log]
  apply Real.exp_le_exp.mpr
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_right h (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))

lemma depth_rpow_le_two_pow {k d : ℕ} {a : ℝ} (h : (d:ℝ)*a ≤ (k:ℝ)) :
    ((2^d : ℕ) : ℝ)^a ≤ ((2^k : ℕ) : ℝ) := by
  rw [two_pow_rpow, ← Real.exp_log (by positivity : (0:ℝ) < (2^k : ℕ)), nat_two_pow_log]
  apply Real.exp_le_exp.mpr
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_right h (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))

lemma balanced_depth_sizes {d : ℕ} (hd : 10 ≤ d) :
    d/2+childDepth d=d ∧
    ((2^d:ℕ):ℝ)^((1:ℝ)/3) ≤ ((2^(d/2):ℕ):ℝ) ∧
    ((2^d:ℕ):ℝ)^((1:ℝ)/3) ≤ ((2^(childDepth d):ℕ):ℝ) ∧
    ((2^(d/2):ℕ):ℝ) ≤ ((2^d:ℕ):ℝ)^((3:ℝ)/5) ∧
    ((2^(childDepth d):ℕ):ℝ) ≤ ((2^d:ℕ):ℝ)^((3:ℝ)/5) := by
  have hb : d/2+childDepth d=d := by unfold childDepth; omega
  have h₁ : d ≤ 3*(d/2) := by omega
  have h₂ : d ≤ 3*childDepth d := by unfold childDepth; omega
  have h₃ : 5*(d/2) ≤ 3*d := by omega
  have h₄ : 5*childDepth d ≤ 3*d := by unfold childDepth; omega
  have h₁' : (d:ℝ) ≤ 3*(d/2 : ℕ) := by exact_mod_cast h₁
  have h₂' : (d:ℝ) ≤ 3*(childDepth d : ℕ) := by exact_mod_cast h₂
  have h₃' : 5*(d/2 : ℕ) ≤ 3*(d:ℝ) := by exact_mod_cast h₃
  have h₄' : 5*(childDepth d : ℕ) ≤ 3*(d:ℝ) := by exact_mod_cast h₄
  exact ⟨hb, depth_rpow_le_two_pow (by linarith), depth_rpow_le_two_pow (by linarith),
    two_pow_le_depth_rpow (by linarith), two_pow_le_depth_rpow (by linarith)⟩

lemma cast_nat_sqrt_le {t : ℕ} : (Nat.sqrt t : ℝ) ≤ Real.sqrt t := by
  apply (Real.le_sqrt (by positivity) (by positivity)).mpr
  have h := Nat.sqrt_le t
  exact_mod_cast (by simpa only [pow_two] using h)

lemma typedLineError_bound {d t : ℕ}
    (ht : (t:ℝ) ≤ ((2^d:ℕ):ℝ)^((3:ℝ)/5)) :
    typedLineError t (sweepColors d) (16*2^d) ≤
      160*((2^d:ℕ):ℝ)^((3:ℝ)/10)*Real.log ((16*2^d : ℕ):ℝ) := by
  let N : ℝ := (2^d : ℕ)
  let W : ℝ := N^((3:ℝ)/10)
  have hn : 1 ≤ N := by dsimp [N]; exact_mod_cast Nat.one_le_pow d 2 (by decide)
  have hn0 : 0 < N := lt_of_lt_of_le zero_lt_one hn
  have hW : 1 ≤ W := Real.one_le_rpow hn (by norm_num)
  have hsqr : (Nat.sqrt t:ℝ) ≤ W := by
    calc
      _ ≤ Real.sqrt t := cast_nat_sqrt_le
      _ ≤ Real.sqrt (N^((3:ℝ)/5)) := Real.sqrt_le_sqrt ht
      _ = W := by rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn0.le]; norm_num [W]
  have hq : (sweepColors d:ℝ) ≤ 2*W :=
    (sweepColors_le_twice d).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn (by norm_num : (1:ℝ)/64 ≤ 3/10)) (by norm_num))
  have hq2 : (sweepColors d:ℝ)^2 ≤ 4*W := by
    calc
      _ ≤ (2*N^((1:ℝ)/64))^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) (sweepColors_le_twice d) 2
      _ = 4*N^((1:ℝ)/32) := by rw [mul_pow, ← Real.rpow_natCast (N^((1:ℝ)/64)) 2, ← Real.rpow_mul hn0.le]; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn (by norm_num : (1:ℝ)/32 ≤ 3/10)) (by norm_num)
  have hlog : 1 ≤ Real.log ((16*2^d : ℕ):ℝ) := by
    have hN16 : (16:ℝ) ≤ (16*2^d : ℕ) := by rw [Nat.cast_mul, Nat.cast_ofNat]; change 16 ≤ 16*N; nlinarith
    have hl := Real.log_le_log (by norm_num : (0:ℝ) < 16) hN16
    have hl16 : Real.log 16 = 4*Real.log 2 := by
      rw [show (16:ℝ) = 2^4 by norm_num, Real.log_pow]; norm_num
    rw [hl16] at hl
    linarith [Real.log_two_gt_d9]
  have hA : 6*(Nat.sqrt t:ℝ)+28*(sweepColors d:ℝ)^2+8*sweepColors d+2 ≤ 136*W := by
    nlinarith
  have hB : 8*(sweepColors d:ℝ)+1 ≤ 17*W := by linarith
  have hC := mul_le_mul_of_nonneg_right hA (show 0 ≤ Real.log ((16*2^d : ℕ):ℝ) by linarith)
  have hD := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 17*W by positivity)
  dsimp [typedLineError, localTraceError]
  change _ ≤ 160*W*Real.log ((16*2^d : ℕ):ℝ)
  nlinarith

lemma log_size_radius (d : ℕ) :
    Real.log ((16*2^d : ℕ):ℝ) = Real.log 16+(d:ℝ)*Real.log 2 := by
  rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) (by positivity), nat_two_pow_log]

lemma depth_power_log_eventually {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∀ᶠ d : ℕ in atTop,
      C*((2^d:ℕ):ℝ)^a*Real.log ((16*2^d : ℕ):ℝ) ≤ ((2^d:ℕ):ℝ)^b/2 := by
  let c := (b-a)*Real.log 2
  have hc : 0 < c := mul_pos (sub_pos.mpr hab) (Real.log_pos (by norm_num))
  have ht₁ := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 c hc).comp
    tendsto_natCast_atTop_atTop).const_mul (C*Real.log 2)
  have ht₀ := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 c hc).comp
    tendsto_natCast_atTop_atTop).const_mul (C*Real.log 16)
  have ht : Tendsto (fun d : ℕ => C*Real.log ((16*2^d : ℕ):ℝ)*((2^d:ℕ):ℝ)^(a-b)) atTop (𝓝 0) := by
    convert ht₁.add ht₀ using 1
    · funext d
      rw [log_size_radius, two_pow_rpow]
      have he : (d:ℝ)*Real.log 2*(a-b) = -c*d := by dsimp [c]; ring
      rw [he]
      simp only [Function.comp_apply, Real.rpow_one, Real.rpow_zero, one_mul]
      ring
    · simp
  filter_upwards [ht.eventually_le_const (by norm_num : (0:ℝ) < 1/2)] with d hd
  have hh := mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (2^d:ℕ)) b)
  have he : ((2^d:ℕ):ℝ)^(a-b)*((2^d:ℕ):ℝ)^b = ((2^d:ℕ):ℝ)^a := by
    rw [← Real.rpow_add (by positivity : (0:ℝ) < (2^d:ℕ))]
    congr 1
    ring
  rw [mul_assoc, he] at hh
  nlinarith only [hh]

lemma balanced_clipping_error {d : ℕ} (hd : 10 ≤ d) {κ : ℝ} (hκ : 0 ≤ κ) :
    holeClippingError (κ/2) (2^(d/2)) (2^(childDepth d)) ≤
      2*((2^d:ℕ):ℝ)^(1-κ/6)*Real.log ((16*2^d:ℕ):ℝ) := by
  obtain ⟨hadd,hsa, hmb,hsu,hmu⟩ := balanced_depth_sizes hd
  let N : ℝ := (2^d : ℕ)
  let S : ℝ := (2^(d/2) : ℕ)
  let M : ℝ := (2^(childDepth d) : ℕ)
  have hN : 0 < N := by positivity
  have hS : 0 < S := by positivity
  have hM : 0 < M := by positivity
  have hSM : S*M=N := by dsimp [S,M,N]; rw [← Nat.cast_mul, ← Nat.pow_add, hadd]
  have hpow (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x*y=N) (hlo : N^((1:ℝ)/3) ≤ x) :
      y*x^(1-κ/2) ≤ N^(1-κ/6) := by
    have hh := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hN _) hlo
      (by linarith : -(κ/2) ≤ 0)
    rw [← Real.rpow_mul hN.le] at hh
    have he : (1:ℝ)/3*(-(κ/2)) = -(κ/6) := by ring
    rw [he] at hh
    calc
      _ = N*x^(-(κ/2)) := by
        rw [show 1-κ/2 = 1+(-(κ/2)) by ring, Real.rpow_add hx, Real.rpow_one]
        rw [← mul_assoc, mul_comm y x, hxy]
      _ ≤ N*N^(-(κ/6)) := mul_le_mul_of_nonneg_left hh hN.le
      _ = N^(1-κ/6) := by
        rw [show 1-κ/6=1+(-(κ/6)) by ring, Real.rpow_add hN, Real.rpow_one]
  have h₁ := hpow S M hS hM hSM hsa
  have h₂ := hpow M S hM hS (by rw [mul_comm]; exact hSM) hmb
  have hSlog : Real.log S ≤ Real.log ((16*2^d:ℕ):ℝ) := by
    apply Real.log_le_log hS
    have hSn : 2^(d/2) ≤ 2^d := Nat.pow_le_pow_right (by decide) (by omega)
    have hSn' : S ≤ N := by dsimp [S,N]; exact_mod_cast hSn
    rw [Nat.cast_mul, Nat.cast_ofNat]
    change S ≤ 16*N
    nlinarith
  have hMlog : Real.log M ≤ Real.log ((16*2^d:ℕ):ℝ) := by
    apply Real.log_le_log hM
    have hMn : 2^(childDepth d) ≤ 2^d := Nat.pow_le_pow_right (by decide) (by omega)
    have hMn' : M ≤ N := by dsimp [M,N]; exact_mod_cast hMn
    rw [Nat.cast_mul, Nat.cast_ofNat]
    change M ≤ 16*N
    nlinarith
  have hSz : 0 ≤ Real.log S := Real.log_nonneg (by dsimp [S]; exact_mod_cast Nat.one_le_pow (d/2) 2 (by decide))
  have hMz : 0 ≤ Real.log M := Real.log_nonneg (by dsimp [M]; exact_mod_cast Nat.one_le_pow (childDepth d) 2 (by decide))
  have hb₁ := mul_le_mul h₁ hSlog hSz (Real.rpow_nonneg hN.le _)
  have hb₂ := mul_le_mul h₂ hMlog hMz (Real.rpow_nonneg hN.le _)
  dsimp [holeClippingError]
  change M*S^(1-κ/2)*Real.log S+S*M^(1-κ/2)*Real.log M ≤ _
  linarith

theorem balanced_recurrence_error_eventually {κ ξ : ℝ} (hκ : 0 < κ)
    (hξ₁ : ξ < 1/10) (hξ₂ : ξ < κ/6) :
    ∃ D : ℕ, 10 ≤ D ∧ ∀ d ≥ D, ∀ (l : ℕ), l ≤ 2^d →
      ((2^(childDepth d):ℕ):ℝ)*typedLineError (2^(d/2)) (sweepColors d) (16*2^d)+
      ((2^(d/2):ℕ):ℝ)*typedLineError (2^(childDepth d)) (sweepColors d) (16*2^d)+
      holeClippingError (κ/2) (2^(d/2)) (2^(childDepth d))+
      (((2^(d/2):ℕ):ℝ)+((2^(childDepth d):ℕ):ℝ))*Real.log (l+1) ≤ ((2^d:ℕ):ℝ)^(1-ξ) := by
  have he₁ := depth_power_log_eventually (by linarith : (9:ℝ)/10 < 1-ξ) 322
  have he₂ := depth_power_log_eventually (by linarith : 1-κ/6 < 1-ξ) 2
  obtain ⟨D,hD⟩ := eventually_atTop.mp (he₁.and he₂)
  refine ⟨max D 10, le_max_right _ _, ?_⟩
  intro d hd l hl
  have hd10 : 10 ≤ d := (le_max_right _ _).trans hd
  obtain ⟨hadd,hsl,hml,hs,hm⟩ := balanced_depth_sizes hd10
  let N : ℝ := (2^d:ℕ)
  let L : ℝ := Real.log ((16*2^d:ℕ):ℝ)
  have hN : 1 ≤ N := by dsimp [N]; exact_mod_cast Nat.one_le_pow d 2 (by decide)
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hL : 0 ≤ L := Real.log_nonneg (by rw [Nat.cast_mul, Nat.cast_ofNat]; change 1 ≤ 16*N; nlinarith [hN])
  have hterms (t m : ℕ) (ht : (t:ℝ) ≤ N^((3:ℝ)/5)) (hm : (m:ℝ) ≤ N^((3:ℝ)/5)) :
      (m:ℝ)*typedLineError t (sweepColors d) (16*2^d) ≤ 160*N^((9:ℝ)/10)*L := by
    calc
      _ ≤ (m:ℝ)*(160*N^((3:ℝ)/10)*L) :=
        mul_le_mul_of_nonneg_left (typedLineError_bound ht) (Nat.cast_nonneg m)
      _ ≤ N^((3:ℝ)/5)*(160*N^((3:ℝ)/10)*L) :=
        mul_le_mul_of_nonneg_right hm (by positivity)
      _ = _ := by
        rw [show N^((3:ℝ)/5)*(160*N^((3:ℝ)/10)*L) =
          160*(N^((3:ℝ)/5)*N^((3:ℝ)/10))*L by ring, ← Real.rpow_add hN0]
        norm_num
  have hH := hterms (2^(d/2)) (2^(childDepth d)) hs hm
  have hK := hterms (2^(childDepth d)) (2^(d/2)) hm hs
  have hlog : Real.log ((l:ℝ)+1) ≤ L := by
    apply Real.log_le_log (by positivity)
    have hl' : (l:ℝ) ≤ N := by dsimp [N]; exact_mod_cast hl
    rw [Nat.cast_mul, Nat.cast_ofNat]
    change (l:ℝ)+1 ≤ 16*N
    nlinarith
  have hsum : ((2^(d/2):ℕ):ℝ)+((2^(childDepth d):ℕ):ℝ) ≤ 2*N^((9:ℝ)/10) := by
    have hb := Real.rpow_le_rpow_of_exponent_le hN (by norm_num : (3:ℝ)/5 ≤ 9/10)
    linarith
  have hhist := mul_le_mul hsum hlog (Real.log_nonneg (by linarith [show (0:ℝ) ≤ l by positivity] : (1:ℝ) ≤ (l:ℝ)+1))
    (by positivity : 0 ≤ 2*N^((9:ℝ)/10))
  have hclip := balanced_clipping_error hd10 hκ.le
  obtain ⟨he₁,he₂⟩ := hD d ((le_max_left _ _).trans hd)
  change _ ≤ N^(1-ξ)
  change _ ≤ 2*N^(1-κ/6)*L at hclip
  change 322*N^((9:ℝ)/10)*L ≤ N^(1-ξ)/2 at he₁
  change 2*N^(1-κ/6)*L ≤ N^(1-ξ)/2 at he₂
  linarith

end SignedSweeps
end

end OAI

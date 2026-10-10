import OAI.Computability.SpaceSimulation.OneTape.Sizes

namespace OAI

namespace Fifths.Cost

noncomputable def Log (T : ℕ) := Real.log (T+2 : ℝ) / Real.log 2
noncomputable def exponent := (2:ℝ)/5

private theorem logpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
theorem one_le (T : ℕ) : 1 ≤ Log T := by
  unfold Log
  apply (le_div_iff₀ logpos).mpr
  rw [one_mul]
  apply Real.log_le_log (by norm_num)
  have : (0:ℝ) ≤ T := by positivity
  linarith

private theorem smallPow {T : ℕ} (h : T ≥ 2) :
    2^(T.size-1) ≤ T ∧ 1 ≤ T.size := by
  have b := Nat.size_pos.mpr (show 0<T by omega)
  exact ⟨Nat.lt_size.mp (by omega), b⟩

theorem lg_real {T : ℕ} (h : T ≥ 2) : (lg T:ℝ) ≤ 3 * Log T := by
  obtain ⟨p,l⟩ := smallPow h
  have q : ((T.size-1:ℕ) : ℝ) ≤ Log T := by
    unfold Log
    apply (le_div_iff₀ logpos).mpr
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact le_trans (by exact_mod_cast p) (show (T:ℝ) ≤ T+2 by linarith)
  have k := one_le T
  rw [Nat.cast_sub l,Nat.cast_one] at q
  unfold lg; push_cast
  linarith

theorem log_integer (T : ℕ) : Log T ≤ lg T := by
  have p : T+2 ≤ 2^lg T := by
    have h := Nat.lt_size_self T
    unfold lg; rw [pow_succ]; omega
  unfold Log
  apply (div_le_iff₀ logpos).mpr
  rw [← Real.log_pow]
  exact Real.log_le_log (by positivity) (by exact_mod_cast p)

theorem log_shift (T : ℕ) : Log (T+2) ≤ 2 * Log T := by
  unfold Log
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ logpos.le
  have w : (↑(T+2:ℕ):ℝ)+2 ≤ ((T:ℝ)+2)^2 := by
    push_cast
    have : (0:ℝ) ≤ T := by positivity
    nlinarith
  have g := Real.log_le_log (by positivity) w
  simpa only [Real.log_pow,Nat.cast_ofNat] using g

theorem k_fifth {T : ℕ} (h : T ≥ 2) : K T ^ 5 ≤ 32*T := by
  obtain ⟨p,l⟩ := smallPow h
  unfold K; rw [← pow_mul]
  calc
    _ ≤ 2^(T.size+4) := Nat.pow_le_pow_right (by omega) (by unfold power; omega)
    _ = 32*2^(T.size-1) := by
      nth_rw 1 [show T.size+4 = 5+(T.size-1) by omega]
      rw [pow_add]; norm_num
    _ ≤ 32*T := Nat.mul_le_mul_left 32 p

theorem k_real {T : ℕ} (h : T ≥ 2) : (K T:ℝ)*(K T:ℝ) ≤ 32*(T:ℝ)^exponent := by
  have p : (K T:ℝ)^5 ≤ 32*(T:ℝ) := by exact_mod_cast k_fifth h
  have a : (0:ℝ) ≤ T := by positivity
  have g : ((T:ℝ)^exponent)^(5:ℕ) = (T:ℝ)^(2:ℕ) := by
    rw [← Real.rpow_mul_natCast a]
    rw [show exponent * (↑(5:ℕ):ℝ) = ((2:ℕ):ℝ) by unfold exponent; norm_num,
      Real.rpow_natCast]
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity)
    (show (5:ℕ)≠0 by decide)).mp
  rw [mul_pow,mul_pow,g]
  calc
    _ ≤ (32*(T:ℝ))*(32*(T:ℝ)) := mul_le_mul p p (by positivity) (by positivity)
    _ ≤ _ := by nlinarith

noncomputable def factor (d : ℕ) : ℝ := 32 * 3^(d+2)
theorem fpos (d : ℕ) : 0 < factor d := by unfold factor; positivity
theorem realBound (d : ℕ) {T : ℕ} (h : T≥2) :
    (bound d T:ℝ) ≤ factor d * (T:ℝ)^exponent * (Log T)^(d+2) := by
  have p := k_real h
  have q := lg_real h
  have b := one_le T
  unfold bound
  push_cast
  calc
    _ ≤ (32 * (T:ℝ)^exponent) * (3*Log T)^(d+2) :=
      mul_le_mul p (pow_le_pow_left₀ (by positivity) q _) (by positivity) (by positivity)
    _ = _ := by rw [mul_pow]; unfold factor; ring

-- The `+1` in a scaled natural bound. State concrete
-- constants. These formulas will be used pointwise.
theorem scaledReal (d u : ℕ) {T : ℕ} (h : T≥2) :
    ((u*(bound d T+1):ℕ) : ℝ) ≤
      (((u:ℝ)+1)*2*factor d) * (T:ℝ)^exponent * (Log T)^(d+2) := by
  have g := realBound d h
  have f : (1:ℝ) ≤ bound d T := by exact_mod_cast bound_pos d T
  have p := one_le T
  push_cast
  calc
    _ ≤ ((u:ℝ)+1)*(2*(bound d T:ℝ)) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    _ ≤ ((u:ℝ)+1)*(2*(factor d * (T:ℝ)^exponent * (Log T)^(d+2))) := by gcongr
    _ = _ := by ring

theorem scaledShift (d u T : ℕ) :
    ((u*(bound d (T+2)+1):ℕ) : ℝ) ≤
      (((u:ℝ)+1)*2*factor d*2^(d+2)) * ((T:ℝ)+2)^exponent * (Log T)^(d+2) := by
  have g := scaledReal d u (show T+2 ≥ 2 by omega)
  apply g.trans
  have p := fpos d
  have h := one_le (T+2)
  push_cast
  calc
    _ ≤ ((u+1 : ℝ)*2*factor d) * ((T:ℝ)+2)^exponent * (2*Log T)^(d+2) := by
      gcongr
      · exact log_shift T
    _ = _ := by rw [mul_pow]; ring

/-- Absorb a prescribed polylog with real leading constant and
real exponent. -/
theorem absorbs (p q : ℝ) (_h : 1 ≤ p) :
    ∃ d c : ℕ, ∀ T : ℕ,
      p * Log T ^ q ≤ ((c*(bound d T + 1):ℕ):ℝ) := by
  obtain ⟨d,v⟩ := exists_nat_gt q
  obtain ⟨c,u⟩ := exists_nat_gt p
  refine ⟨d,c,?_⟩
  intro T
  have j := one_le T
  have l : Log T ^ q ≤ ((bound d T:ℕ) : ℝ) := calc
    _ ≤ Log T ^ (d:ℝ) := Real.rpow_le_rpow_of_exponent_le j v.le
    _ = Log T ^ d := Real.rpow_natCast ..
    _ ≤ (lg T:ℝ)^d := pow_le_pow_left₀ (by linarith) (log_integer T) _
    _ ≤ (bound d T:ℝ) := by exact_mod_cast lg_pow_le d T
  push_cast
  exact mul_le_mul u.le (by linarith) (Real.rpow_nonneg (by linarith) _) (by positivity)

end Fifths.Cost

end OAI

import OAI.NumberTheory.TwoPoint.Halasz.HalaszScaleFactor

namespace OAI

/-! A natural modulus scale just above the k-th root, with the exact
division endpoint controlled for the classical recurrence. -/
namespace TwoPointCorrelations

noncomputable def halaszRootScale (N k : ℕ) : ℕ := ⌊(N:ℝ)^(1/(k:ℝ))⌋₊+1

lemma halasz_root_scale_pos (N k : ℕ) : 0<halaszRootScale N k := by
  unfold halaszRootScale
  omega

lemma halasz_root_scale_lt {N k : ℕ} (hk : 0<k) : N<(halaszRootScale N k)^k := by
  have hroot : 0≤(N:ℝ)^(1/(k:ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hlt : (N:ℝ)^(1/(k:ℝ))<(halaszRootScale N k:ℝ) := by
    simpa only [halaszRootScale,Nat.cast_add,Nat.cast_one] using
      Nat.lt_floor_add_one ((N:ℝ)^(1/(k:ℝ)))
  have hp := pow_lt_pow_left₀ hlt hroot hk.ne'
  have he : ((N:ℝ)^(1/(k:ℝ)))^k=(N:ℝ) := by
    simpa only [one_div] using Real.rpow_inv_natCast_pow (Nat.cast_nonneg N) hk.ne'
  rw [he] at hp
  exact_mod_cast hp

lemma halasz_root_scale_upper {N k : ℕ} (hN : 1≤N) :
    (halaszRootScale N k:ℝ)≤2*(N:ℝ)^(1/(k:ℝ)) := by
  have hroot : 1≤(N:ℝ)^(1/(k:ℝ)) := Real.one_le_rpow
    (by exact_mod_cast hN) (by positivity)
  have hf := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) (1/(k:ℝ)))
  simp only [halaszRootScale,Nat.cast_add,Nat.cast_one]
  linarith

lemma halasz_root_scale_large {N k T : ℕ} (hk : 0<k) (hT : T^k≤N) :
    T<halaszRootScale N k := by
  by_contra! h
  have hpow := Nat.pow_le_pow_left h k
  have hstrict := halasz_root_scale_lt (N := N) hk
  omega

lemma halasz_root_scale_le_endpoint {N k : ℕ} (hk : 2≤k) (hN : 2^k≤N) :
    halaszRootScale N k≤N := by
  let x := (N:ℝ)^(1/(k:ℝ))
  have hk0 : k≠0 := by omega
  have hx0 : 0≤x := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hxk : x^k=(N:ℝ) := by
    simpa only [x,one_div] using Real.rpow_inv_natCast_pow (Nat.cast_nonneg N) hk0
  have hx2 : (2:ℝ)≤x := by
    by_contra! h
    have hh := pow_lt_pow_left₀ h hx0 hk0
    have hN' : (2:ℝ)^k≤(N:ℝ) := by exact_mod_cast hN
    rw [hxk] at hh
    linarith
  have hsquare : x^2≤x^k := pow_le_pow_right₀ (by linarith : 1≤x) hk
  have hfloor := Nat.floor_le hx0
  have hreal : (halaszRootScale N k:ℝ)≤(N:ℝ) := by
    simp only [halaszRootScale,Nat.cast_add,Nat.cast_one]
    change (⌊x⌋₊:ℝ)+1≤(N:ℝ)
    rw [hxk] at hsquare
    nlinarith
  exact_mod_cast hreal

lemma halasz_division_endpoint {N R : ℕ} (hR : 0<R) (hRN : R≤N) :
    ((N/R+1:ℕ):ℝ)≤2*(N:ℝ)/(R:ℝ) := by
  have hr : (0:ℝ)<R := by exact_mod_cast hR
  have hone : (1:ℝ)≤(N:ℝ)/(R:ℝ) :=
    (le_div_iff₀ hr).mpr (by simpa only [one_mul] using
      (show (R:ℝ)≤N by exact_mod_cast hRN))
  have hd : ((N/R:ℕ):ℝ)≤(N:ℝ)/(R:ℝ) := Nat.cast_div_le
  push_cast
  rw [show 2*(N:ℝ)/(R:ℝ)=2*((N:ℝ)/(R:ℝ)) by ring]
  linarith

end TwoPointCorrelations

end OAI

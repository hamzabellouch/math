import OAI.Probability.ThorpShuffle.FiniteLaw

namespace OAI

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

theorem exists_mixing_time_succ (d : ℕ) : ∃ t : ℕ, distance (d + 1) t ≤ 1 / 4 := by
  classical
  obtain ⟨T, hT⟩ := Reachability.exists_surjective_run d
  let c : ℝ := 1 / Fintype.card (History (d + 1) T)
  let r : ℝ := 1 - (Fintype.card (State (d + 1)) : ℝ) * c
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hminor (g : State (d + 1)) : c ≤ law (d + 1) T g :=
    FiniteLaw.fairMass_lower_of_surjective _ hT g
  have hr : 0 ≤ r := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun g _ => hminor g)
    simp only [law, fairMass_sum] at hh
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using sub_nonneg.mpr hh
  have hrlt : r < 1 := by
    dsimp [r]
    have hn : (0 : ℝ) < Fintype.card (State (d + 1)) := by positivity
    nlinarith
  have hcontract (s : ℕ) : distance (d + 1) (s + T) ≤ r * distance (d + 1) s := by
    unfold distance uniform
    rw [law_add]
    exact FiniteLaw.tv_conv_contract _ _ (fairMass_sum _) (fairMass_sum _) c hminor
  have hgeom (n : ℕ) : distance (d + 1) (n * T) ≤ r ^ n * distance (d + 1) 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.succ_mul]
      calc
        _ ≤ r * distance (d + 1) (n * T) := hcontract _
        _ ≤ r * (r ^ n * distance (d + 1) 0) := mul_le_mul_of_nonneg_left ih hr
        _ = _ := by rw [pow_succ']; ring
  have hlim : Tendsto (fun n : ℕ => r ^ n * distance (d + 1) 0) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr hrlt).mul_const (distance (d + 1) 0)
  have hev : ∀ᶠ n : ℕ in atTop, r ^ n * distance (d + 1) 0 < 1 / 4 :=
    hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  obtain ⟨n, hn⟩ := hev.exists
  exact ⟨n * T, (hgeom n).trans hn.le⟩

theorem exists_mixing_time {d : ℕ} (hd : 1 ≤ d) : ∃ t : ℕ, distance d t ≤ 1 / 4 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  exact exists_mixing_time_succ k

theorem exact_support_lower {d : ℕ} (hd : 1 ≤ d) :
    supportThreshold d ≤ (mixingTime d : ℤ) :=
  supportThreshold_le_mixingTime hd (exists_mixing_time hd)

theorem log_factorial_lower (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial : ℝ) := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hh := Real.pow_div_factorial_le_exp (n : ℝ) hpos.le n
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ) ^ n / (n.factorial : ℝ)) hh
  rw [Real.log_exp, Real.log_div (by positivity) hf.ne', Real.log_pow] at hlog
  linarith

theorem supportThreshold_bounds (d : ℕ) :
    2 * (d : ℝ) - 6 ≤ (supportThreshold d : ℝ) ∧
      (supportThreshold d : ℝ) ≤ 2 * (d : ℝ) := by
  let n : ℕ := 2 ^ d
  have hn : 0 < n := by dsimp [n]; positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hfact : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hl2pos : 0 < Real.log 2 := by linarith
  have hlfrac : -(1 / 3 : ℝ) ≤ Real.log (3 / 4 : ℝ) := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3 / 4)
    norm_num at hh ⊢
    exact hh
  have hlogn : Real.log (n : ℝ) = (d : ℝ) * Real.log 2 := by
    simp only [n, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have hlow := log_factorial_lower n hn
  have hupp : Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n := by
    have hh : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    simpa only [Real.log_pow] using Real.log_le_log hfact hh
  have hprod : Real.log (3 * (n.factorial : ℝ) / 4) =
      Real.log (3 / 4 : ℝ) + Real.log (n.factorial : ℝ) := by
    rw [show 3 * (n.factorial : ℝ) / 4 = (3 / 4) * n.factorial by ring]
    exact Real.log_mul (by norm_num) hfact.ne'
  have hlowlog : (n : ℝ) * ((d : ℝ) * Real.log 2) - n - 1 / 3 ≤
      Real.log (3 * (n.factorial : ℝ) / 4) := by
    rw [hprod, ← hlogn]
    linarith
  have hupplog : Real.log (3 * (n.factorial : ℝ) / 4) ≤
      (n : ℝ) * ((d : ℝ) * Real.log 2) := by
    rw [hprod, ← hlogn]
    have hh : Real.log (3 / 4 : ℝ) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
    linarith
  let a : ℝ := (2 / (n : ℝ)) * Real.logb 2 (3 * (n.factorial : ℝ) / 4)
  have ha_low : 2 * (d : ℝ) - 6 ≤ a := by
    dsimp [a]
    rw [Real.logb]
    have he : (2 / (n : ℝ)) *
        (Real.log (3 * (n.factorial : ℝ) / 4) / Real.log 2) =
        (2 * Real.log (3 * (n.factorial : ℝ) / 4)) / ((n : ℝ) * Real.log 2) := by ring
    rw [he]
    apply (le_div_iff₀ (mul_pos hnR hl2pos)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hl2 (by positivity : (0 : ℝ) ≤ n)]
  have ha_upp : a ≤ 2 * (d : ℝ) := by
    dsimp [a]
    rw [Real.logb]
    have hscale := mul_le_mul_of_nonneg_left hupplog (by positivity : (0 : ℝ) ≤ 2 / n / Real.log 2)
    have hid : (2 / (n : ℝ) / Real.log 2) * ((n : ℝ) * ((d : ℝ) * Real.log 2)) = 2 * d := by
      field_simp
    rw [hid] at hscale
    calc
      _ = (2 / (n : ℝ) / Real.log 2) * Real.log (3 * (n.factorial : ℝ) / 4) := by ring
      _ ≤ 2 * (d : ℝ) := hscale
  have hceil : supportThreshold d = ⌈a⌉ := by
    simp only [supportThreshold, a, n, Nat.cast_pow, Nat.cast_ofNat]
  rw [hceil]
  constructor
  · exact ha_low.trans (Int.le_ceil a)
  · have hh : ⌈a⌉ ≤ (2 * d : ℤ) := Int.ceil_le.mpr (by exact_mod_cast ha_upp)
    exact_mod_cast hh

theorem supportThreshold_isBigO :
    Asymptotics.IsBigO atTop
      (fun d : ℕ => (supportThreshold d : ℝ) - 2 * (d : ℝ)) (fun _ => (1 : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨6, Filter.Eventually.of_forall (fun d => ?_)⟩
  have h := supportThreshold_bounds d
  simp only [Real.norm_eq_abs, norm_one, mul_one]
  apply abs_le.mpr
  constructor <;> linarith

theorem orderFunction_isBigO_mixingTime :
    Asymptotics.IsBigO atTop orderFunction (fun d : ℕ => (mixingTime d : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, Filter.eventually_atTop.2 ⟨6, fun d hd => ?_⟩⟩
  have hs := (supportThreshold_bounds d).1
  have hl : (supportThreshold d : ℝ) ≤ mixingTime d := by
    exact_mod_cast exact_support_lower (by omega : 1 ≤ d)
  have hdR : (6 : ℝ) ≤ d := by exact_mod_cast hd
  simp only [orderFunction, Real.norm_eq_abs, one_mul]
  rw [abs_of_nonneg (Nat.cast_nonneg d), abs_of_nonneg (Nat.cast_nonneg (mixingTime d))]
  linarith

end Thorp

end

end OAI

import OAI.Probability.RandomSAT.Convergence

namespace OAI

/-!
For every fixed clause size at least three, the proper-clause satisfiability
probability has a positive finite limiting threshold. No conclusion is asserted
at the critical density.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def limitingCenter (k : ℕ) : ℝ := Filter.limsup (fun n : ℕ => center n k) Filter.atTop

theorem center_tendsto (k : ℕ) (hk : 3 ≤ k) :
    Filter.Tendsto (fun n : ℕ => center n k) Filter.atTop (nhds (limitingCenter k)) := by
  have hb := center_bounds_eventually k hk
  have hUpper : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (fun n : ℕ => center n k) :=
    Filter.isBoundedUnder_of_eventually_le (hb.mono (fun _ h => h.2))
  have hLower : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop (fun n : ℕ => center n k) :=
    Filter.isBoundedUnder_of_eventually_ge (hb.mono (fun _ h => h.1))
  apply summable_min_convergence (fun n => center n k) (by norm_num : (0 : ℝ) ≤ 4)
    (delta_pos hk) hUpper hLower
  obtain ⟨N, hadd, hnext⟩ := center_comparisons k hk
  refine ⟨N, ?_, ?_⟩
  · intro r hr s hs
    simpa only [densityWindow, Nat.cast_min] using hadd r hr s hs
  · intro s hs
    exact hnext s hs

theorem limitingCenter_bounds (k : ℕ) (hk : 3 ≤ k) :
    lowerCenterBound ≤ limitingCenter k ∧ limitingCenter k ≤ (2 : ℝ)^k + 1 := by
  have ht := center_tendsto k hk
  have hb := center_bounds_eventually k hk
  exact ⟨ge_of_tendsto ht (hb.mono (fun _ h => h.1)), le_of_tendsto ht (hb.mono (fun _ h => h.2))⟩

theorem limitingCenter_pos (k : ℕ) (hk : 3 ≤ k) : 0 < limitingCenter k :=
  lowerCenterBound_pos.trans_le (limitingCenter_bounds k hk).1

theorem limitingCenter_lt_cap (k : ℕ) (hk : 3 ≤ k) : limitingCenter k < capMultiplier k := by
  have hp : (1 : ℝ) < 2^k := one_lt_pow₀ (by norm_num) (by omega : k ≠ 0)
  have he : (capMultiplier k : ℝ) = 2^k * 2 := by simp [capMultiplier, pow_succ]
  rw [he]
  have h := (limitingCenter_bounds k hk).2
  linarith

theorem floor_density_le_cap {n k : ℕ} {c : ℝ} (hc0 : 0 ≤ c) (hcL : c ≤ capMultiplier k) :
    ⌊c * (n : ℝ)⌋₊ ≤ mainCap n k := by
  have h := (Nat.floor_le (mul_nonneg hc0 (Nat.cast_nonneg n : (0 : ℝ) ≤ n))).trans
    (mul_le_mul_of_nonneg_right hcL (Nat.cast_nonneg n : (0 : ℝ) ≤ n))
  exact_mod_cast (show (⌊c * (n : ℝ)⌋₊ : ℝ) ≤ (mainCap n k : ℝ) by
    simpa only [mainCap, Nat.cast_mul] using h)

theorem subcritical_limit (k : ℕ) (hk : 3 ≤ k) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : c < limitingCenter k) :
    Filter.Tendsto (fun n : ℕ => properSATProbability n k ⌊c * (n : ℝ)⌋₊)
      Filter.atTop (nhds 1) := by
  have hcL : c ≤ capMultiplier k := (hc.trans (limitingCenter_lt_cap k hk)).le
  have hcenter : Filter.Tendsto (fun n : ℕ => center n k - densityWindow n k)
      Filter.atTop (nhds (limitingCenter k)) := by
    simpa only [sub_zero] using (center_tendsto k hk).sub (densityWindow_tendsto k hk)
  have hmargin := hcenter.eventually (Ioi_mem_nhds hc)
  have hlower : ∀ᶠ n : ℕ in Filter.atTop,
      1 - concentrationError n k ≤ properSATProbability n k ⌊c * (n : ℝ)⌋₊ := by
    filter_upwards [hmargin, Filter.eventually_ge_atTop (k + 1)] with n hmargin hn
    apply properSATProbability_center_lower hk hn (floor_density_le_cap hc0 hcL)
    have hn0 : 0 < n := by omega
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [fluctuationWindow_eq_mul hn0]
    have hmul := mul_le_mul_of_nonneg_left hmargin.le hn'.le
    have hf := Nat.floor_le (mul_nonneg hc0 hn'.le)
    nlinarith
  have hlowT : Filter.Tendsto (fun n : ℕ => 1 - concentrationError n k) Filter.atTop (nhds 1) := by
    simpa only [sub_zero] using (concentrationError_tendsto k hk).const_sub 1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowT tendsto_const_nhds hlower
    (Filter.Eventually.of_forall fun n => properSATProbability_le_one n k _)

theorem supercritical_limit_below_cap (k : ℕ) (hk : 3 ≤ k) (c : ℝ)
    (hc : limitingCenter k < c) (hcL : c ≤ capMultiplier k) :
    Filter.Tendsto (fun n : ℕ => properSATProbability n k ⌊c * (n : ℝ)⌋₊)
      Filter.atTop (nhds 0) := by
  have hc0 : 0 ≤ c := ((limitingCenter_pos k hk).trans hc).le
  have hd : Filter.Tendsto (fun n : ℕ => 2 * densityWindow n k) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using (densityWindow_tendsto k hk).const_mul (2 : ℝ)
  have hcenter : Filter.Tendsto (fun n : ℕ => center n k + 2 * densityWindow n k)
      Filter.atTop (nhds (limitingCenter k)) := by
    simpa only [add_zero] using (center_tendsto k hk).add hd
  have hmargin := hcenter.eventually_lt_const hc
  have hupper : ∀ᶠ n : ℕ in Filter.atTop,
      properSATProbability n k ⌊c * (n : ℝ)⌋₊ ≤ concentrationError n k := by
    filter_upwards [hmargin, Filter.eventually_ge_atTop (k + 1)] with n hmargin hn
    apply properSATProbability_center_upper hk hn (floor_density_le_cap hc0 hcL)
    have hn0 : 0 < n := by omega
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hw := fluctuationWindow_one_le (n := n) hk hn0
    have he := fluctuationWindow_eq_mul (k := k) hn0
    have hmul := mul_le_mul_of_nonneg_left hmargin.le hn'.le
    have hf := Nat.lt_floor_add_one (c * (n : ℝ))
    nlinarith
  exact squeeze_zero' (Filter.Eventually.of_forall fun n => properSATProbability_nonneg n k _)
    hupper (concentrationError_tendsto k hk)

theorem supercritical_limit (k : ℕ) (hk : 3 ≤ k) (c : ℝ)
    (hc : limitingCenter k < c) :
    Filter.Tendsto (fun n : ℕ => properSATProbability n k ⌊c * (n : ℝ)⌋₊)
      Filter.atTop (nhds 0) := by
  let d := min c (capMultiplier k : ℝ)
  have hd : limitingCenter k < d := lt_min hc (limitingCenter_lt_cap k hk)
  have hdL : d ≤ capMultiplier k := min_le_right _ _
  have ht := supercritical_limit_below_cap k hk d hd hdL
  apply squeeze_zero' (Filter.Eventually.of_forall fun n => properSATProbability_nonneg n k _) _ ht
  filter_upwards [Filter.eventually_ge_atTop k] with n hn
  apply properSATProbability_antitone hn
  exact Nat.floor_mono (mul_le_mul_of_nonneg_right (min_le_left c (capMultiplier k : ℝ)) (Nat.cast_nonneg n))

theorem main (k : ℕ) (hk : 3 ≤ k) : HasLimitingThreshold k := by
  refine ⟨limitingCenter k, limitingCenter_pos k hk, ?_, ?_⟩
  · intro c hc0 hc
    exact subcritical_limit k hk c hc0 hc
  · intro c hc
    exact supercritical_limit k hk c hc

end


end FixedClauseThreshold

end OAI

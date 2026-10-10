import OAI.Probability.RandomSAT.Transfer

namespace OAI

/-!
Partition interpolation and concentration yield summable-error comparisons
for centers of two blocks and of neighboring sizes.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem auxiliary_interpolation_center_lower {r s k m : ℕ} (hk : 3 ≤ k)
    (hr : k + 1 ≤ r) (hs : k + 1 ≤ s)
    (hrrep : 2 * repeatPairs k ≤ r) (hsrep : 2 * repeatPairs k ≤ s)
    (hrerr : concentrationError r k ≤ 1 / 2) (hserr : concentrationError s k ≤ 1 / 2)
    (hm : (m : ℝ) ≤ (capMultiplier k : ℝ) * ((r : ℝ) + s))
    (hgapr : (m : ℝ) * ((r : ℝ) / (r + s)) + 2 * fluctuationWindow r k ≤ (r : ℝ) * center r k)
    (hgaps : (m : ℝ) * ((s : ℝ) / (r + s)) + 2 * fluctuationWindow s k ≤ (s : ℝ) * center s k) :
    (transferLower k)^2 * (1 - samplingError r k - samplingError s k) ≤
      auxiliaryProbability (r + s) k m := by
  have hr0 : 0 < r := by omega
  have hs0 : 0 < s := by omega
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr0
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs0
  let p : ℝ := (r : ℝ) / (r + s)
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by
    dsimp [p]
    apply (div_le_one (by positivity : (0 : ℝ) < r + s)).mpr
    linarith
  have hpq : 1 - p = (s : ℝ) / (r + s) := by dsimp [p]; field_simp; ring
  have hwr := fluctuationWindow_pos (k := k) hr0
  have hws := fluctuationWindow_pos (k := k) hs0
  have hpoint : ∀ j ≤ m,
      (transferLower k)^2 * (1 - ((j : ℝ) - m * p)^2 / (fluctuationWindow r k)^2 -
        ((j : ℝ) - m * p)^2 / (fluctuationWindow s k)^2) ≤
      auxiliaryProbability r k j * auxiliaryProbability s k (m - j) := by
    intro j hj
    apply product_lower_two_deviations (transferLower_pos k).le (by positivity) (by positivity)
      (auxiliaryProbability_nonneg r k j) (auxiliaryProbability_nonneg s k (m - j))
    · intro hdev
      apply auxiliaryProbability_center_lower hk hr hrrep hrerr
      have hsq : ((j : ℝ) - m * p)^2 < (fluctuationWindow r k)^2 :=
        (div_lt_one (sq_pos_of_pos hwr)).mp hdev
      by_contra hgap
      have hdiff : fluctuationWindow r k < (j : ℝ) - m * p := by
        change (m : ℝ) * p + 2 * fluctuationWindow r k ≤ (r : ℝ) * center r k at hgapr
        linarith
      nlinarith
    · intro hdev
      apply auxiliaryProbability_center_lower hk hs hsrep hserr
      have hsq : ((j : ℝ) - m * p)^2 < (fluctuationWindow s k)^2 :=
        (div_lt_one (sq_pos_of_pos hws)).mp hdev
      rw [← hpq] at hgaps
      rw [Nat.cast_sub hj]
      by_contra hgap
      have hdiff : fluctuationWindow s k < -((j : ℝ) - m * p) := by linarith
      nlinarith
  have hmean := binomialMean_mono hp0 hp1 hpoint
  rw [binomialMean_const_mul, binomialMean_sub, binomialMean_sub, binomialMean_const,
    binomialMean_div_const, binomialMean_div_const, binomialMean_centered_square] at hmean
  apply le_trans _ (hmean.trans (auxiliary_interpolation hr0 hs0 m))
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  have hmp : (m : ℝ) * p ≤ (capMultiplier k : ℝ) * r := by
    have h := mul_le_mul_of_nonneg_right hm hp0
    have he : ((capMultiplier k : ℝ) * ((r : ℝ) + s)) * p =
        (capMultiplier k : ℝ) * r := by dsimp [p]; field_simp
    simpa only [he] using h
  have hmq : (m : ℝ) * (1 - p) ≤ (capMultiplier k : ℝ) * s := by
    have h := mul_le_mul_of_nonneg_right hm (sub_nonneg.mpr hp1)
    have he : ((capMultiplier k : ℝ) * ((r : ℝ) + s)) * (1 - p) =
        (capMultiplier k : ℝ) * s := by rw [hpq]; field_simp
    simpa only [he] using h
  have hvr : (m : ℝ) * p * (1 - p) ≤ (capMultiplier k : ℝ) * r := by
    have h := mul_le_mul_of_nonneg_left (show 1 - p ≤ 1 by linarith)
      (mul_nonneg (Nat.cast_nonneg m) hp0)
    nlinarith
  have hvs : (m : ℝ) * p * (1 - p) ≤ (capMultiplier k : ℝ) * s := by
    have h := mul_le_mul_of_nonneg_left hp1
      (mul_nonneg (Nat.cast_nonneg m) (sub_nonneg.mpr hp1))
    nlinarith
  have hfr := div_le_div_of_nonneg_right hvr (sq_nonneg (fluctuationWindow r k))
  have hfs := div_le_div_of_nonneg_right hvs (sq_nonneg (fluctuationWindow s k))
  unfold samplingError
  linarith

def densityWindow (n k : ℕ) : ℝ := (n : ℝ)^(-delta k)

theorem densityWindow_pos {n k : ℕ} (hn : 0 < n) : 0 < densityWindow n k :=
  Real.rpow_pos_of_pos (by exact_mod_cast hn) _

theorem fluctuationWindow_eq_mul {n k : ℕ} (hn : 0 < n) :
    fluctuationWindow n k = (n : ℝ) * densityWindow n k := by
  unfold fluctuationWindow densityWindow
  rw [sub_eq_add_neg, Real.rpow_add (by exact_mod_cast hn), Real.rpow_one]

theorem fluctuationWindow_one_le {n k : ℕ} (hk : 3 ≤ k) (hn : 0 < n) :
    1 ≤ fluctuationWindow n k := by
  apply Real.one_le_rpow (by exact_mod_cast hn : (1 : ℝ) ≤ n)
  have h := delta_lt_half hk
  linarith

theorem densityWindow_antitone {r s k : ℕ} (hk : 3 ≤ k) (hr : 0 < r) (hrs : r ≤ s) :
    densityWindow s k ≤ densityWindow r k :=
  Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hr) (by exact_mod_cast hrs)
    (neg_nonpos.mpr (delta_pos hk).le)

theorem densityWindow_tendsto (k : ℕ) (hk : 3 ≤ k) :
    Filter.Tendsto (fun n : ℕ => densityWindow n k) Filter.atTop (nhds 0) :=
  (tendsto_rpow_neg_atTop (delta_pos hk)).comp (tendsto_natCast_atTop_atTop (R := ℝ))

theorem concentrationError_tendsto (k : ℕ) (hk : 3 ≤ k) :
    Filter.Tendsto (fun n : ℕ => concentrationError n k) Filter.atTop (nhds 0) := by
  have hη : 0 < eta k := by rw [eta_eq_twice_delta]; positivity [delta_pos hk]
  have ht := (tendsto_rpow_neg_atTop hη).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [concentrationError, Function.comp_apply, mul_zero] using ht.const_mul (varianceConstant k)

theorem samplingError_identity {n k : ℕ} (hn : 0 < n) :
    samplingError n k = (capMultiplier k : ℝ) * (n : ℝ)^(-(1 - 2 * delta k)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold samplingError fluctuationWindow
  rw [← Real.rpow_two ((n : ℝ)^(1 - delta k)), ← Real.rpow_mul hn'.le]
  have he : -(1 - 2 * delta k) = 1 - (1 - delta k) * 2 := by ring
  rw [he, Real.rpow_sub hn', Real.rpow_one]
  ring

theorem samplingError_tendsto (k : ℕ) (hk : 3 ≤ k) :
    Filter.Tendsto (fun n : ℕ => samplingError n k) Filter.atTop (nhds 0) := by
  have hd : 0 < 1 - 2 * delta k := by linarith [delta_lt_half hk]
  have ht := (tendsto_rpow_neg_atTop hd).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht' : Filter.Tendsto (fun n : ℕ => (capMultiplier k : ℝ) * (n : ℝ)^(-(1 - 2 * delta k)))
      Filter.atTop (nhds 0) := by simpa only [Function.comp_apply, mul_zero] using ht.const_mul (capMultiplier k : ℝ)
  apply ht'.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact (samplingError_identity (k := k) (by omega)).symm

theorem fluctuationWindow_tendsto (k : ℕ) (hk : 3 ≤ k) :
    Filter.Tendsto (fun n : ℕ => fluctuationWindow n k) Filter.atTop Filter.atTop := by
  have hd : 0 < 1 - delta k := by linarith [delta_lt_half hk]
  exact (tendsto_rpow_atTop hd).comp (tendsto_natCast_atTop_atTop (R := ℝ))

theorem center_lower_of_auxiliary_probability {n k : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
    {c : ℝ} (hc0 : 0 ≤ c) (hcL : c ≤ capMultiplier k)
    (hprob : concentrationError n k < auxiliaryProbability n k ⌊c * n⌋₊) :
    c - 2 * densityWindow n k < center n k := by
  have hn0 : 0 < n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hf := Nat.floor_le (mul_nonneg hc0 hn'.le)
  have hm : ⌊c * (n : ℝ)⌋₊ ≤ mainCap n k := by
    have h := hf.trans (mul_le_mul_of_nonneg_right hcL hn'.le)
    exact_mod_cast (show (⌊c * (n : ℝ)⌋₊ : ℝ) ≤ (mainCap n k : ℝ) by
      simpa only [mainCap, Nat.cast_mul] using h)
  by_contra h
  have hw := fluctuationWindow_one_le (n := n) hk hn0
  have he := fluctuationWindow_eq_mul (k := k) hn0
  have hc : center n k + 2 * densityWindow n k ≤ c := by linarith
  have hmul := mul_le_mul_of_nonneg_left hc hn'.le
  have hfloor := Nat.lt_floor_add_one (c * (n : ℝ))
  have hgap : (n : ℝ) * center n k + fluctuationWindow n k ≤ ⌊c * (n : ℝ)⌋₊ := by
    nlinarith
  exact not_lt_of_ge (auxiliaryProbability_center_upper hk hn hm hgap) hprob

theorem center_sum_comparison_of_bounds {r s k : ℕ} (hk : 3 ≤ k)
    (hr : k + 1 ≤ r) (hs : k + 1 ≤ s)
    (hrrep : 2 * repeatPairs k ≤ r) (hsrep : 2 * repeatPairs k ≤ s)
    (hrerr : concentrationError r k ≤ 1 / 2) (hserr : concentrationError s k ≤ 1 / 2)
    (hrsample : samplingError r k ≤ 1 / 4) (hssample : samplingError s k ≤ 1 / 4)
    (hNerr : concentrationError (r + s) k < (transferLower k)^2 / 2)
    (hlow : 2 * densityWindow (min r s) k ≤ min (center r k) (center s k)) :
    min (center r k) (center s k) - 4 * densityWindow (min r s) k ≤ center (r + s) k := by
  have hr0 : 0 < r := by omega
  have hs0 : 0 < s := by omega
  have hu0 : 0 < min r s := lt_min hr0 hs0
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr0
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs0
  have hN' : (0 : ℝ) < (r : ℝ) + s := by positivity
  let c := min (center r k) (center s k) - 2 * densityWindow (min r s) k
  have hc0 : 0 ≤ c := sub_nonneg.mpr hlow
  have hcL : c ≤ capMultiplier k := by
    have hh := (min_le_left (center r k) (center s k)).trans (center_le_capMultiplier (by omega) hr0)
    dsimp [c]
    have hp := (densityWindow_pos (k := k) hu0).le
    linarith
  have hcr : c + 2 * densityWindow r k ≤ center r k := by
    have hd := densityWindow_antitone hk hu0 (min_le_left r s)
    have hh := min_le_left (center r k) (center s k)
    dsimp [c]
    linarith
  have hcs : c + 2 * densityWindow s k ≤ center s k := by
    have hd := densityWindow_antitone hk hu0 (min_le_right r s)
    have hh := min_le_right (center r k) (center s k)
    dsimp [c]
    linarith
  let m := ⌊c * ((r : ℝ) + s)⌋₊
  have hm : (m : ℝ) ≤ c * ((r : ℝ) + s) := Nat.floor_le (mul_nonneg hc0 hN'.le)
  have hmr : (m : ℝ) * ((r : ℝ) / (r + s)) ≤ c * r := by
    have hh := mul_le_mul_of_nonneg_right hm (show 0 ≤ (r : ℝ) / (r + s) by positivity)
    have he : c * ((r : ℝ) + s) * ((r : ℝ) / (r + s)) = c * r := by field_simp
    rwa [he] at hh
  have hms : (m : ℝ) * ((s : ℝ) / (r + s)) ≤ c * s := by
    have hh := mul_le_mul_of_nonneg_right hm (show 0 ≤ (s : ℝ) / (r + s) by positivity)
    have he : c * ((r : ℝ) + s) * ((s : ℝ) / (r + s)) = c * s := by field_simp
    rwa [he] at hh
  have hprob := auxiliary_interpolation_center_lower hk hr hs hrrep hsrep hrerr hserr
    (hm.trans (mul_le_mul_of_nonneg_right hcL hN'.le))
    (show (m : ℝ) * ((r : ℝ) / (r + s)) + 2 * fluctuationWindow r k ≤ (r : ℝ) * center r k by
      rw [fluctuationWindow_eq_mul hr0]
      have hh := mul_le_mul_of_nonneg_left hcr hr'.le
      nlinarith)
    (show (m : ℝ) * ((s : ℝ) / (r + s)) + 2 * fluctuationWindow s k ≤ (s : ℝ) * center s k by
      rw [fluctuationWindow_eq_mul hs0]
      have hh := mul_le_mul_of_nonneg_left hcs hs'.le
      nlinarith)
  have hhalf : (transferLower k)^2 / 2 ≤ auxiliaryProbability (r + s) k m := by
    have hh := mul_le_mul_of_nonneg_left (show (1 / 2 : ℝ) ≤ 1 - samplingError r k - samplingError s k by linarith)
      (sq_nonneg (transferLower k))
    nlinarith
  have hcN := center_lower_of_auxiliary_probability hk (by omega : k + 1 ≤ r + s) hc0 hcL
    (show concentrationError (r + s) k < auxiliaryProbability (r + s) k ⌊c * ((r + s : ℕ) : ℝ)⌋₊ by
      simpa only [Nat.cast_add, ← show ⌊c * ((r : ℝ) + s)⌋₊ = m from rfl] using hNerr.trans_le hhalf)
  have hd := densityWindow_antitone hk hu0 (show min r s ≤ r + s by omega)
  dsimp [c] at hcN
  linarith

def neighborFactor (k : ℕ) : ℝ := Real.exp (-2 * (capMultiplier k : ℝ))

def neighborLower (k : ℕ) : ℝ := neighborFactor k * transferLower k

theorem neighborLower_pos (k : ℕ) : 0 < neighborLower k :=
  mul_pos (Real.exp_pos _) (transferLower_pos k)

@[simp] theorem auxiliaryProbability_zero (n k : ℕ) : auxiliaryProbability n k 0 = 1 := by
  simp only [auxiliaryProbability, auxiliarySurvival, Function.iterate_zero, id_eq, alive_univ]

theorem neighbor_all_left {s k m : ℕ} (hs : 0 < s) :
    ((s : ℝ) / (s + 1))^m * auxiliaryProbability s k m ≤ auxiliaryProbability (s + 1) k m := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hp0 : 0 ≤ (s : ℝ) / (s + 1) := by positivity
  have hp1 : (s : ℝ) / (s + 1) ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℝ) < s + 1)).mpr
    linarith
  have h := binomialMean_all_success hp0 hp1 m
    (fun j => auxiliaryProbability s k j * auxiliaryProbability 1 k (m - j))
    (fun j _ => mul_nonneg (auxiliaryProbability_nonneg _ _ _) (auxiliaryProbability_nonneg _ _ _))
  simp only [Nat.sub_self, auxiliaryProbability_zero, mul_one] at h
  apply h.trans
  simpa only [Nat.cast_one] using (auxiliary_interpolation (k := k) hs (by omega : 0 < 1) m)

theorem neighbor_pow_lower {s k m : ℕ} (hs : 0 < s)
    (hm : (m : ℝ) ≤ (capMultiplier k : ℝ) * ((s : ℝ) + 1)) :
    neighborFactor k ≤ ((s : ℝ) / (s + 1))^m := by
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hN : (0 : ℝ) < s + 1 := by linarith
  have hx0 : (0 : ℝ) ≤ 1 / ((s : ℝ) + 1) := by positivity
  have hx : (1 : ℝ) / ((s : ℝ) + 1) ≤ 1 / 2 := by
    apply (div_le_iff₀ hN).mpr
    linarith
  have hbase := exp_neg_two_le_one_sub hx0 hx
  have he : 1 - (1 : ℝ) / ((s : ℝ) + 1) = (s : ℝ) / (s + 1) := by field_simp; ring
  rw [he] at hbase
  have hpow := pow_le_pow_left₀ (Real.exp_pos _).le hbase m
  rw [← Real.exp_nat_mul] at hpow
  apply le_trans _ hpow
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right hm hx0
  have he' : (capMultiplier k : ℝ) * ((s : ℝ) + 1) * (1 / ((s : ℝ) + 1)) = capMultiplier k := by field_simp
  rw [he'] at hh
  nlinarith

theorem center_neighbor_comparison_of_bounds {s k : ℕ} (hk : 3 ≤ k)
    (hs : k + 1 ≤ s) (hsrep : 2 * repeatPairs k ≤ s)
    (hserr : concentrationError s k ≤ 1 / 2)
    (hNerr : concentrationError (s + 1) k < neighborLower k)
    (hlow : 2 * densityWindow s k ≤ center s k)
    (hwindow : (capMultiplier k : ℝ) ≤ fluctuationWindow s k) :
    center s k - 4 * densityWindow s k ≤ center (s + 1) k := by
  have hs0 : 0 < s := by omega
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs0
  let c := center s k - 2 * densityWindow s k
  have hc0 : 0 ≤ c := sub_nonneg.mpr hlow
  have hcenter := center_le_capMultiplier (by omega : k ≤ s) hs0
  have hcL : c ≤ capMultiplier k := by
    have hp := (densityWindow_pos (k := k) hs0).le
    dsimp [c]
    linarith
  let m := ⌊c * ((s : ℝ) + 1)⌋₊
  have hm : (m : ℝ) ≤ c * ((s : ℝ) + 1) := Nat.floor_le (by positivity)
  have hmL := hm.trans (mul_le_mul_of_nonneg_right hcL (by positivity : (0 : ℝ) ≤ (s : ℝ) + 1))
  have hgap : (m : ℝ) + fluctuationWindow s k ≤ (s : ℝ) * center s k := by
    have hw := fluctuationWindow_eq_mul (k := k) hs0
    have he : c * ((s : ℝ) + 1) = (s : ℝ) * center s k - 2 * fluctuationWindow s k + c := by
      rw [hw]
      dsimp [c]
      ring
    rw [he] at hm
    linarith
  have hlocal := auxiliaryProbability_center_lower hk hs hsrep hserr hgap
  have hpow := neighbor_pow_lower (k := k) hs0 hmL
  have hprod := mul_le_mul hpow hlocal (transferLower_pos k).le
    (pow_nonneg (by positivity : (0 : ℝ) ≤ (s : ℝ) / (s + 1)) m)
  have hprob : neighborLower k ≤ auxiliaryProbability (s + 1) k m :=
    hprod.trans (neighbor_all_left hs0)
  have hcN := center_lower_of_auxiliary_probability hk (by omega : k + 1 ≤ s + 1) hc0 hcL
    (show concentrationError (s + 1) k < auxiliaryProbability (s + 1) k ⌊c * ((s + 1 : ℕ) : ℝ)⌋₊ by
      simpa only [Nat.cast_add, Nat.cast_one] using hNerr.trans_le hprob)
  have hd := densityWindow_antitone hk hs0 (Nat.le_succ s)
  dsimp [c] at hcN
  linarith

structure CenterRegular (k n : ℕ) : Prop where
  size : k + 1 ≤ n
  repetition : 2 * repeatPairs k ≤ n
  error : concentrationError n k ≤ 1 / 2
  sampling : samplingError n k ≤ 1 / 4
  sumError : concentrationError n k < (transferLower k)^2 / 2
  neighborError : concentrationError n k < neighborLower k
  centerLower : lowerCenterBound ≤ center n k
  densitySmall : 2 * densityWindow n k ≤ lowerCenterBound
  windowLarge : (capMultiplier k : ℝ) ≤ fluctuationWindow n k

theorem centerRegular_eventually (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in Filter.atTop, CenterRegular k n := by
  have hsize : ∀ᶠ n : ℕ in Filter.atTop, k + 1 ≤ n := Filter.eventually_ge_atTop _
  have hrep := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Filter.eventually_ge_atTop (2 * repeatPairs k))
  have he := (concentrationError_tendsto k hk).eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)
  have hs := (samplingError_tendsto k hk).eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 4)
  have heSum := (concentrationError_tendsto k hk).eventually_lt_const
    (div_pos (sq_pos_of_pos (transferLower_pos k)) (by norm_num) : (0 : ℝ) < (transferLower k)^2 / 2)
  have heNeighbor := (concentrationError_tendsto k hk).eventually_lt_const (neighborLower_pos k)
  have hd := (densityWindow_tendsto k hk).eventually_lt_const
    (div_pos lowerCenterBound_pos (by norm_num) : (0 : ℝ) < lowerCenterBound / 2)
  have hw := (fluctuationWindow_tendsto k hk).eventually (Filter.eventually_ge_atTop (capMultiplier k : ℝ))
  filter_upwards [hsize, hrep, he, hs, heSum, heNeighbor, center_bounds_eventually k hk, hd, hw]
    with n hn hr he hs hes hen hc hd hw
  exact ⟨hn, hr, he.le, hs.le, hes, hen, hc.1, by linarith, hw⟩

theorem center_comparisons (k : ℕ) (hk : 3 ≤ k) :
    ∃ N : ℕ,
      (∀ r ≥ N, ∀ s ≥ N,
        min (center r k) (center s k) - 4 * densityWindow (min r s) k ≤ center (r + s) k) ∧
      (∀ s ≥ N, center s k - 4 * densityWindow s k ≤ center (s + 1) k) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (centerRegular_eventually k hk)
  refine ⟨N, ?_, ?_⟩
  · intro r hr s hs
    have hR := hN r hr
    have hS := hN s hs
    have hU := hN (min r s) (le_min hr hs)
    have hT := hN (r + s) (by omega)
    exact center_sum_comparison_of_bounds hk hR.size hS.size hR.repetition hS.repetition
      hR.error hS.error hR.sampling hS.sampling hT.sumError
      (hU.densitySmall.trans (le_min hR.centerLower hS.centerLower))
  · intro s hs
    have hS := hN s hs
    have hT := hN (s + 1) (by omega)
    exact center_neighbor_comparison_of_bounds hk hS.size hS.repetition hS.error hT.neighborError
      (hS.densitySmall.trans hS.centerLower) hS.windowLarge

end


end FixedClauseThreshold

end OAI

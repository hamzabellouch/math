import Mathlib

namespace OAI

open Filter
open scoped Topology

namespace Balanced
open scoped _root_.Balanced

theorem abs_prod_sub_prod_le_sum_errors {ι : Type*} (s : Finset ι)
    (f g : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1)
    (hg : ∀ i ∈ s, 0 ≤ g i ∧ g i ≤ 1) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤ ∑ i ∈ s, |f i - g i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfa := hf a (Finset.mem_insert_self a s)
    have hga := hg a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgs : ∀ i ∈ s, 0 ≤ g i ∧ g i ≤ 1 := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hgp0 : 0 ≤ ∏ i ∈ s, g i := Finset.prod_nonneg fun i hi => (hgs i hi).1
    have hgp1 : (∏ i ∈ s, g i) ≤ 1 := Finset.prod_le_one₀
      (fun i hi => (hgs i hi).1) (fun i hi => (hgs i hi).2)
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    calc
      |f a * (∏ i ∈ s, f i) - g a * ∏ i ∈ s, g i|
          = |f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) +
              (f a - g a) * ∏ i ∈ s, g i| := by congr 1; ring
      _ ≤ |f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)| +
            |(f a - g a) * ∏ i ∈ s, g i| := abs_add_le _ _
      _ = f a * |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| +
            |f a - g a| * ∏ i ∈ s, g i := by
        rw [abs_mul, abs_mul, abs_of_nonneg hfa.1, abs_of_nonneg hgp0]
      _ ≤ |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| + |f a - g a| := by
        nlinarith [abs_nonneg ((∏ i ∈ s, f i) - ∏ i ∈ s, g i), abs_nonneg (f a - g a)]
      _ ≤ |f a - g a| + ∑ i ∈ s, |f i - g i| := by linarith [ih hfs hgs]

theorem descFactorial_factor_error (d N i r : ℕ)
    (hd : d ≤ N) (hi : i < r) (hr : r < N) :
    |((d - i : ℕ) : ℝ) / (N - i : ℕ) - (d : ℝ) / N| ≤
      (r : ℝ) / ((N : ℝ) - r) := by
  have hiN : i < N := hi.trans hr
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hr)
  have hNipos : (0 : ℝ) < (N : ℝ) - i := sub_pos.mpr (by exact_mod_cast hiN)
  have hNrpos : (0 : ℝ) < (N : ℝ) - r := sub_pos.mpr (by exact_mod_cast hr)
  have hdi_nonneg : (0 : ℝ) ≤ (d : ℝ) / N := by positivity
  have hir : (i : ℝ) ≤ r := by exact_mod_cast hi.le
  have hdN : (d : ℝ) ≤ N := by exact_mod_cast hd
  rw [Nat.cast_sub hiN.le]
  by_cases hid : i ≤ d
  · rw [Nat.cast_sub hid]
    have hratio : ((d : ℝ) - i) / ((N : ℝ) - i) ≤ (d : ℝ) / N := by
      apply (div_le_div_iff₀ hNipos hNpos).2
      nlinarith
    rw [abs_of_nonpos (sub_nonpos.mpr hratio)]
    have hfirst : (d : ℝ) / N - ((d : ℝ) - i) / ((N : ℝ) - i) ≤
        (i : ℝ) / ((N : ℝ) - i) := by
      apply (le_div_iff₀ hNipos).2
      have hcancel : (((d : ℝ) - i) / ((N : ℝ) - i)) * ((N : ℝ) - i) = (d : ℝ) - i :=
        div_mul_cancel₀ _ hNipos.ne'
      have hcancel' : ((d : ℝ) / N) * N = d := div_mul_cancel₀ _ hNpos.ne'
      nlinarith [mul_nonneg hdi_nonneg (Nat.cast_nonneg i)]
    have hsecond : (i : ℝ) / ((N : ℝ) - i) ≤ (r : ℝ) / ((N : ℝ) - r) := by
      apply (div_le_div_iff₀ hNipos hNrpos).2
      nlinarith
    linarith
  · have hdi : d < i := Nat.lt_of_not_ge hid
    rw [Nat.sub_eq_zero_of_le hdi.le, Nat.cast_zero, zero_div, zero_sub, abs_neg,
      abs_of_nonneg hdi_nonneg]
    apply (div_le_div_iff₀ hNpos hNrpos).2
    have hdr : (d : ℝ) ≤ r := by exact_mod_cast (hdi.trans hi).le
    nlinarith [mul_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]

theorem descFactorial_ratio_power_error (d N r : ℕ) (hd : d ≤ N) (hr : r < N) :
    |(d.descFactorial r : ℝ) / (N.descFactorial r : ℝ) - ((d : ℝ) / N) ^ r| ≤
      (r : ℝ) ^ 2 / ((N : ℝ) - r) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hr)
  let f : ℕ → ℝ := fun i => ((d - i : ℕ) : ℝ) / (N - i : ℕ)
  let g : ℕ → ℝ := fun _ => (d : ℝ) / N
  have hf : ∀ i ∈ Finset.range r, 0 ≤ f i ∧ f i ≤ 1 := by
    intro i hi
    have hiN : i < N := (Finset.mem_range.mp hi).trans hr
    have hden : (0 : ℝ) < (N - i : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hiN
    refine ⟨by dsimp [f]; positivity, ?_⟩
    apply (div_le_one hden).2
    exact_mod_cast Nat.sub_le_sub_right hd i
  have hg : ∀ i ∈ Finset.range r, 0 ≤ g i ∧ g i ≤ 1 := by
    intro i hi
    refine ⟨by dsimp [g]; positivity, ?_⟩
    apply (div_le_one hNpos).2
    exact_mod_cast hd
  have hprod := abs_prod_sub_prod_le_sum_errors (Finset.range r) f g hf hg
  have hsum : (∑ i ∈ Finset.range r, |f i - g i|) ≤
      (r : ℝ) ^ 2 / ((N : ℝ) - r) := by
    calc
      (∑ i ∈ Finset.range r, |f i - g i|)
          ≤ ∑ _i ∈ Finset.range r, (r : ℝ) / ((N : ℝ) - r) := by
        apply Finset.sum_le_sum
        intro i hi
        exact descFactorial_factor_error d N i r hd (Finset.mem_range.mp hi) hr
      _ = (r : ℝ) ^ 2 / ((N : ℝ) - r) := by simp; ring
  have heq : (∏ i ∈ Finset.range r, f i) =
      (d.descFactorial r : ℝ) / (N.descFactorial r : ℝ) := by
    simp only [f, Nat.descFactorial_eq_prod_range, Nat.cast_prod, Finset.prod_div_distrib]
  have heqg : (∏ i ∈ Finset.range r, g i) = ((d : ℝ) / N) ^ r := by simp [g, div_pow]
  rw [heq, heqg] at hprod
  exact hprod.trans hsum

theorem descFactorial_ratio_power_error_uniform (d N r B : ℕ)
    (hd : d ≤ N) (hrB : r ≤ B) (hN : 0 < N) (hlarge : 2 * B ≤ N) :
    |(d.descFactorial r : ℝ) / (N.descFactorial r : ℝ) - ((d : ℝ) / N) ^ r| ≤
      2 * (B : ℝ) ^ 2 / N := by
  by_cases hr0 : r = 0
  · subst r
    simp only [Nat.descFactorial_zero, Nat.cast_one, div_self one_ne_zero, pow_zero,
      sub_self, abs_zero]
    positivity
  have hr : r < N := by omega
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hden : (0 : ℝ) < (N : ℝ) - r := sub_pos.mpr (by exact_mod_cast hr)
  have hrBreal : (r : ℝ) ≤ B := by exact_mod_cast hrB
  have hlargeReal : 2 * (B : ℝ) ≤ N := by exact_mod_cast hlarge
  apply (descFactorial_ratio_power_error d N r hd hr).trans
  apply (div_le_div_iff₀ hden hNreal).2
  have hrr : (r : ℝ) ^ 2 ≤ (B : ℝ) ^ 2 := by nlinarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r), (Nat.cast_nonneg B : (0 : ℝ) ≤ B)]
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ N by positivity) (sub_nonneg.mpr hrr),
    mul_nonneg (sq_nonneg (B : ℝ)) (show 0 ≤ (N : ℝ) - 2 * r by linarith)]

theorem tendsto_descFactorial_ratio_sub_power {ι : Type*} {l : Filter ι}
    (d N : ι → ℕ) (r : ℕ) (hN : Tendsto N l atTop)
    (hd : ∀ᶠ t in l, d t ≤ N t) :
    Tendsto (fun t => (d t |>.descFactorial r : ℝ) / (N t |>.descFactorial r : ℝ) -
      ((d t : ℝ) / N t) ^ r) l (𝓝 0) := by
  have hNreal : Tendsto (fun t => (N t : ℝ)) l atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hden : Tendsto (fun t => (N t : ℝ) - r) l atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right l (-(r : ℝ)) hNreal
  have hbound := hden.const_div_atTop ((r : ℝ) ^ 2)
  apply (tendsto_zero_iff_abs_tendsto_zero _).2
  apply squeeze_zero' (Filter.Eventually.of_forall fun t => abs_nonneg _) ?_ hbound
  filter_upwards [hd, hN.eventually (eventually_gt_atTop r)] with t hdt hNt
  exact descFactorial_ratio_power_error (d t) (N t) r hdt hNt

theorem tendsto_descFactorial_ratio {ι : Type*} {l : Filter ι}
    (d N : ι → ℕ) (r : ℕ) {z : ℝ} (hN : Tendsto N l atTop)
    (hd : ∀ᶠ t in l, d t ≤ N t)
    (hz : Tendsto (fun t => (d t : ℝ) / N t) l (𝓝 z)) :
    Tendsto (fun t => (d t |>.descFactorial r : ℝ) / (N t |>.descFactorial r : ℝ))
      l (𝓝 (z ^ r)) := by
  have h := (tendsto_descFactorial_ratio_sub_power d N r hN hd).add (hz.pow r)
  simpa only [sub_add_cancel, zero_add] using h

theorem choose_ratio_eq_descFactorial_ratio (d N r : ℕ) (hrd : r ≤ d) (hdN : d ≤ N) :
    ((N - r).choose (d - r) : ℝ) / (N.choose d : ℝ) =
      (d.descFactorial r : ℝ) / (N.descFactorial r : ℝ) := by
  have hNd : (N.choose d : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hdN).ne'
  have hNr : (N.choose r : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (hrd.trans hdN)).ne'
  have hfac : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
  calc
    ((N - r).choose (d - r) : ℝ) / (N.choose d : ℝ)
        = (d.choose r : ℝ) / (N.choose r : ℝ) := by
      apply (div_eq_div_iff hNd hNr).2
      have h := Nat.choose_mul (n := N) hrd
      exact_mod_cast (by nlinarith : (N - r).choose (d - r) * N.choose r = d.choose r * N.choose d)
    _ = (d.descFactorial r : ℝ) / (N.descFactorial r : ℝ) := by
      simp only [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
      field_simp

theorem uniform_subset_contains_probability {α : Type*} [DecidableEq α]
    (U T : Finset α) (d : ℕ) (hTU : T ⊆ U) (hd : d ≤ U.card) :
    ((PMF.uniformOfFinset (U.powersetCard d) (Finset.powersetCard_nonempty.mpr hd)).toOuterMeasure
      {S : Finset α | T ⊆ S}).toReal =
      (d.descFactorial T.card : ℝ) / (U.card.descFactorial T.card : ℝ) := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFinset_apply, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast, Finset.card_powersetCard, Set.mem_ofPred_eq]
  by_cases hTd : T.card ≤ d
  · rw [Finset.card_filter_powersetCard_subset T U d hTU hTd]
    exact choose_ratio_eq_descFactorial_ratio d U.card T.card hTd hd
  · have hempty : (U.powersetCard d).filter (T ⊆ ·) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro S hS hTS
      have hcard := Finset.card_le_card hTS
      rw [(Finset.mem_powersetCard.mp hS).2] at hcard
      exact hTd hcard
    rw [hempty, Finset.card_empty, Nat.cast_zero, zero_div,
      Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge hTd), Nat.cast_zero, zero_div]

theorem uniform_subset_contains_probability_error {α : Type*} [DecidableEq α]
    (U T : Finset α) (d B : ℕ) (hTU : T ⊆ U) (hd : d ≤ U.card)
    (hTB : T.card ≤ B) (hU : 0 < U.card) (hlarge : 2 * B ≤ U.card) :
    |((PMF.uniformOfFinset (U.powersetCard d) (Finset.powersetCard_nonempty.mpr hd)).toOuterMeasure
      {S : Finset α | T ⊆ S}).toReal - ((d : ℝ) / U.card) ^ T.card| ≤
        2 * (B : ℝ) ^ 2 / U.card := by
  rw [uniform_subset_contains_probability U T d hTU hd]
  exact descFactorial_ratio_power_error_uniform d U.card T.card B hd hTB hU hlarge

theorem uniform_subset_after_target_probability {α : Type*} [DecidableEq α]
    (U T : Finset α) (a : α) (d : ℕ) (hTU : T ⊆ U) (ha : a ∈ T)
    (hd : d ≤ U.card) :
    ((PMF.uniformOfFinset ((U.erase a).powersetCard (d - 1))
      (Finset.powersetCard_nonempty.mpr (by
        rw [Finset.card_erase_of_mem (hTU ha)]
        exact Nat.sub_le_sub_right hd 1))).toOuterMeasure
      {S : Finset α | T.erase a ⊆ S}).toReal =
      ((d - 1).descFactorial (T.card - 1) : ℝ) /
        ((U.card - 1).descFactorial (T.card - 1) : ℝ) := by
  have hsub : T.erase a ⊆ U.erase a := Finset.erase_subset_erase a hTU
  have hcard : d - 1 ≤ (U.erase a).card := by
    rw [Finset.card_erase_of_mem (hTU ha)]
    exact Nat.sub_le_sub_right hd 1
  simpa only [Finset.card_erase_of_mem ha, Finset.card_erase_of_mem (hTU ha)] using
    uniform_subset_contains_probability (U.erase a) (T.erase a) (d - 1) hsub hcard

end Balanced

end OAI

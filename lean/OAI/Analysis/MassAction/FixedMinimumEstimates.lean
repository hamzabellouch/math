import Mathlib

namespace OAI

universe uIota

noncomputable section

open Filter Finset
open scoped Topology BigOperators

namespace Problem326.FixedMinimum

/-- The affine value relative to the constant-slope branch `t`. -/
def relativeValue {ι : Type uIota} [Fintype ι]
    (t : ℝ) (r p : ι → ℝ) (h c : ℝ) : ℝ :=
  (∑ i, (r i - t) * h ^ p i) + c

/-- A strict limiting exponent gap makes the normalized monomial vanish.
This formulation permits the approximating exponents to leave their cube. -/
theorem tendsto_rpow_ratio {h p : ℕ → ℝ} {q p₀ : ℝ}
    (hh : ∀ n, 0 < h n) (hh0 : Tendsto h atTop (𝓝 0))
    (hp : Tendsto p atTop (𝓝 p₀)) (hqp : q < p₀) :
    Tendsto (fun n => h n ^ p n / h n ^ q) atTop (𝓝 0) := by
  have hlim := hh0.rpow (hp.sub_const q) (Or.inr (sub_pos.mpr hqp))
  simp only [Real.zero_rpow (ne_of_gt (sub_pos.mpr hqp))] at hlim
  convert hlim using 1
  ext n
  exact (Real.rpow_sub (hh n) (p n) q).symm

/-- Finite sums of monomials whose nonzero coefficients have exponent above `q`
are negligible relative to `h^q`. -/
theorem tendsto_normalized_sum {ι : Type uIota} [Fintype ι]
    {h : ℕ → ℝ} {p : ℕ → ι → ℝ} {p₀ a : ι → ℝ} {q : ℝ}
    (hh : ∀ n, 0 < h n) (hh0 : Tendsto h atTop (𝓝 0))
    (hp : ∀ i, Tendsto (fun n => p n i) atTop (𝓝 (p₀ i)))
    (hgap : ∀ i, a i ≠ 0 → q < p₀ i) :
    Tendsto (fun n => (∑ i, a i * h n ^ p n i) / h n ^ q)
      atTop (𝓝 0) := by
  have hterm : ∀ i, Tendsto (fun n => a i * (h n ^ p n i / h n ^ q))
      atTop (𝓝 0) := by
    intro i
    by_cases hai : a i = 0
    · simp [hai]
    · simpa using (tendsto_rpow_ratio hh hh0 (hp i) (hgap i hai)).const_mul (a i)
  have hs := tendsto_finsetSum Finset.univ (fun i _ => hterm i)
  simpa only [Finset.sum_const_zero, Finset.sum_div, mul_div_assoc] using hs

/-- A positive coefficient in a nonnegative sum cannot be dominated by a
strictly higher exponent, even in the presence of a negligible offset. -/
theorem coefficient_nonpos_of_domination
    {A B d : ℕ → ℝ} {c : ℝ}
    (hA : ∀ n, 0 < A n) (hB : ∀ n, 0 < B n)
    (hBA : Tendsto (fun n => B n / A n) atTop (𝓝 0))
    (hd : Tendsto (fun n => d n / B n) atTop (𝓝 0))
    (hdom : ∀ n, c * A n ≤ B n - d n) : c ≤ 0 := by
  have hlim : Tendsto (fun n => (B n / A n) * (1 - d n / B n))
      atTop (𝓝 0) := by
    simpa using hBA.mul (tendsto_const_nhds.sub hd)
  apply ge_of_tendsto hlim
  filter_upwards [] with n
  have h := (le_div_iff₀ (hA n)).2 (hdom n)
  convert h using 1
  field_simp [ne_of_gt (hA n), ne_of_gt (hB n)]

/-- The quotient version also allows a moving denominator exponent. -/
theorem tendsto_rpow_ratio_of_gap {h p q : ℕ → ℝ} {p₀ q₀ : ℝ}
    (hh : ∀ n, 0 < h n) (hh0 : Tendsto h atTop (𝓝 0))
    (hp : Tendsto p atTop (𝓝 p₀)) (hq : Tendsto q atTop (𝓝 q₀))
    (hqp : q₀ < p₀) :
    Tendsto (fun n => h n ^ p n / h n ^ q n) atTop (𝓝 0) := by
  have hlim := hh0.rpow (hp.sub hq) (Or.inr (sub_pos.mpr hqp))
  simp only [Real.zero_rpow (ne_of_gt (sub_pos.mpr hqp))] at hlim
  convert hlim using 1
  ext n
  exact (Real.rpow_sub (hh n) (p n) (q n)).symm

/-- Nonnegative raised coordinates of an active branch cannot have limiting
exponent below the offset exponent. -/
theorem active_raised_exponent_ge {ι : Type uIota} [Fintype ι]
    {h c : ℕ → ℝ} {p : ℕ → ι → ℝ} {p₀ r : ι → ℝ} {t β : ℝ}
    (hh : ∀ n, 0 < h n) (hh0 : Tendsto h atTop (𝓝 0))
    (hp : ∀ i, Tendsto (fun n => p n i) atTop (𝓝 (p₀ i)))
    (hr : ∀ i, t ≤ r i)
    (hc : Tendsto (fun n => c n / h n ^ β) atTop (𝓝 (-1)))
    (hactive : ∀ n, relativeValue t r (p n) (h n) (c n) ≤ 0)
    {i : ι} (hi : t < r i) : β ≤ p₀ i := by
  by_contra hle
  have hlt : p₀ i < β := lt_of_not_ge hle
  have hratio : Tendsto (fun n => h n ^ β / h n ^ p n i) atTop (𝓝 0) :=
    tendsto_rpow_ratio_of_gap hh hh0 tendsto_const_nhds (hp i) hlt
  have hlim : Tendsto (fun n => (-c n / h n ^ β) *
      (h n ^ β / h n ^ p n i)) atTop (𝓝 0) := by
    simpa only [neg_div, neg_neg, one_mul, mul_zero] using hc.neg.mul hratio
  have hnonpos : r i - t ≤ 0 := by
    apply ge_of_tendsto hlim
    filter_upwards [] with n
    have hsingle : (r i - t) * h n ^ p n i ≤
        ∑ j, (r j - t) * h n ^ p n j := by
      exact Finset.single_le_sum
        (fun j _ => mul_nonneg (sub_nonneg.mpr (hr j)) (Real.rpow_nonneg (hh n).le _))
        (Finset.mem_univ i)
    have hbound : (r i - t) * h n ^ p n i ≤ -c n := by
      have ha := hactive n
      unfold relativeValue at ha
      linarith
    have hdiv := (le_div_iff₀ (Real.rpow_pos_of_pos (hh n) (p n i))).2 hbound
    convert hdiv using 1
    field_simp [ne_of_gt (Real.rpow_pos_of_pos (hh n) β)]
  linarith

/-- A competitor with normalized value tending to `-1` defeats any branch
whose slope is coordinatewise above the baseline and whose normalized
offset tends to zero. No continuity of either offset is needed. -/
theorem not_active_of_offset_gap {ι : Type uIota} [Fintype ι]
    {h c d : ℕ → ℝ} {p : ℕ → ι → ℝ} {p₀ r s : ι → ℝ} {t γ : ℝ}
    (hh : ∀ n, 0 < h n) (hh0 : Tendsto h atTop (𝓝 0))
    (hp : ∀ i, Tendsto (fun n => p n i) atTop (𝓝 (p₀ i)))
    (hr : ∀ i, t ≤ r i)
    (hc : Tendsto (fun n => c n / h n ^ γ) atTop (𝓝 0))
    (hd : Tendsto (fun n => d n / h n ^ γ) atTop (𝓝 (-1)))
    (hgap : ∀ i, s i ≠ t → γ < p₀ i) :
    ¬ (∀ n, relativeValue t r (p n) (h n) (c n) ≤
      relativeValue t s (p n) (h n) (d n)) := by
  intro hactive
  have hsum : Tendsto (fun n => (∑ i, (s i - t) * h n ^ p n i) /
      h n ^ γ) atTop (𝓝 0) :=
    tendsto_normalized_sum hh hh0 hp (fun i hi => hgap i (sub_ne_zero.mp hi))
  have hvalue : Tendsto (fun n => relativeValue t s (p n) (h n) (d n) /
      h n ^ γ) atTop (𝓝 (-1)) := by
    simpa only [relativeValue, add_div, zero_add] using hsum.add hd
  have hbad : (0 : ℝ) ≤ -1 := by
    apply le_of_tendsto_of_tendsto hc hvalue
    filter_upwards [] with n
    apply (div_le_div_iff_of_pos_right (Real.rpow_pos_of_pos (hh n) γ)).2
    have hsum0 : 0 ≤ ∑ i, (r i - t) * h n ^ p n i := by
      exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (sub_nonneg.mpr (hr i)) (Real.rpow_nonneg (hh n).le _)
    have ha := hactive n
    unfold relativeValue at ha ⊢
    linarith
  norm_num at hbad

/-- The second exclusion in the fixed-minimum argument. A next-type
competitor supported on `U ∪ {j}` forces every unraised exponent below
its offset threshold. -/
theorem unraised_exponent_le {ι : Type uIota} [Fintype ι] [DecidableEq ι]
    {h c d : ℕ → ℝ} {p : ℕ → ι → ℝ} {p₀ r s : ι → ℝ}
    {t β γ : ℝ} {U : Finset ι} {j : ι}
    (hh : ∀ n, 0 < h n) (hh0 : Tendsto h atTop (𝓝 0))
    (hp : ∀ i, Tendsto (fun n => p n i) atTop (𝓝 (p₀ i)))
    (hr : ∀ i, t ≤ r i)
    (hc : Tendsto (fun n => c n / h n ^ γ) atTop (𝓝 0))
    (hd : Tendsto (fun n => d n / h n ^ γ) atTop (𝓝 (-1)))
    (hγβ : γ < β) (hpU : ∀ i ∈ U, β ≤ p₀ i)
    (hs : ∀ i, i ∉ U → i ≠ j → s i = t)
    (hactive : ∀ n, relativeValue t r (p n) (h n) (c n) ≤
      relativeValue t s (p n) (h n) (d n)) : p₀ j ≤ γ := by
  by_contra hj
  have hj' : γ < p₀ j := lt_of_not_ge hj
  apply not_active_of_offset_gap hh hh0 hp hr hc hd _ hactive
  intro i hi
  by_cases hiU : i ∈ U
  · exact hγβ.trans_le (hpU i hiU)
  · have hij : i = j := by
      by_contra hij
      exact hi (hs i hiU hij)
    simpa only [hij] using hj'

/-- When only one coordinate is unraised, the fixed minimum determines
that coordinate exactly. -/
theorem last_unraised_eq_minimum {ι : Type uIota} {p : ι → ℝ} {t β : ℝ} {j : ι}
    (hmin : ∃ i, p i = t) (htβ : t < β)
    (hother : ∀ i, i ≠ j → β ≤ p i) : p j = t := by
  obtain ⟨i, hi⟩ := hmin
  have hij : i = j := by
    by_contra hij
    have h := hother i hij
    rw [hi] at h
    exact (not_le_of_gt htβ) h
  simpa only [hij] using hi

/-- Combining the inductive error on raised coordinates with the threshold
bound on all other coordinates yields the full sup-norm error estimate. -/
theorem error_of_raised_and_unraised {ι : Type uIota} [Fintype ι]
    {p r : ι → ℝ} {U : Set ι} {t γ ε : ℝ}
    (hraised : ∀ i ∈ U, |p i - r i| < ε)
    (hr : ∀ i ∉ U, r i = t)
    (hlo : ∀ i ∉ U, t ≤ p i)
    (hhi : ∀ i ∉ U, p i ≤ γ) (hε : γ - t < ε) :
    ∀ i, |p i - r i| < ε := by
  intro i
  by_cases hi : i ∈ U
  · exact hraised i hi
  · rw [hr i hi, abs_of_nonneg (sub_nonneg.mpr (hlo i hi))]
    exact (sub_le_sub_right (hhi i hi) t).trans_lt hε

theorem fixed_minimum_label_bound {ι : Type uIota} [Fintype ι] [DecidableEq ι]
    {h c : ℕ → ℝ} {p : ℕ → ι → ℝ} {p₀ r : ι → ℝ}
    {t β ε : ℝ} {U : Finset ι}
    (hh : ∀ n, 0 < h n) (hh0 : Tendsto h atTop (𝓝 0))
    (hp : ∀ i, Tendsto (fun n => p n i) atTop (𝓝 (p₀ i)))
    (hlo : ∀ i, t ≤ p₀ i) (hmin : ∃ i, p₀ i = t)
    (htβ : t < β) (hε : 0 < ε)
    (hrin : ∀ i ∈ U, β ≤ r i) (hrout : ∀ i ∉ U, r i = t)
    (hoffset : (U = ∅ ∧ ∀ n, c n = 0) ∨
      Tendsto (fun n => c n / h n ^ β) atTop (𝓝 (-1)))
    (hbase : ∀ n, relativeValue t r (p n) (h n) (c n) ≤ 0)
    (hind : (∀ i ∈ U, β ≤ p₀ i) → ∀ i ∈ U, |p₀ i - r i| < ε)
    (hnext : (∀ i ∉ U, ∀ j ∉ U, i = j) ∨
      ∃ γ : ℝ, γ < β ∧ γ - t < ε ∧
        ∀ j, j ∉ U → ∃ s : ι → ℝ, ∃ d : ℕ → ℝ,
          Tendsto (fun n => d n / h n ^ γ) atTop (𝓝 (-1)) ∧
          (∀ i, i ∉ U → i ≠ j → s i = t) ∧
          (∀ n, relativeValue t r (p n) (h n) (c n) ≤
            relativeValue t s (p n) (h n) (d n))) :
    ∀ i, |p₀ i - r i| < ε := by
  have hr : ∀ i, t ≤ r i := by
    intro i
    by_cases hi : i ∈ U
    · exact htβ.le.trans (hrin i hi)
    · rw [hrout i hi]
  have hpU : ∀ i ∈ U, β ≤ p₀ i := by
    intro i hi
    rcases hoffset with ⟨hU, _⟩ | hc
    · simp [hU] at hi
    · exact active_raised_exponent_ge hh hh0 hp hr hc hbase
        (htβ.trans_le (hrin i hi))
  have herrU := hind hpU
  rcases hnext with hlast | ⟨γ, hγβ, hγε, hcomp⟩
  · obtain ⟨j, hj⟩ := hmin
    have hjU : j ∉ U := by
      intro hjU
      have hb := hpU j hjU
      rw [hj] at hb
      exact (not_le_of_gt htβ) hb
    intro i
    by_cases hi : i ∈ U
    · exact herrU i hi
    · have hij := hlast i hi j hjU
      rw [hrout i hi, hij, hj, sub_self, abs_zero]
      exact hε
  · have hcγ : Tendsto (fun n => c n / h n ^ γ) atTop (𝓝 0) := by
      rcases hoffset with ⟨_, hc⟩ | hc
      · have hz : (fun n => c n / h n ^ γ) = fun _ => 0 := by
          funext n
          simp only [hc n, zero_div]
        rw [hz]
        exact tendsto_const_nhds
      · have hratio := tendsto_rpow_ratio hh hh0
          (show Tendsto (fun _ : ℕ => β) atTop (𝓝 β) from tendsto_const_nhds) hγβ
        have hlim := hc.mul hratio
        simp only [mul_zero] at hlim
        convert hlim using 1
        funext n
        field_simp [ne_of_gt (Real.rpow_pos_of_pos (hh n) β)]
    have hpout : ∀ j ∉ U, p₀ j ≤ γ := by
      intro j hj
      obtain ⟨s, d, hd, hs, ha⟩ := hcomp j hj
      exact unraised_exponent_le hh hh0 hp hr hcγ hd hγβ hpU hs ha
    exact error_of_raised_and_unraised (U := (↑U : Set ι))
      herrU hrout (fun i _ => hlo i) hpout hγε

end Problem326.FixedMinimum

end

end OAI

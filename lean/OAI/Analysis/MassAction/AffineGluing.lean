import Mathlib

namespace OAI

universe uAlpha uIota

noncomputable section

open Filter Asymptotics
open scoped BigOperators Topology

namespace Problem326.AffineGluing

/-- A positive comparison scale dominates a finite affine error that is little-o of it. -/
theorem eventually_pos_sum_add_scale {α : Type uAlpha} {ι : Type uIota} [Fintype ι]
    {l : Filter α} {x : ι → α → ℝ} {c s : α → ℝ} (a : ι → ℝ)
    (hs : ∀ᶠ n in l, 0 < s n) (hc : c =o[l] s)
    (hx : ∀ i, x i =o[l] s) :
    ∀ᶠ n in l, 0 < (∑ i, a i * x i n) + c n + s n := by
  classical
  have hsum : (fun n => ∑ i, a i * x i n) =o[l] s := by
    exact IsLittleO.fun_sum (fun i _ => (hx i).const_mul_left (a i))
  have herr := (hsum.add hc).eventuallyLT_norm_of_eventually_pos
    (hs.mono fun n hn => by simpa only [Real.norm_eq_abs, abs_of_pos hn] using hn)
  filter_upwards [hs, herr] with n hn he
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hn] at he
  have := (abs_lt.mp he).1
  linarith

/-- One positive coordinate contribution that dominates the comparison scale also
    dominates all nonnegative remaining contributions and a little-o offset. -/
theorem eventually_pos_sum_add_sub_scale {α : Type uAlpha} {ι : Type uIota} [Fintype ι]
    {l : Filter α} {x : ι → α → ℝ} {c s : α → ℝ} (a : ι → ℝ) (j : ι)
    (ha : ∀ i, 0 ≤ a i) (haj : 0 < a j)
    (hs : ∀ᶠ n in l, 0 < s n) (hc : c =o[l] s)
    (hx : ∀ᶠ n in l, ∀ i, 0 ≤ x i n)
    (hj : Tendsto (fun n => x j n / s n) l atTop) :
    ∀ᶠ n in l, 0 < (∑ i, a i * x i n) + c n - s n := by
  classical
  have hlarge := hj.eventually_gt_atTop (3 / a j)
  filter_upwards [hs, hc.eventuallyLE, hx, hlarge] with n hn he hx hlarge
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hn] at he
  have hcoord : 3 * s n < a j * x j n := by
    have h := (lt_div_iff₀ hn).mp hlarge
    have h' := mul_lt_mul_of_pos_left h haj
    field_simp at h'
    nlinarith
  have hsum : a j * x j n ≤ ∑ i, a i * x i n := by
    exact Finset.single_le_sum (fun i _ => mul_nonneg (ha i) (hx i)) (Finset.mem_univ j)
  have he' := (abs_le.mp he).1
  linarith

/-- The upper comparison in affine gluing forces some limiting exponent below the cut.
    The asymptotic hypotheses are exactly the variable-exponent power estimates. -/
theorem active_upper_cut {ι : Type uIota} [Fintype ι]
    {x : ι → ℕ → ℝ} {c s : ℕ → ℝ} (a p : ι → ℝ) (q : ℝ)
    (hs : ∀ᶠ n in atTop, 0 < s n) (hc : c =o[atTop] s)
    (hgap : ∀ i, q < p i → x i =o[atTop] s)
    (hactive : ∀ᶠ n in atTop, (∑ i, a i * x i n) + c n + s n ≤ 0) :
    ∃ i, p i ≤ q := by
  classical
  by_contra h
  have hp : ∀ i, q < p i := by simpa only [not_exists, not_le] using h
  have hpos := eventually_pos_sum_add_scale a hs hc (fun i => hgap i (hp i))
  obtain ⟨n, hn, hn'⟩ := (hpos.and hactive).exists
  exact (not_lt_of_ge hn') hn

/-- The lower comparison in affine gluing forces every limiting exponent above the cut. -/
theorem active_lower_cut {ι : Type uIota} [Fintype ι]
    {x : ι → ℕ → ℝ} {c s : ℕ → ℝ} (a p : ι → ℝ) (q : ℝ)
    (ha : ∀ i, 0 < a i)
    (hs : ∀ᶠ n in atTop, 0 < s n) (hc : c =o[atTop] s)
    (hx : ∀ᶠ n in atTop, ∀ i, 0 ≤ x i n)
    (hgap : ∀ i, p i < q → Tendsto (fun n => x i n / s n) atTop atTop)
    (hactive : ∀ᶠ n in atTop, (∑ i, a i * x i n) + c n - s n ≤ 0) :
    ∀ i, q ≤ p i := by
  intro i
  by_contra hi
  have hpos := eventually_pos_sum_add_sub_scale a i (fun j => (ha j).le)
    (ha i) hs hc hx (hgap i (lt_of_not_ge hi))
  obtain ⟨n, hn, hn'⟩ := (hpos.and hactive).exists
  exact (not_lt_of_ge hn') hn

/-- A supported version of the upper comparison: coordinates with zero coefficient
    need no asymptotic control. This is useful in the fixed-minimum induction. -/
theorem active_upper_cut_on_support {ι : Type uIota} [Fintype ι]
    {x : ι → ℕ → ℝ} {c s : ℕ → ℝ} (a p : ι → ℝ) (q : ℝ)
    (hs : ∀ᶠ n in atTop, 0 < s n) (hc : c =o[atTop] s)
    (hgap : ∀ i, a i ≠ 0 → q < p i → x i =o[atTop] s)
    (hactive : ∀ᶠ n in atTop, (∑ i, a i * x i n) + c n + s n ≤ 0) :
    ∃ i, a i ≠ 0 ∧ p i ≤ q := by
  classical
  by_contra h
  have hp : ∀ i, a i ≠ 0 → q < p i := by
    intro i hi
    exact lt_of_not_ge (fun hpi => h ⟨i, hi, hpi⟩)
  have hterm : ∀ i, (fun n => a i * x i n) =o[atTop] s := by
    intro i
    by_cases hi : a i = 0
    · simpa only [hi, zero_mul] using (isLittleO_zero s atTop)
    · exact (hgap i hi (hp i hi)).const_mul_left (a i)
  have hsum : (fun n => ∑ i, a i * x i n) =o[atTop] s := by
    exact IsLittleO.fun_sum (fun i _ => hterm i)
  have herr := (hsum.add hc).eventuallyLT_norm_of_eventually_pos
    (hs.mono fun n hn => by simpa only [Real.norm_eq_abs, abs_of_pos hn] using hn)
  obtain ⟨n, hn, he, hact⟩ := (hs.and (herr.and hactive)).exists
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hn] at he
  have := (abs_lt.mp he).1
  linarith

/-- With nonnegative contributions, only strictly positive coefficients force a
    lower bound on the corresponding limiting exponent. -/
theorem active_nonnegative_lower_cut {ι : Type uIota} [Fintype ι]
    {x : ι → ℕ → ℝ} {c s : ℕ → ℝ} (a p : ι → ℝ) (q : ℝ)
    (ha : ∀ i, 0 ≤ a i)
    (hs : ∀ᶠ n in atTop, 0 < s n) (hc : c =o[atTop] s)
    (hx : ∀ᶠ n in atTop, ∀ i, 0 ≤ x i n)
    (hgap : ∀ i, p i < q → Tendsto (fun n => x i n / s n) atTop atTop)
    (hactive : ∀ᶠ n in atTop, (∑ i, a i * x i n) + c n - s n ≤ 0) :
    ∀ i, 0 < a i → q ≤ p i := by
  intro i hi
  by_contra hpi
  have hpos := eventually_pos_sum_add_sub_scale a i ha hi hs hc hx
    (hgap i (lt_of_not_ge hpi))
  obtain ⟨n, hn, hn'⟩ := (hpos.and hactive).exists
  exact (not_lt_of_ge hn') hn

/-- Common offset shifts preserve all comparisons inside a local family. -/
theorem common_shift_comparison (a b shift : ℝ) :
    a - shift ≤ b - shift ↔ a ≤ b := sub_le_sub_iff_right shift

theorem shifted_active_upper_cut {ι : Type uIota} [Fintype ι]
    {x : ι → ℕ → ℝ} {c : ℕ → ℝ} (scale : ℕ → ℕ → ℝ)
    (r p : ι → ℝ) (next q : ℝ) (j : ℕ)
    (hs : ∀ᶠ n in atTop, 0 < scale j n) (hc : c =o[atTop] scale j)
    (hgap : ∀ i, q < p i → x i =o[atTop] scale j)
    (hactive : ∀ᶠ n in atTop,
      (∑ i, r i * x i n) + c n - (∑ k ∈ Finset.range j, scale k n) ≤
      (∑ i, next * x i n) - (∑ k ∈ Finset.range (j + 1), scale k n)) :
    ∃ i, p i ≤ q := by
  apply active_upper_cut (fun i => r i - next) p q hs hc hgap
  filter_upwards [hactive] with n hn
  simp only [Finset.sum_range_succ, sub_mul, Finset.sum_sub_distrib] at hn ⊢
  linarith

theorem shifted_active_lower_cut {ι : Type uIota} [Fintype ι]
    {x : ι → ℕ → ℝ} {c : ℕ → ℝ} (scale : ℕ → ℕ → ℝ)
    (r p : ι → ℝ) (prev q : ℝ) (j : ℕ)
    (hr : ∀ i, prev < r i)
    (hs : ∀ᶠ n in atTop, 0 < scale j n) (hc : c =o[atTop] scale j)
    (hx : ∀ᶠ n in atTop, ∀ i, 0 ≤ x i n)
    (hgap : ∀ i, p i < q →
      Tendsto (fun n => x i n / scale j n) atTop atTop)
    (hactive : ∀ᶠ n in atTop,
      (∑ i, r i * x i n) + c n - (∑ k ∈ Finset.range (j + 1), scale k n) ≤
      (∑ i, prev * x i n) - (∑ k ∈ Finset.range j, scale k n)) :
    ∀ i, q ≤ p i := by
  apply active_lower_cut (fun i => r i - prev) p q (fun i => sub_pos.mpr (hr i))
    hs hc hx hgap
  filter_upwards [hactive] with n hn
  simp only [Finset.sum_range_succ, sub_mul, Finset.sum_sub_distrib] at hn ⊢
  linarith

end Problem326.AffineGluing

end

end OAI

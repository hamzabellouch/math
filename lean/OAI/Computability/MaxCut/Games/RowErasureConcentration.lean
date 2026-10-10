import Mathlib
import OAI.Computability.MaxCut.Games.AffineWitness

namespace OAI

noncomputable section

namespace MaxCutGames.Inverse.RowErasure

open scoped BigOperators Classical

theorem table_expect_prod {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → ℝ) :
    Finset.univ.expect (fun r : X → Y => ∏ x, f x (r x)) =
      ∏ x, Finset.univ.expect (f x) := by
  classical
  simp only [Fintype.expect_eq_sum_div_card, ← Fintype.prod_sum,
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fun, Nat.cast_pow]

private theorem exp_half_le_seven_quarters_inline_RowErasureConcentration : Real.exp (1 / 2 : ℝ) ≤ 7 / 4 := by
  have h := Real.exp_bound' (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

private theorem exp_half_indicator_inline_RowErasureConcentration (P : Prop) :
    Real.exp (indicator P / 2) = 1 + (Real.exp (1 / 2 : ℝ) - 1) * indicator P := by
  classical
  by_cases h : P <;> simp [indicator, h]

theorem table_coordinate_exp_le {Y : Type*} [Fintype Y] [Nonempty Y]
    (P : Prop) (target : Y) :
    Finset.univ.expect (fun y => Real.exp (indicator (P ∧ y = target) / 2)) ≤
      Real.exp (3 / (4 * (Fintype.card Y : ℝ))) := by
  classical
  have hcard : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.mpr Fintype.card_pos
  by_cases hP : P
  · have hsingle : Finset.univ.expect (fun y : Y => indicator (y = target)) =
        1 / (Fintype.card Y : ℝ) := by
      simp [indicator]
    have heq : Finset.univ.expect
        (fun y => Real.exp (indicator (P ∧ y = target) / 2)) =
        1 + (Real.exp (1 / 2 : ℝ) - 1) / (Fintype.card Y : ℝ) := by
      simp_rw [hP, true_and, exp_half_indicator_inline_RowErasureConcentration]
      rw [Finset.expect_add_distrib, ← Finset.mul_expect, hsingle]
      simp [div_eq_mul_inv]
    rw [heq]
    calc
      1 + (Real.exp (1 / 2 : ℝ) - 1) / (Fintype.card Y : ℝ) ≤
          1 + 3 / (4 * (Fintype.card Y : ℝ)) := by
        have h := div_le_div_of_nonneg_right
          (show Real.exp (1 / 2 : ℝ) - 1 ≤ 3 / 4 by
            linarith [exp_half_le_seven_quarters_inline_RowErasureConcentration]) hcard.le
        simpa only [div_div, add_comm] using add_le_add_left h 1
      _ ≤ Real.exp (3 / (4 * (Fintype.card Y : ℝ))) := by
        simpa only [add_comm] using Real.add_one_le_exp (3 / (4 * (Fintype.card Y : ℝ)))
  · simp only [hP, false_and, indicator_false, zero_div, Real.exp_zero,
      Fintype.expect_const]
    exact Real.one_le_exp (by positivity)

def randomizedMatches {X Y : Type*} (s : Finset X) (B : X → Prop)
    (target replacement : X → Y) : ℝ :=
  ∑ x ∈ s, indicator (B x ∧ replacement x = target x)

private theorem randomizedMatches_eq_masked_sum_inline_RowErasureTail
    {X Y : Type*} [Fintype X] (s : Finset X) (B : X → Prop)
    (target replacement : X → Y) :
    randomizedMatches s B target replacement =
      ∑ x, indicator (x ∈ s ∧ B x ∧ replacement x = target x) := by
  classical
  symm
  calc
    (∑ x, indicator (x ∈ s ∧ B x ∧ replacement x = target x)) =
        ∑ x ∈ s, indicator (x ∈ s ∧ B x ∧ replacement x = target x) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro x _ hx
      simp [indicator, hx]
    _ = randomizedMatches s B target replacement := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [indicator, hx]

private theorem randomizedMatches_exp_product_inline_RowErasureTail
    {X Y : Type*} [Fintype X] (s : Finset X) (B : X → Prop)
    (target replacement : X → Y) :
    Real.exp (randomizedMatches s B target replacement / 2) =
      ∏ x, Real.exp (indicator (x ∈ s ∧ B x ∧ replacement x = target x) / 2) := by
  rw [randomizedMatches_eq_masked_sum_inline_RowErasureTail]
  simp only [div_eq_mul_inv, Finset.sum_mul, Real.exp_sum]

private theorem table_randomizedMatches_mgf_eq_inline_RowErasureTail
    {X Y : Type*} [Fintype X] [Fintype Y]
    (s : Finset X) (B : X → Prop) (target : X → Y) :
    Finset.univ.expect (fun replacement : X → Y =>
      Real.exp (randomizedMatches s B target replacement / 2)) =
      ∏ x, Finset.univ.expect (fun y : Y =>
        Real.exp (indicator (x ∈ s ∧ B x ∧ y = target x) / 2)) := by
  classical
  calc
    _ = Finset.univ.expect (fun replacement : X → Y =>
        ∏ x, Real.exp (indicator (x ∈ s ∧ B x ∧ replacement x = target x) / 2)) := by
      apply Finset.expect_congr rfl
      intro replacement _
      exact randomizedMatches_exp_product_inline_RowErasureTail s B target replacement
    _ = _ := table_expect_prod (X := X) (Y := Y)
      (fun x y => Real.exp (indicator (x ∈ s ∧ B x ∧ y = target x) / 2))

private theorem table_randomizedMatches_product_le_inline_RowErasureTail
    {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Y]
    (s : Finset X) (B : X → Prop) (target : X → Y) :
    (∏ x, Finset.univ.expect (fun y : Y =>
      Real.exp (indicator (x ∈ s ∧ B x ∧ y = target x) / 2))) ≤
      Real.exp (3 / (4 * (Fintype.card Y : ℝ)) * s.card) := by
  classical
  let c : ℝ := 3 / (4 * (Fintype.card Y : ℝ))
  have hpoint : ∀ x : X,
      Finset.univ.expect (fun y : Y =>
        Real.exp (indicator (x ∈ s ∧ B x ∧ y = target x) / 2)) ≤
      Real.exp (if x ∈ s then c else 0) := by
    intro x
    by_cases hx : x ∈ s
    · simpa only [hx, true_and, ite_true] using table_coordinate_exp_le (B x) (target x)
    · simp [hx, indicator]
  calc
    (∏ x, Finset.univ.expect (fun y : Y =>
        Real.exp (indicator (x ∈ s ∧ B x ∧ y = target x) / 2))) ≤
        ∏ x, Real.exp (if x ∈ s then c else 0) := by
      apply Finset.prod_le_prod₀
      · intro x _
        exact Finset.expect_nonneg fun _ _ => (Real.exp_pos _).le
      · intro x _
        exact hpoint x
    _ = Real.exp (3 / (4 * (Fintype.card Y : ℝ)) * s.card) := by
      rw [← Real.exp_sum]
      congr 1
      simp [c, mul_comm]

theorem table_randomizedMatches_mgf_le
    {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Y]
    (s : Finset X) (B : X → Prop) (target : X → Y) :
    Finset.univ.expect (fun replacement : X → Y =>
      Real.exp (randomizedMatches s B target replacement / 2)) ≤
      Real.exp (3 / (4 * (Fintype.card Y : ℝ)) * s.card) := by
  rw [table_randomizedMatches_mgf_eq_inline_RowErasureTail]
  exact table_randomizedMatches_product_le_inline_RowErasureTail s B target

theorem uniformMass_mono {R : Type*} [Fintype R]
    {p q : R → Prop} (h : ∀ r, p r → q r) : uniformMass p ≤ uniformMass q := by
  classical
  apply Finset.expect_le_expect
  intro r _
  by_cases hp : p r
  · simp [indicator, hp, h r hp]
  · simpa [indicator, hp] using indicator_nonneg (q r)

/-- A full uniform table supplies independent coordinate samples. Only the
entries in `B ∩ s` contribute; all other entries deterministically contribute 0. -/
theorem table_randomizedMatches_tail_le
    {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Y]
    (s : Finset X) (B : X → Prop) (target : X → Y)
    (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1)
    (hsmall : 1 / (Fintype.card Y : ℝ) ≤ α / 8) :
    uniformMass (fun replacement : X → Y =>
      α * s.card / 4 ≤ randomizedMatches s B target replacement) ≤
      Real.exp (-(α ^ 2 * s.card) / 32) := by
  classical
  let N : ℝ := s.card
  let c : ℝ := 3 / (4 * (Fintype.card Y : ℝ))
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hp : ∀ replacement : X → Y,
      indicator (α * s.card / 4 ≤ randomizedMatches s B target replacement) ≤
        Real.exp (-(α * N) / 8) *
          Real.exp (randomizedMatches s B target replacement / 2) := by
    intro replacement
    by_cases h : α * s.card / 4 ≤ randomizedMatches s B target replacement
    · rw [show indicator (α * s.card / 4 ≤ randomizedMatches s B target replacement) = 1
          from by simp [indicator, h], ← Real.exp_add]
      apply Real.one_le_exp
      dsimp [N]
      linarith
    · simp only [indicator, ite_eq_right h]
      positivity
  have hm := Finset.expect_le_expect (s := Finset.univ) (fun replacement _ => hp replacement)
  change uniformMass _ ≤ _ at hm
  rw [← Finset.mul_expect] at hm
  have hmgf := table_randomizedMatches_mgf_le s B target
  have hc : c ≤ 3 * α / 32 := by
    dsimp [c]
    calc
      3 / (4 * (Fintype.card Y : ℝ)) = (3 / 4) * (1 / (Fintype.card Y : ℝ)) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ 3 * α / 32 := by nlinarith [hsmall]
  have hexponent : -(α * N) / 8 + c * N ≤ -(α ^ 2 * N) / 32 := by
    have hcN := mul_le_mul_of_nonneg_right hc hN
    have hsq : α ^ 2 ≤ α := by
      nlinarith [mul_nonneg hα.le (sub_nonneg.mpr hαone)]
    have hsqN := mul_le_mul_of_nonneg_right hsq hN
    nlinarith
  calc
    uniformMass (fun replacement : X → Y =>
        α * s.card / 4 ≤ randomizedMatches s B target replacement) ≤
        Real.exp (-(α * N) / 8) *
          Finset.univ.expect (fun replacement : X → Y =>
            Real.exp (randomizedMatches s B target replacement / 2)) := hm
    _ ≤ Real.exp (-(α * N) / 8) * Real.exp (c * N) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = Real.exp (-(α * N) / 8 + c * N) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-(α ^ 2 * s.card) / 32) := Real.exp_le_exp.mpr hexponent

/-- The per-description bound used by the simultaneous erasure union bound. -/
theorem SliceFamily.randomizedAgreement_probability_le
    {X Y A S D : Type*} [Fintype X] [Fintype Y] [Nonempty Y]
    (F : SliceFamily X Y A S D) (B : X → Prop) (α : ℝ)
    (hα : 0 < α) (hαone : α ≤ 1)
    (hsmall : 1 / (Fintype.card Y : ℝ) ≤ α / 8) (d : D) :
    uniformMass (fun replacement : X → Y =>
      (F.points d).Nonempty ∧ α / 4 ≤ F.randomizedAgreement B replacement d) ≤
      Real.exp (-(α ^ 2 * (F.points d).card) / 32) := by
  apply le_trans (uniformMass_mono ?_) (table_randomizedMatches_tail_le
    (F.points d) B (F.target d) α hα hαone hsmall)
  intro replacement h
  have hcard : (0 : ℝ) < (F.points d).card := Nat.cast_pos.mpr h.1.card_pos
  have hmass := h.2
  rw [SliceFamily.randomizedAgreement, Finset.expect_eq_sum_div_card] at hmass
  have hm := (le_div_iff₀ hcard).mp hmass
  dsimp [randomizedMatches]
  nlinarith

end MaxCutGames.Inverse.RowErasure

namespace MaxCutGames.Inverse.RowErasureMatrix

open MaxCutGames.Inverse.Shortcode
open MaxCutGames.Inverse.RowErasure
open MaxCutGames.Inverse.RowErasureDescriptions
open scoped BigOperators

/-- One replacement table simultaneously defeats every padded slice/target.
The budget depends only on dimensions and α, not on the labeling or erased set. -/
theorem exists_replacement_of_budget {ell m r : ℕ}
    (B : Mat ell m → Prop) (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1)
    (halphabet : 1 / (2 ^ ell : ℝ) ≤ α / 8)
    (hbudget : (2 : ℝ) ^ ((2 * r + 1) * (ell + m)) *
      Real.exp (-(α ^ 2 * (2 : ℝ) ^ ((ell - r) * (m - r))) / 32) < 1) :
    ∃ replacement : Mat ell m → Vector ell,
      ∀ d : Description ell m r, ((family ell m r).points d).Nonempty →
        (family ell m r).randomizedAgreement B replacement d < α / 4 := by
  let ρ := Real.exp (-(α ^ 2 * (2 : ℝ) ^ ((ell - r) * (m - r))) / 32)
  apply (family ell m r).exists_erasure_of_probability_bound B α ρ
  · intro d
    by_cases hne : ((family ell m r).points d).Nonempty
    · have htail := (family ell m r).randomizedAgreement_probability_le B α hα hαone
        (by simpa only [card_vector, Nat.cast_pow, Nat.cast_ofNat] using halphabet) d
      have hcardNat := d.toSlice.pow_dimension_le_card r le_rfl le_rfl hne
      have hcard : (2 : ℝ) ^ ((ell - r) * (m - r)) ≤
          (((family ell m r).points d).card : ℝ) := by
        exact_mod_cast hcardNat
      apply htail.trans
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hcard (sq_nonneg α)
      linarith
    · simpa [uniformMass, indicator, hne] using (Real.exp_pos
        (-(α ^ 2 * (2 : ℝ) ^ ((ell - r) * (m - r))) / 32)).le
  · simpa only [card_description, Nat.cast_pow, Nat.cast_ofNat] using hbudget

/-- Finite product concentration and concrete slice counts discharge the
random-erasure obligation under the inverse hypothesis. -/
theorem advice_mass_ge_of_inverse_and_budget {ell m r : ℕ}
    (f : Mat ell m → Vector ell) (η α : ℝ) (hη : 0 < η)
    (hα : 0 < α) (hαone : α ≤ 1)
    (halphabet : 1 / (2 ^ ell : ℝ) ≤ α / 8)
    (haccept : 4 * η ≤ Shortcode.equalityAcceptance f)
    (inverse : ∀ g : Mat ell m → Vector ell,
      η ≤ Shortcode.equalityAcceptance g → HasAffineSlice g α r)
    (hbudget : (2 : ℝ) ^ ((2 * r + 1) * (ell + m)) *
      Real.exp (-(α ^ 2 * (2 : ℝ) ^ ((ell - r) * (m - r))) / 32) < 1) :
    η / (2 ^ (ell * r) : ℝ) ≤ adviceMass ((family ell m r).goodAt f α) := by
  exact advice_mass_ge_of_inverse_and_erasure f η α hη hα haccept inverse
    (exists_replacement_of_budget ((family ell m r).erasedUnion f α)
      α hα hαone halphabet hbudget)

end MaxCutGames.Inverse.RowErasureMatrix

/-!
The row-erasure union bound is eventually strictly below one. The number of
descriptions grows exponentially in `m`, while the tail exponent grows as
`2 ^ ((ell-r)*(m-r))`. The only asymptotic input is the standard proved limit
that a fixed polynomial divided by `2^n` tends to zero.
-/

namespace MaxCutGames.Inverse.RowErasure

open Filter
open scoped Topology

/-- Logarithm of the finite union-bound estimate, for every sufficiently large
column dimension. Neither the threshold nor the proof depends on a parity
condition on the column dimension. -/
theorem eventually_log_unionBound_neg (α : ℝ) (hα : 0 < α)
    (ell r : ℕ) (hr : r < ell) :
    ∀ᶠ m : ℕ in atTop,
      (((2 * r + 1) * (ell + m) : ℕ) : ℝ) * Real.log 2 -
        α ^ 2 * (2 : ℝ) ^ ((ell - r) * (m - r)) / 32 < 0 := by
  let C : ℝ := (2 * r + 1 : ℕ)
  let D : ℝ := (ell + r : ℕ)
  have hzero : Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [pow_zero] using
      (tendsto_pow_const_div_const_pow_of_one_lt 0 (show (1 : ℝ) < 2 by norm_num))
  have hone : Tendsto (fun n : ℕ => (n : ℝ) / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [pow_one] using
      (tendsto_pow_const_div_const_pow_of_one_lt 1 (show (1 : ℝ) < 2 by norm_num))
  have hlim' : Tendsto
      (fun n : ℕ => (C * Real.log 2) * (D * (1 / (2 : ℝ) ^ n) +
        (n : ℝ) / (2 : ℝ) ^ n)) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      ((hzero.const_mul D).add hone).const_mul (C * Real.log 2)
  have hlim : Tendsto
      (fun n : ℕ => C * (D + (n : ℝ)) * Real.log 2 / (2 : ℝ) ^ n)
      atTop (𝓝 0) := by
    convert hlim' using 1
    ext n
    ring
  have hpos : 0 < α ^ 2 / 32 := by positivity
  have hsmall : ∀ᶠ n : ℕ in atTop,
      C * (D + (n : ℝ)) * Real.log 2 / (2 : ℝ) ^ n < α ^ 2 / 32 :=
    hlim.eventually (gt_mem_nhds hpos)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  apply eventually_atTop.2
  refine ⟨N + r, ?_⟩
  intro m hm
  have hrm : r ≤ m := by omega
  have hn : N ≤ m - r := by omega
  have hmcast : (m : ℝ) = (r : ℝ) + ((m - r : ℕ) : ℝ) := by
    exact_mod_cast (show m = r + (m - r) by omega)
  have hcast : (((2 * r + 1) * (ell + m) : ℕ) : ℝ) =
      C * (D + ((m - r : ℕ) : ℝ)) := by
    dsimp [C, D]
    push_cast
    rw [hmcast]
    ring
  have hlinear := (div_lt_iff₀ (show (0 : ℝ) < 2 ^ (m - r) by positivity)).1
    (hN (m - r) hn)
  have hexponent : m - r ≤ (ell - r) * (m - r) := by
    have h := Nat.mul_le_mul_right (m - r) (show 1 ≤ ell - r by omega)
    simpa only [one_mul] using h
  have hpower : (2 : ℝ) ^ (m - r) ≤ 2 ^ ((ell - r) * (m - r)) :=
    pow_le_pow_right₀ (by norm_num) hexponent
  have hproduct := mul_le_mul_of_nonneg_left hpower hpos.le
  rw [hcast]
  nlinarith

/-- The exact description-count times tail estimate needed for simultaneous
row erasure is strictly below one in all sufficiently large dimensions. -/
theorem eventually_unionBound_lt_one (α : ℝ) (hα : 0 < α)
    (ell r : ℕ) (hr : r < ell) :
    ∀ᶠ m : ℕ in atTop,
      (2 : ℝ) ^ ((2 * r + 1) * (ell + m)) *
        Real.exp (-(α ^ 2) * (2 : ℝ) ^ ((ell - r) * (m - r)) / 32) < 1 := by
  filter_upwards [eventually_log_unionBound_neg α hα ell r hr] with m hm
  have hpositive : (0 : ℝ) < 2 ^ ((2 * r + 1) * (ell + m)) := by positivity
  calc
    (2 : ℝ) ^ ((2 * r + 1) * (ell + m)) *
        Real.exp (-(α ^ 2) * (2 : ℝ) ^ ((ell - r) * (m - r)) / 32) =
        Real.exp ((((2 * r + 1) * (ell + m) : ℕ) : ℝ) * Real.log 2 -
          α ^ 2 * (2 : ℝ) ^ ((ell - r) * (m - r)) / 32) := by
      rw [← Real.exp_log hpositive, ← Real.exp_add, Real.log_pow]
      congr 1
      ring
    _ < 1 := Real.exp_lt_one_iff.mpr hm

/-- A threshold usable by dimension-selection arguments, with enough columns
to accommodate all `r` prescribed column constraints. -/
theorem exists_unionBound_threshold (α : ℝ) (hα : 0 < α)
    (ell r : ℕ) (hr : r < ell) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → r ≤ m ∧
      (2 : ℝ) ^ ((2 * r + 1) * (ell + m)) *
        Real.exp (-(α ^ 2) * (2 : ℝ) ^ ((ell - r) * (m - r)) / 32) < 1 := by
  exact eventually_atTop.1 ((eventually_ge_atTop r).and
    (eventually_unionBound_lt_one α hα ell r hr))

end MaxCutGames.Inverse.RowErasure

namespace MaxCutGames.Inverse.RowErasureMatrix

open MaxCutGames.Inverse.Shortcode
open MaxCutGames.Inverse.RowErasure
open MaxCutGames.Inverse.RowErasureDescriptions
open scoped BigOperators

/-- A single dimension threshold supplies replacements for every erased set.
There is no inverse-theorem premise in this concentration/counting statement. -/
theorem exists_erasure_threshold (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1)
    (ell r : ℕ) (hr : r < ell) (halphabet : 1 / (2 ^ ell : ℝ) ≤ α / 8) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ B : Mat ell m → Prop,
        ∃ replacement : Mat ell m → Vector ell,
          ∀ d : Description ell m r, ((family ell m r).points d).Nonempty →
            (family ell m r).randomizedAgreement B replacement d < α / 4 := by
  obtain ⟨m₀, hm₀⟩ := exists_unionBound_threshold α hα ell r hr
  refine ⟨m₀, ?_⟩
  intro m hm B
  apply exists_replacement_of_budget B α hα hαone halphabet
  simpa only [neg_mul] using (hm₀ m hm).2

/-- For sufficiently many columns, every accepted function has a positive
measure of good row advice, assuming the genuine bounded-slice inverse. -/
theorem exists_fixed_context_advice_threshold (η α : ℝ)
    (hη : 0 < η) (hα : 0 < α) (hαone : α ≤ 1)
    (ell r : ℕ) (hr : r < ell) (halphabet : 1 / (2 ^ ell : ℝ) ≤ α / 8) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      (∀ g : Mat ell m → Vector ell,
        η ≤ Shortcode.equalityAcceptance g → HasAffineSlice g α r) →
      ∀ f : Mat ell m → Vector ell,
        4 * η ≤ Shortcode.equalityAcceptance f →
          η / (2 ^ (ell * r) : ℝ) ≤ adviceMass ((family ell m r).goodAt f α) := by
  obtain ⟨m₀, hm₀⟩ := exists_erasure_threshold α hα hαone ell r hr halphabet
  refine ⟨m₀, ?_⟩
  intro m hm inverse f haccept
  exact advice_mass_ge_of_inverse_and_erasure f η α hη hα haccept inverse
    (hm₀ m hm ((family ell m r).erasedUnion f α))

theorem exists_contextual_advice_threshold (η α : ℝ)
    (hη : 0 < η) (hα : 0 < α) (hαone : α ≤ 1)
    (ell r : ℕ) (hr : r < ell) (halphabet : 1 / (2 ^ ell : ℝ) ≤ α / 8) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      (∀ g : Mat ell m → Vector ell,
        η ≤ Shortcode.equalityAcceptance g → HasAffineSlice g α r) →
      ∀ (Q : Type) [Fintype Q] (f : Q → Mat ell m → Vector ell),
        10 * η ≤ uniformMass (fun q => 4 * η ≤ Shortcode.equalityAcceptance (f q)) →
          10 * η ^ 2 / (2 ^ (ell * r) : ℝ) ≤
            Finset.univ.expect (fun q => adviceMass ((family ell m r).goodAt (f q) α)) := by
  obtain ⟨m₀, hm₀⟩ := exists_erasure_threshold α hα hαone ell r hr halphabet
  refine ⟨m₀, ?_⟩
  intro m hm inverse Q _ f hcontext
  have hlocal : ∀ q : Q, 4 * η ≤ Shortcode.equalityAcceptance (f q) →
      η ≤ uniformMass (goodUnion ((family ell m r).goodAt (f q) α)) := by
    intro q hq
    exact (family ell m r).union_mass_ge_of_inverse_and_erasure
      left right (f q) η α hη hα
      (by simpa only [acceptance_eq] using hq)
      left_uniform right_uniform (described_inverse α η inverse)
      (hm₀ m hm ((family ell m r).erasedUnion (f q) α))
  have h := advice_average_ge_ten_eta_sq_div_card
    (fun q => 4 * η ≤ Shortcode.equalityAcceptance (f q))
    (fun q => (family ell m r).goodAt (f q) α) η hη.le hcontext hlocal
  simpa only [card_rowMap, Nat.cast_pow, Nat.cast_ofNat] using h

end MaxCutGames.Inverse.RowErasureMatrix

end

end OAI

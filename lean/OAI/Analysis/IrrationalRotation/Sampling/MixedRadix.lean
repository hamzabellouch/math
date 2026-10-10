import OAI.Analysis.IrrationalRotation.Model.MixedRadix
import OAI.Analysis.IrrationalRotation.Analysis.ParameterTails
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Tactic

namespace OAI

open Filter
open scoped Topology

namespace Invariant233.MixedRadix

@[simp] theorem denominator_zero (r : ℕ → ℕ) : denominator r 0 = 1 := by
  simp [denominator]

@[simp] theorem denominator_succ (r : ℕ → ℕ) (n : ℕ) :
    denominator r (n + 1) = denominator r n * r n := by
  simp [denominator, Finset.prod_range_succ]

theorem denominator_pos {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) (n : ℕ) :
    0 < denominator r n := by
  exact Finset.prod_pos (fun i _ => hr i)

theorem term_nonneg {r : ℕ → ℕ} (d : Digits r) (n : ℕ) :
    0 ≤ term d n := by unfold term; positivity

theorem term_le_reciprocal_gap {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (n : ℕ) :
    term d n ≤ 1 / (denominator r n : ℝ) - 1 / (denominator r (n + 1) : ℝ) := by
  have hq : (0 : ℝ) < denominator r n := by exact_mod_cast denominator_pos hr n
  have hrr : (0 : ℝ) < r n := by exact_mod_cast hr n
  have hd : (d n : ℝ) ≤ (r n : ℝ) - 1 := by
    have hh : (d n : ℝ) + 1 ≤ (r n : ℝ) := by exact_mod_cast (d n).isLt
    linarith
  rw [term, denominator_succ, Nat.cast_mul]
  calc
    (d n : ℝ) / ((denominator r n : ℝ) * (r n : ℝ)) ≤
        ((r n : ℝ) - 1) / ((denominator r n : ℝ) * (r n : ℝ)) :=
      div_le_div_of_nonneg_right hd (mul_pos hq hrr).le
    _ = _ := by field_simp

theorem sum_terms_le_reciprocal_gap {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (j N : ℕ) :
    (∑ n ∈ Finset.range N, term d (j + n)) ≤
      1 / (denominator r j : ℝ) - 1 / (denominator r (j + N) : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hterm := term_le_reciprocal_gap hr d (j + N)
      simp only [Nat.add_assoc] at hterm
      linarith

theorem summable_terms {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) (d : Digits r) :
    Summable (term d) := by
  apply summable_of_sum_range_le (term_nonneg d) (c := 1)
  intro N
  have h := sum_terms_le_reciprocal_gap hr d 0 N
  simp only [Nat.zero_add, denominator_zero, Nat.cast_one, div_one] at h
  have hnonneg : (0 : ℝ) ≤ 1 / (denominator r N : ℝ) := by positivity
  linarith

theorem tsum_tail_le {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) (d : Digits r) (j : ℕ) :
    (∑' n, term d (j + n)) ≤ 1 / (denominator r j : ℝ) := by
  apply Real.tsum_le_of_sum_range_le (fun n => term_nonneg d (j + n))
  intro N
  have h := sum_terms_le_reciprocal_gap hr d j N
  have hnonneg : (0 : ℝ) ≤ 1 / (denominator r (j + N) : ℝ) := by positivity
  linarith

theorem ofDigits_nonneg {r : ℕ → ℕ} (d : Digits r) : 0 ≤ ofDigits d :=
  tsum_nonneg (term_nonneg d)

theorem ofDigits_le_one {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) (d : Digits r) :
    ofDigits d ≤ 1 := by
  simpa [ofDigits] using tsum_tail_le hr d 0

theorem tailValue_nonneg {r : ℕ → ℕ} (d : Digits r) (j : ℕ) :
    0 ≤ tailValue d j := by
  unfold tailValue
  exact mul_nonneg (Nat.cast_nonneg _) (tsum_nonneg (fun n => term_nonneg d (j + n)))

theorem tailValue_le_one {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) (d : Digits r) (j : ℕ) :
    tailValue d j ≤ 1 := by
  have hq : (0 : ℝ) < denominator r j := by exact_mod_cast denominator_pos hr j
  calc
    tailValue d j ≤ (denominator r j : ℝ) * (1 / (denominator r j : ℝ)) :=
      mul_le_mul_of_nonneg_left (tsum_tail_le hr d j) hq.le
    _ = 1 := by field_simp

theorem ofDigits_mono {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) {d e : Digits r}
    (hde : ∀ n, d n ≤ e n) : ofDigits d ≤ ofDigits e := by
  apply (summable_terms hr d).tsum_le_tsum _ (summable_terms hr e)
  intro n
  exact div_le_div_of_nonneg_right (by exact_mod_cast hde n) (Nat.cast_nonneg _)

theorem tailValue_mono {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) {d e : Digits r}
    (hde : ∀ n, d n ≤ e n) (j : ℕ) : tailValue d j ≤ tailValue e j := by
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply ((summable_terms hr d).comp_injective (fun _ _ h => Nat.add_left_cancel h)).tsum_le_tsum
    _ ((summable_terms hr e).comp_injective (fun _ _ h => Nat.add_left_cancel h))
  intro n
  exact div_le_div_of_nonneg_right (by exact_mod_cast hde (j + n)) (Nat.cast_nonneg _)

theorem tailValue_rec {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) (d : Digits r) (j : ℕ) :
    tailValue d j = ((d j : ℝ) + tailValue d (j + 1)) / (r j : ℝ) := by
  have hs : Summable (fun n => term d (j + (n + 1))) :=
    (summable_terms hr d).comp_injective (fun _ _ h => by omega)
  have hsplit : (∑' n, term d (j + n)) =
      term d j + ∑' n, term d (j + 1 + n) := by
    simpa only [Nat.add_zero, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using tsum_eq_zero_add' (f := fun n => term d (j + n)) hs
  have hq : (denominator r j : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast denominator_pos hr j)
  have hrr : (r j : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hr j)
  unfold tailValue
  rw [hsplit]
  simp only [term, denominator_succ, Nat.cast_mul]
  field_simp

theorem tailValue_mem_bin {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) (d : Digits r) (j : ℕ) :
    (d j : ℝ) / (r j : ℝ) ≤ tailValue d j ∧
      tailValue d j ≤ ((d j : ℝ) + 1) / (r j : ℝ) := by
  rw [tailValue_rec hr d j]
  constructor
  · exact div_le_div_of_nonneg_right (by linarith [tailValue_nonneg d (j + 1)])
      (Nat.cast_nonneg _)
  · exact div_le_div_of_nonneg_right (by linarith [tailValue_le_one hr d (j + 1)])
      (Nat.cast_nonneg _)

theorem abs_tailValue_sub_raw_le {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (j : ℕ) {X : ℝ}
    (hlo : (d j : ℝ) ≤ (r j : ℝ) * X)
    (hhi : (r j : ℝ) * X ≤ (d j : ℝ) + 1) :
    |tailValue d j - X| ≤ 1 / (r j : ℝ) := by
  have hrr : (0 : ℝ) < r j := by exact_mod_cast hr j
  have hrec := tailValue_rec hr d j
  have heq : (r j : ℝ) * tailValue d j = (d j : ℝ) + tailValue d (j + 1) := by
    rw [hrec]
    field_simp
  rw [abs_sub_le_iff]
  constructor
  · apply (le_div_iff₀ hrr).mpr
    nlinarith [tailValue_le_one hr d (j + 1)]
  · apply (le_div_iff₀ hrr).mpr
    nlinarith [tailValue_nonneg d (j + 1)]

theorem abs_tailValue_sub_raw_le_of_floor {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (j : ℕ) {X : ℝ} (hX : 0 ≤ X)
    (hdigit : ⌊(r j : ℝ) * X⌋₊ = (d j : ℕ)) :
    |tailValue d j - X| ≤ 1 / (r j : ℝ) := by
  have h := (Nat.floor_eq_iff (mul_nonneg (Nat.cast_nonneg _) hX)).mp hdigit
  exact abs_tailValue_sub_raw_le hr d j h.1 h.2.le

theorem ofDigits_eq_prefix_add_tail {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (N : ℕ) :
    ofDigits d = (∑ n ∈ Finset.range N, term d n) + ∑' n, term d (N + n) := by
  simpa only [ofDigits, Nat.add_comm] using
    ((summable_terms hr d).sum_add_tsum_nat_add N).symm

theorem abs_ofDigits_sub_ofDigits_le {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    {d e : Digits r} {N : ℕ} (hde : ∀ n < N, d n = e n) :
    |ofDigits d - ofDigits e| ≤ 1 / (denominator r N : ℝ) := by
  rw [ofDigits_eq_prefix_add_tail hr d N, ofDigits_eq_prefix_add_tail hr e N]
  have heq : (∑ n ∈ Finset.range N, term d n) = ∑ n ∈ Finset.range N, term e n := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [term, hde n (Finset.mem_range.mp hn)]
  rw [heq, add_sub_add_left_eq_sub, abs_sub_le_iff]
  have hd0 : (0 : ℝ) ≤ ∑' n, term d (N + n) :=
    tsum_nonneg (fun n => term_nonneg d (N + n))
  have he0 : (0 : ℝ) ≤ ∑' n, term e (N + n) :=
    tsum_nonneg (fun n => term_nonneg e (N + n))
  constructor <;> linarith [tsum_tail_le hr d N, tsum_tail_le hr e N]

theorem denominator_double {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n) (n : ℕ) :
    2 * (denominator r n : ℝ) ≤ (denominator r (n + 1) : ℝ) := by
  rw [denominator_succ, Nat.cast_mul]
  have hh : (2 : ℝ) ≤ r n := by exact_mod_cast hr n
  nlinarith [Nat.cast_nonneg (α := ℝ) (denominator r n)]

theorem summable_reciprocal_denominator {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n) :
    Summable (fun n => 1 / (denominator r n : ℝ)) := by
  apply ParameterTails.summable_reciprocal
  · intro n
    exact_mod_cast denominator_pos (fun i => lt_of_lt_of_le (by decide : 0 < 2) (hr i)) n
  · exact denominator_double hr

theorem reciprocal_denominator_tendsto_zero {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n) :
    Tendsto (fun n => 1 / (denominator r n : ℝ)) atTop (𝓝 0) :=
  (summable_reciprocal_denominator hr).tendsto_atTop_zero

theorem continuous_ofDigits {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n) :
    Continuous (@ofDigits r) := by
  apply continuous_tsum (u := fun n => 1 / (denominator r n : ℝ))
  · intro n
    have hd : Continuous (fun a : Fin (r n) => (a : ℝ)) := continuous_of_discreteTopology
    exact (hd.comp (continuous_apply n)).div_const _
  · exact summable_reciprocal_denominator hr
  · intro n d
    rw [Real.norm_eq_abs, abs_of_nonneg (term_nonneg d n)]
    have h := term_le_reciprocal_gap
      (fun i => lt_of_lt_of_le (by decide : 0 < 2) (hr i)) d n
    have hnn : (0 : ℝ) ≤ 1 / (denominator r (n + 1) : ℝ) := by positivity
    linarith

theorem tendsto_ofDigits_of_agree_prefix {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n)
    (d : Digits r) (e : ℕ → Digits r) (hde : ∀ N n, n < N → e N n = d n) :
    Tendsto (fun N => ofDigits (e N)) atTop (𝓝 (ofDigits d)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (reciprocal_denominator_tendsto_zero hr)
  · intro N
    exact norm_nonneg _
  · intro N
    simpa only [Real.norm_eq_abs] using abs_ofDigits_sub_ofDigits_le
      (fun i => lt_of_lt_of_le (by decide : 0 < 2) (hr i)) (hde N)

@[simp] theorem prefixRank_zero {r : ℕ → ℕ} (d : Digits r) : prefixRank d 0 = 0 := rfl

@[simp] theorem prefixRank_succ {r : ℕ → ℕ} (d : Digits r) (N : ℕ) :
    prefixRank d (N + 1) = prefixRank d N * r N + (d N : ℕ) := rfl

theorem prefixRank_lt_denominator {r : ℕ → ℕ} (_hr : ∀ n, 0 < r n)
    (d : Digits r) (N : ℕ) : prefixRank d N < denominator r N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [prefixRank_succ, denominator_succ]
      have hd := (d N).isLt
      nlinarith [_hr N]

theorem denominator_mul_prefix {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (N : ℕ) :
    (denominator r N : ℝ) * (∑ n ∈ Finset.range N, term d n) = (prefixRank d N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hq : (denominator r N : ℝ) ≠ 0 :=
        ne_of_gt (by exact_mod_cast denominator_pos hr N)
      have hrr : (r N : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hr N)
      rw [Finset.sum_range_succ, prefixRank_succ, Nat.cast_add, Nat.cast_mul]
      simp only [term, denominator_succ, Nat.cast_mul] at *
      field_simp at *
      nlinarith

theorem denominator_mul_ofDigits {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (N : ℕ) :
    (denominator r N : ℝ) * ofDigits d = (prefixRank d N : ℝ) + tailValue d N := by
  rw [ofDigits_eq_prefix_add_tail hr d N, mul_add, denominator_mul_prefix hr d N]
  rfl

theorem tailValue_eq_one_imp_next {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (j : ℕ) (heq : tailValue d j = 1) :
    tailValue d (j + 1) = 1 := by
  have hrr : (r j : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hr j)
  have hrec := (eq_div_iff hrr).mp (tailValue_rec hr d j)
  have hd : (d j : ℝ) + 1 ≤ (r j : ℝ) := by exact_mod_cast (d j).isLt
  rw [heq, one_mul] at hrec
  linarith [tailValue_le_one hr d (j + 1)]

theorem tailValue_lt_one {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (hnt : Nonterminal d) (j : ℕ) : tailValue d j < 1 := by
  by_contra hnot
  have heq : tailValue d j = 1 := le_antisymm (tailValue_le_one hr d j) (le_of_not_gt hnot)
  have hprop : ∀ k, tailValue d (j + k) = 1 := by
    intro k
    induction k with
    | zero => simpa using heq
    | succ k ih =>
        simpa only [Nat.add_assoc] using tailValue_eq_one_imp_next hr d (j + k) ih
  obtain ⟨n, hjn, hn⟩ := hnt j
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hjn
  have hrr : (r (j + k) : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hr (j + k))
  have hrec := (eq_div_iff hrr).mp (tailValue_rec hr d (j + k))
  rw [hprop k, one_mul] at hrec
  have hd : (d (j + k) : ℝ) + 1 < (r (j + k) : ℝ) := by exact_mod_cast hn
  linarith [tailValue_le_one hr d (j + k + 1)]

theorem fract_denominator_mul_ofDigits {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (hnt : Nonterminal d) (j : ℕ) :
    Int.fract ((denominator r j : ℝ) * ofDigits d) = tailValue d j := by
  rw [denominator_mul_ofDigits hr d j, Int.fract_natCast_add]
  exact Int.fract_eq_self.mpr ⟨tailValue_nonneg d j, tailValue_lt_one hr d hnt j⟩

theorem floor_radix_mul_tailValue {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (hnt : Nonterminal d) (j : ℕ) :
    ⌊(r j : ℝ) * tailValue d j⌋₊ = (d j : ℕ) := by
  have hrr : (r j : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hr j)
  have hrec := (eq_div_iff hrr).mp (tailValue_rec hr d j)
  rw [mul_comm] at hrec
  apply (Nat.floor_eq_iff (mul_nonneg (Nat.cast_nonneg _) (tailValue_nonneg d j))).mpr
  constructor
  · linarith [tailValue_nonneg d (j + 1)]
  · linarith [tailValue_lt_one hr d hnt (j + 1)]

theorem floor_coordinate_recovers_digit {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (hnt : Nonterminal d) (j : ℕ) :
    ⌊(r j : ℝ) * Int.fract ((denominator r j : ℝ) * ofDigits d)⌋₊ = (d j : ℕ) := by
  rw [fract_denominator_mul_ofDigits hr d hnt j]
  exact floor_radix_mul_tailValue hr d hnt j

theorem ofDigits_injective_on_nonterminal {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    {d e : Digits r} (hd : Nonterminal d) (he : Nonterminal e)
    (hde : ofDigits d = ofDigits e) : d = e := by
  funext j
  apply Fin.ext
  rw [← floor_coordinate_recovers_digit hr d hd j,
    ← floor_coordinate_recovers_digit hr e he j, hde]

theorem prefixRank_canonicalDigits {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    {x : ℝ} (hx : x ∈ Set.Ico 0 1) (N : ℕ) :
    prefixRank (canonicalDigits r hr x) N = ⌊(denominator r N : ℝ) * x⌋₊ := by
  induction N with
  | zero => simp [Nat.floor_eq_zero.mpr hx.2]
  | succ N ih =>
      rw [prefixRank_succ, ih]
      change ⌊(denominator r N : ℝ) * x⌋₊ * r N +
        ⌊(denominator r (N + 1) : ℝ) * x⌋₊ % r N = _
      have hdiv : ⌊(denominator r (N + 1) : ℝ) * x⌋₊ / r N =
          ⌊(denominator r N : ℝ) * x⌋₊ := by
        rw [denominator_succ, Nat.cast_mul, mul_right_comm, mul_comm _ (r N : ℝ)]
        exact Nat.cast_mul_floor_div_cancel (ne_of_gt (hr N)) _
      rw [← hdiv]
      exact Nat.div_add_mod' _ _

theorem canonical_prefix_error {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    {x : ℝ} (hx : x ∈ Set.Ico 0 1) (N : ℕ) :
    0 ≤ x - (∑ n ∈ Finset.range N, term (canonicalDigits r hr x) n) ∧
    x - (∑ n ∈ Finset.range N, term (canonicalDigits r hr x) n) <
      1 / (denominator r N : ℝ) := by
  have hq : (0 : ℝ) < denominator r N := by exact_mod_cast denominator_pos hr N
  have hgrid := denominator_mul_prefix hr (canonicalDigits r hr x) N
  rw [prefixRank_canonicalDigits hr hx N] at hgrid
  have hlow := Nat.floor_le (mul_nonneg hq.le hx.1)
  have hhigh := Nat.lt_floor_add_one ((denominator r N : ℝ) * x)
  constructor
  · nlinarith
  · apply (lt_div_iff₀ hq).mpr
    nlinarith

theorem ofDigits_canonicalDigits {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n)
    {x : ℝ} (hx : x ∈ Set.Ico 0 1) :
    ofDigits (canonicalDigits r (fun n => lt_of_lt_of_le (by decide : 0 < 2) (hr n)) x) = x := by
  let hp : ∀ n, 0 < r n := fun n => lt_of_lt_of_le (by decide : 0 < 2) (hr n)
  let d := canonicalDigits r hp x
  have hlim : Tendsto (fun N => ∑ n ∈ Finset.range N, term d n) atTop (𝓝 x) := by
    have hzero : Tendsto (fun N => x - ∑ n ∈ Finset.range N, term d n) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (reciprocal_denominator_tendsto_zero hr)
      · intro N; exact (canonical_prefix_error hp hx N).1
      · intro N; exact (canonical_prefix_error hp hx N).2.le
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)).sub hzero
    simpa using h
  have hs := (summable_terms hp d).hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique hs hlim

theorem prefixRank_congr {r : ℕ → ℕ} {d e : Digits r} (N : ℕ)
    (hde : ∀ n < N, d n = e n) : prefixRank d N = prefixRank e N := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [prefixRank_succ, prefixRank_succ, ih (fun n hn => hde n (by omega)), hde N (by omega)]

theorem prefixRank_eq_iff {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) (d e : Digits r) (N : ℕ) :
    prefixRank d N = prefixRank e N ↔ ∀ n < N, d n = e n := by
  refine ⟨?_, fun h => prefixRank_congr N h⟩
  induction N with
  | zero => intro _ n hn; omega
  | succ N ih =>
      intro heq
      have hlast : d N = e N := by
        apply Fin.ext
        have hmod := congrArg (fun k => k % r N) heq
        simpa [prefixRank_succ, Nat.add_mod, Nat.mul_mod,
          Nat.mod_eq_of_lt (d N).isLt, Nat.mod_eq_of_lt (e N).isLt] using hmod
      have hprev : prefixRank d N = prefixRank e N := by
        rw [prefixRank_succ, prefixRank_succ, hlast] at heq
        exact Nat.eq_of_mul_eq_mul_right (hr N) (Nat.add_right_cancel heq)
      intro n hn
      by_cases hn' : n < N
      · exact ih hprev n hn'
      · have : n = N := by omega
        subst n
        exact hlast

@[simp] theorem extendPrefix_apply_lt {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    {N : ℕ} (d : (i : Fin N) → Fin (r i)) {n : ℕ} (hn : n < N) :
    extendPrefix r hr N d n = d ⟨n, hn⟩ := by
  simp [extendPrefix, hn]

theorem finitePrefixRank_injective {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) (N : ℕ) :
    Function.Injective (fun d : (i : Fin N) → Fin (r i) =>
      prefixRank (extendPrefix r hr N d) N) := by
  intro d e hde
  have h := (prefixRank_eq_iff hr (extendPrefix r hr N d) (extendPrefix r hr N e) N).mp hde
  funext i
  simpa using h i i.isLt

theorem finitePrefixRank_surjective {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (N k : ℕ) (hk : k < denominator r N) :
    ∃ d : (i : Fin N) → Fin (r i), prefixRank (extendPrefix r hr N d) N = k := by
  let x : ℝ := (k : ℝ) / (denominator r N : ℝ)
  have hq : (0 : ℝ) < denominator r N := by exact_mod_cast denominator_pos hr N
  have hx : x ∈ Set.Ico 0 1 := by
    constructor
    · dsimp [x]; positivity
    · apply (div_lt_one hq).mpr
      exact_mod_cast hk
  let d := canonicalDigits r hr x
  refine ⟨fun i => d i, ?_⟩
  calc
    prefixRank (extendPrefix r hr N (fun i => d i)) N = prefixRank d N := by
      apply prefixRank_congr
      intro n hn
      simp [hn]
    _ = ⌊(denominator r N : ℝ) * x⌋₊ := prefixRank_canonicalDigits hr hx N
    _ = k := by
      have hscale : (denominator r N : ℝ) * x = (k : ℝ) := by dsimp [x]; field_simp
      rw [hscale, Nat.floor_natCast]

noncomputable def finitePrefixRankEquiv (r : ℕ → ℕ) (hr : ∀ n, 0 < r n) (N : ℕ) :
    ((i : Fin N) → Fin (r i)) ≃ Fin (denominator r N) :=
  Equiv.ofBijective
    (fun d => ⟨prefixRank (extendPrefix r hr N d) N,
      prefixRank_lt_denominator hr (extendPrefix r hr N d) N⟩)
    ⟨fun _ _ h => finitePrefixRank_injective hr N (congrArg Fin.val h),
      fun k => by
        obtain ⟨d, hd⟩ := finitePrefixRank_surjective hr N k k.isLt
        exact ⟨d, Fin.ext hd⟩⟩

@[simp] theorem finitePrefixRankEquiv_val (r : ℕ → ℕ) (hr : ∀ n, 0 < r n)
    (N : ℕ) (d : (i : Fin N) → Fin (r i)) :
    (finitePrefixRankEquiv r hr N d : ℕ) = prefixRank (extendPrefix r hr N d) N := rfl

theorem finitePrefixRankEquiv_canonicalDigits (r : ℕ → ℕ) (hr : ∀ n, 0 < r n)
    {x : ℝ} (hx : x ∈ Set.Ico 0 1) (N : ℕ) :
    (finitePrefixRankEquiv r hr N (fun i => canonicalDigits r hr x i) : ℕ) =
      ⌊(denominator r N : ℝ) * x⌋₊ := by
  rw [finitePrefixRankEquiv_val]
  calc
    prefixRank (extendPrefix r hr N (fun i => canonicalDigits r hr x i)) N =
        prefixRank (canonicalDigits r hr x) N := by
      apply prefixRank_congr
      intro n hn
      simp [hn]
    _ = _ := prefixRank_canonicalDigits hr hx N

theorem measurable_canonicalDigits (r : ℕ → ℕ) (hr : ∀ n, 0 < r n) :
    Measurable (canonicalDigits r hr) := by
  apply Measurable.of_eval
  intro n
  exact (measurable_of_countable (fun k : ℕ =>
    (⟨k % r n, Nat.mod_lt _ (hr n)⟩ : Fin (r n)))).comp
      ((measurable_const.mul measurable_id).nat_floor)

theorem measurable_ofDigits {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n) :
    Measurable (@ofDigits r) := (continuous_ofDigits hr).measurable

theorem ofDigits_mem_Ico {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (hnt : Nonterminal d) : ofDigits d ∈ Set.Ico 0 1 := by
  refine ⟨ofDigits_nonneg d, ?_⟩
  simpa [tailValue, ofDigits] using tailValue_lt_one hr d hnt 0

theorem floor_denominator_mul_ofDigits {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (hnt : Nonterminal d) (N : ℕ) :
    ⌊(denominator r N : ℝ) * ofDigits d⌋₊ = prefixRank d N := by
  apply (Nat.floor_eq_iff (mul_nonneg (Nat.cast_nonneg _) (ofDigits_nonneg d))).mpr
  rw [denominator_mul_ofDigits hr d N]
  constructor
  · linarith [tailValue_nonneg d N]
  · linarith [tailValue_lt_one hr d hnt N]

theorem canonicalDigits_ofDigits {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (hnt : Nonterminal d) : canonicalDigits r hr (ofDigits d) = d := by
  funext n
  have hrank := prefixRank_canonicalDigits hr (ofDigits_mem_Ico hr d hnt) (n + 1)
  rw [floor_denominator_mul_ofDigits hr d hnt (n + 1)] at hrank
  exact (prefixRank_eq_iff hr _ _ (n + 1)).mp hrank n (Nat.lt_succ_self n)

end Invariant233.MixedRadix

end OAI

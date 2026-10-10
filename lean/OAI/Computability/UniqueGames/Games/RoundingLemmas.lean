import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Games.FinishBoundsLemmas
import OAI.Computability.UniqueGames.Reduction.WeightRounding

namespace OAI

/-!
# Largest-remainder rounding for the occurrence game

The input is an indexed list of nonnegative rational weights, represented
exactly by natural numerators with a common positive denominator. The order
uses decreasing fractional remainders, with the original occurrence index as
a deterministic tie-break. No constraint, endpoint or occurrence identity is
changed by rounding.
-/

namespace UniqueGamesTheorem.Explicit.Rounding

open scoped BigOperators

abbrev IntegerRounding := UniqueGamesTheorem.Reduction.WeightRounding.ceilQuotient

/-- Exact integer implementation of `ceil(h / (a/b))`. -/
def denominator (h a b : Nat) : Nat := IntegerRounding (h * b) a

theorem denominator_budget (h a b : Nat) (ha : 0 < a) :
    h * b ≤ denominator h a b * a :=
  UniqueGamesTheorem.Reduction.WeightRounding.le_ceilQuotient_mul _ _ ha

theorem denominator_size (h a b : Nat) (ha : 0 < a) :
    denominator h a b ≤ b * h := by
  simpa [denominator, Nat.mul_comm] using
    UniqueGamesTheorem.Reduction.WeightRounding.ceilQuotient_le (h * b) a ha

theorem denominator_positive (h a b : Nat) (hh : 0 < h)
    (ha : 0 < a) (hb : 0 < b) : 0 < denominator h a b := by
  have hp := Nat.mul_pos hh hb
  have he := denominator_budget h a b ha
  by_contra hn
  have hz : denominator h a b = 0 := by omega
  rw [hz] at he
  simp at he
  omega

variable {h : Nat}

/-- The fractional part of `Q * (p i / q)`, with denominator `q`. -/
def remainder (Q q : Nat) (p : Fin h → Nat) (i : Fin h) : Nat :=
  (Q * p i) % q

def priority (Q q : Nat) (p : Fin h → Nat) (i j : Fin h) : Prop :=
  remainder Q q p j < remainder Q q p i ∨
    (remainder Q q p i = remainder Q q p j ∧ i ≤ j)

instance priorityDecidable (Q q : Nat) (p : Fin h → Nat) :
    DecidableRel (priority Q q p) := fun _ _ => inferInstanceAs
      (Decidable (_ < _ ∨ (_ = _ ∧ _ ≤ _)))

instance priorityTrans (Q q : Nat) (p : Fin h → Nat) :
    IsTrans (Fin h) (priority Q q p) where
  trans := by
    intro i j k hij hjk
    unfold priority at *
    omega

instance priorityAntisymm (Q q : Nat) (p : Fin h → Nat) :
    Std.Antisymm (priority Q q p) where
  antisymm := by
    intro i j hij hji
    apply Fin.ext
    unfold priority at *
    omega

instance priorityTotal (Q q : Nat) (p : Fin h → Nat) :
    Std.Total (priority Q q p) where
  total := by
    intro i j
    unfold priority
    omega

/-- Executable merge-sort of occurrence indices, rather than their records. -/
def remainderOrder (Q q : Nat) (p : Fin h → Nat) : List (Fin h) :=
  Finset.univ.sort (priority Q q p)

theorem remainderOrder_sorted (Q q : Nat) (p : Fin h → Nat) :
    (remainderOrder Q q p).Pairwise (priority Q q p) :=
  Finset.pairwise_sort _ _

@[simp] theorem remainderOrder_length (Q q : Nat) (p : Fin h → Nat) :
    (remainderOrder Q q p).length = h := by
  simp [remainderOrder]

theorem remainderOrder_nodup (Q q : Nat) (p : Fin h → Nat) :
    (remainderOrder Q q p).Nodup := Finset.sort_nodup _ _

def floorCount (Q q : Nat) (p : Fin h → Nat) (i : Fin h) : Nat :=
  Q * p i / q

def deficit (Q q : Nat) (p : Fin h → Nat) : Nat :=
  Q - ∑ i, floorCount Q q p i

theorem floor_sum_le (Q q : Nat) (p : Fin h → Nat) (hq : 0 < q)
    (hmass : ∑ i, p i = q) : (∑ i, floorCount Q q p i) ≤ Q := by
  have he := UniqueGamesTheorem.Reduction.WeightRounding.floorMass_le_target
    Q q (List.ofFn p) hq (by simpa [List.sum_ofFn] using hmass)
  simpa [UniqueGamesTheorem.Reduction.WeightRounding.floorMass, List.map_ofFn,
    List.sum_ofFn, floorCount] using he

theorem deficit_lt (Q q : Nat) (p : Fin h → Nat) (hq : 0 < q)
    (hmass : ∑ i, p i = q) : deficit Q q p < h := by
  have he := UniqueGamesTheorem.Reduction.WeightRounding.deficit_lt_length
    Q q (List.ofFn p) hq (by simpa [List.sum_ofFn] using hmass)
  simpa [UniqueGamesTheorem.Reduction.WeightRounding.deficit,
    UniqueGamesTheorem.Reduction.WeightRounding.floorMass, List.map_ofFn,
    List.sum_ofFn, floorCount, deficit] using he

/-- Precisely the first `deficit` indices in decreasing remainder order. -/
def incremented (Q q : Nat) (p : Fin h → Nat) : Finset (Fin h) :=
  ((remainderOrder Q q p).take (deficit Q q p)).toFinset

def count (Q q : Nat) (p : Fin h → Nat) (i : Fin h) : Nat :=
  floorCount Q q p i + if i ∈ incremented Q q p then 1 else 0

theorem incremented_card (Q q : Nat) (p : Fin h → Nat) (hq : 0 < q)
    (hmass : ∑ i, p i = q) : (incremented Q q p).card = deficit Q q p := by
  rw [incremented, List.toFinset_card_of_nodup
    ((remainderOrder_nodup Q q p).take), List.length_take,
    remainderOrder_length, Nat.min_eq_left (Nat.le_of_lt (deficit_lt Q q p hq hmass))]

/-- Largest-remainder rounding preserves total mass exactly. -/
theorem sum_count (Q q : Nat) (p : Fin h → Nat) (hq : 0 < q)
    (hmass : ∑ i, p i = q) : ∑ i, count Q q p i = Q := by
  have hc := incremented_card Q q p hq hmass
  have hf := floor_sum_le Q q p hq hmass
  simp only [count, Finset.sum_add_distrib, Finset.sum_boole,
    Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id]
  rw [hc, deficit]
  omega

/-- Cross-multiplied pointwise error, independent of the rounding order. -/
theorem count_error (Q q : Nat) (p : Fin h → Nat) (hq : 0 < q) (i : Fin h) :
    count Q q p i * q ≤ Q * p i + q ∧
      Q * p i ≤ count Q q p i * q + q := by
  have hlo := Nat.div_mul_le_self (Q * p i) q
  have hhi : Q * p i < (Q * p i / q + 1) * q :=
    (Nat.div_lt_iff_lt_mul hq).mp (Nat.lt_succ_self _)
  unfold count floorCount
  split <;> simp only [Nat.add_zero, Nat.add_mul, Nat.one_mul] at * <;> omega

/-- Every incremented entry precedes every entry that is not incremented.
This records the largest-remainder requirement, including deterministic ties. -/
theorem incremented_priority (Q q : Nat) (p : Fin h → Nat) (i j : Fin h)
    (hi : i ∈ incremented Q q p) (hj : j ∉ incremented Q q p) :
    priority Q q p i j := by
  have hi' : i ∈ (remainderOrder Q q p).take (deficit Q q p) := by
    simpa [incremented] using hi
  have hj' : j ∉ (remainderOrder Q q p).take (deficit Q q p) := by
    simpa [incremented] using hj
  have hm : j ∈ remainderOrder Q q p := by simp [remainderOrder]
  have hd : j ∈ (remainderOrder Q q p).drop (deficit Q q p) := by
    rw [← List.take_append_drop (deficit Q q p) (remainderOrder Q q p),
      List.mem_append] at hm
    exact hm.resolve_left hj'
  have hs := remainderOrder_sorted Q q p
  rw [← List.take_append_drop (deficit Q q p) (remainderOrder Q q p),
    List.pairwise_append] at hs
  exact hs.2.2 i hi' j hd

/-- Error on any selected set of occurrences, before division. -/
theorem selected_count_error (Q q : Nat) (p : Fin h → Nat) (hq : 0 < q)
    (s : Finset (Fin h)) :
    (∑ i ∈ s, count Q q p i) * q ≤ Q * (∑ i ∈ s, p i) + s.card * q ∧
    Q * (∑ i ∈ s, p i) ≤ (∑ i ∈ s, count Q q p i) * q + s.card * q := by
  constructor
  · simpa [Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib] using
      (Finset.sum_le_sum fun i (_ : i ∈ s) => (count_error Q q p hq i).1)
  · simpa [Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib] using
      (Finset.sum_le_sum fun i (_ : i ∈ s) => (count_error Q q p hq i).2)

/-- Convert the integer error certificate to its normalized rational form. -/
theorem ratio_error (n p m Q q : Nat) (hQ : 0 < Q) (hq : 0 < q)
    (hu : n * q ≤ Q * p + m * q) (hl : Q * p ≤ n * q + m * q) :
    |(n : ℚ) / Q - (p : ℚ) / q| ≤ (m : ℚ) / Q := by
  have hQ' : (0 : ℚ) < Q := by exact_mod_cast hQ
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  have hu' : (n : ℚ) * q ≤ Q * p + m * q := by exact_mod_cast hu
  have hl' : (Q : ℚ) * p ≤ n * q + m * q := by exact_mod_cast hl
  rw [div_sub_div _ _ hQ'.ne' hq'.ne', abs_div, abs_of_pos (mul_pos hQ' hq')]
  apply (div_le_iff₀ (mul_pos hQ' hq')).mpr
  calc
    |(n : ℚ) * q - (Q : ℚ) * p| ≤ (m : ℚ) * q :=
      abs_le.mpr ⟨by nlinarith, by nlinarith⟩
    _ = ((m : ℚ) / Q) * (Q * q) := by field_simp [hQ'.ne']

theorem count_ratio_error (Q q : Nat) (p : Fin h → Nat)
    (hQ : 0 < Q) (hq : 0 < q) (i : Fin h) :
    |(count Q q p i : ℚ) / Q - (p i : ℚ) / q| ≤ 1 / (Q : ℚ) := by
  have he := count_error Q q p hq i
  simpa using ratio_error (count Q q p i) (p i) 1 Q q hQ hq
    (by simpa using he.1) (by simpa using he.2)

theorem selected_ratio_error (Q q : Nat) (p : Fin h → Nat)
    (hQ : 0 < Q) (hq : 0 < q) (s : Finset (Fin h)) :
    |((∑ i ∈ s, count Q q p i : Nat) : ℚ) / Q -
      ((∑ i ∈ s, p i : Nat) : ℚ) / q| ≤ (h : ℚ) / Q := by
  have he := selected_count_error Q q p hq s
  have hb := ratio_error _ _ _ Q q hQ hq he.1 he.2
  refine hb.trans ?_
  apply div_le_div_of_nonneg_right _ (by exact_mod_cast hQ.le)
  exact_mod_cast (show s.card ≤ h from
    (Finset.card_le_card (Finset.subset_univ s)).trans_eq (by simp))

theorem denominator_ratio_budget (h a b : Nat) (hh : 0 < h)
    (ha : 0 < a) (hb : 0 < b) :
    (h : ℚ) / denominator h a b ≤ (a : ℚ) / b := by
  have hQ : (0 : ℚ) < denominator h a b := by
    exact_mod_cast denominator_positive h a b hh ha hb
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  apply (div_le_div_iff₀ hQ hb').mpr
  have hc : (h : ℚ) * b ≤ denominator h a b * (a : ℚ) := by
    exact_mod_cast denominator_budget h a b ha
  simpa [mul_comm] using hc

/-- The algorithm's natural-number division is exactly the claimed ceiling. -/
theorem denominator_eq_ceil (h a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    denominator h a b = Nat.ceil ((h : ℚ) / ((a : ℚ) / b)) := by
  have ha' : (0 : ℚ) < a := by exact_mod_cast ha
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  have hr : (h : ℚ) / ((a : ℚ) / b) = ((h * b : Nat) : ℚ) / a := by
    push_cast
    field_simp [ha'.ne', hb'.ne']
  rw [hr]
  apply le_antisymm
  · unfold denominator IntegerRounding UniqueGamesTheorem.Reduction.WeightRounding.ceilQuotient
    apply (Nat.div_le_iff_le_mul ha).mpr
    have hc := (div_le_iff₀ ha').mp (Nat.le_ceil (((h * b : Nat) : ℚ) / a))
    have hn : h * b ≤ Nat.ceil (((h * b : Nat) : ℚ) / a) * a := by
      exact_mod_cast hc
    omega
  · apply Nat.ceil_le.mpr
    apply (div_le_iff₀ ha').mpr
    exact_mod_cast denominator_budget h a b ha

/-- Every satisfied-occurrence set has error at most the prescribed tolerance. -/
theorem selected_tolerance (a b q : Nat) (p : Fin h → Nat)
    (hh : 0 < h) (ha : 0 < a) (hb : 0 < b) (hq : 0 < q)
    (s : Finset (Fin h)) :
    |((∑ i ∈ s, count (denominator h a b) q p i : Nat) : ℚ) /
          denominator h a b - ((∑ i ∈ s, p i : Nat) : ℚ) / q| ≤
      (a : ℚ) / b :=
  (selected_ratio_error _ q p (denominator_positive h a b hh ha hb) hq s).trans
    (denominator_ratio_budget h a b hh ha hb)

/-- Satisfaction-predicate form, with individually normalized rational weights. -/
theorem selected_weight_error (Q q : Nat) (p : Fin h → Nat)
    (hQ : 0 < Q) (hq : 0 < q) (keep : Fin h → Bool) :
    |(∑ i, if keep i then (count Q q p i : ℚ) / Q else 0) -
      (∑ i, if keep i then (p i : ℚ) / q else 0)| ≤ (h : ℚ) / Q := by
  have he := selected_ratio_error Q q p hQ hq (Finset.univ.filter fun i => keep i)
  simpa [Nat.cast_sum, Finset.sum_filter, div_eq_mul_inv, Finset.sum_mul, ite_mul] using he

theorem selected_weight_tolerance (a b q : Nat) (p : Fin h → Nat)
    (hh : 0 < h) (ha : 0 < a) (hb : 0 < b) (hq : 0 < q)
    (keep : Fin h → Bool) :
    |(∑ i, if keep i then (count (denominator h a b) q p i : ℚ) /
        denominator h a b else 0) -
      (∑ i, if keep i then (p i : ℚ) / q else 0)| ≤ (a : ℚ) / b :=
  (selected_weight_error _ q p (denominator_positive h a b hh ha hb) hq keep).trans
    (denominator_ratio_budget h a b hh ha hb)

def copies (Q q : Nat) (p : Fin h → Nat) : List (Fin h) :=
  (List.ofFn fun i => List.replicate (count Q q p i) i).flatten

theorem copies_length (Q q : Nat) (p : Fin h → Nat) (hq : 0 < q)
    (hmass : ∑ i, p i = q) : (copies Q q p).length = Q := by
  simpa [copies, List.map_ofFn, List.sum_ofFn] using sum_count Q q p hq hmass

theorem copies_nonempty (Q q : Nat) (p : Fin h → Nat) (hQ : 0 < Q)
    (hq : 0 < q) (hmass : ∑ i, p i = q) : copies Q q p ≠ [] := by
  intro he
  have hl := copies_length Q q p hq hmass
  rw [he] at hl
  simp at hl
  omega

theorem copies_filter_length (Q q : Nat) (p : Fin h → Nat) (keep : Fin h → Bool) :
    ((copies Q q p).filter keep).length =
      ∑ i, if keep i then count Q q p i else 0 := by
  simp [copies, List.filter_flatten, List.map_ofFn, List.sum_ofFn,
    List.filter_replicate, apply_ite]

/-- An individual multiplicity is bounded by the chosen output size. -/
theorem count_le (Q q : Nat) (p : Fin h → Nat) (hq : 0 < q)
    (hmass : ∑ i, p i = q) (i : Fin h) : count Q q p i ≤ Q := by
  calc
    count Q q p i ≤ ∑ j, count Q q p j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ = Q := sum_count Q q p hq hmass

end UniqueGamesTheorem.Explicit.Rounding

namespace UniqueGamesTheorem.Explicit

open scoped BigOperators

/-- Normalized rational occurrence weights; zero weights are also permitted. -/
structure RationalWeights (h : Nat) where
  weight : Fin h → ℚ
  nonnegative : ∀ i, 0 ≤ weight i
  normalized : ∑ i, weight i = 1

namespace RationalWeights

variable {h : Nat} (w : RationalWeights h)

theorem length_positive (w : RationalWeights h) : 0 < h := by
  by_contra hn
  have hh : h = 0 := by omega
  subst h
  have he := w.normalized
  simp at he

/-- An executable exact common denominator, not the number of output copies. -/
def denominator : Nat := ∏ i, (w.weight i).den

theorem denominator_positive : 0 < w.denominator := by
  exact Nat.pos_of_ne_zero
    (Finset.prod_ne_zero_iff.mpr fun i _ => (w.weight i).den_ne_zero)

theorem den_dvd_denominator (i : Fin h) : (w.weight i).den ∣ w.denominator :=
  Finset.dvd_prod_of_mem (fun j => (w.weight j).den) (Finset.mem_univ i)

def numerator (i : Fin h) : Nat :=
  (w.weight i).num.toNat * (w.denominator / (w.weight i).den)

theorem numerator_cast (i : Fin h) :
    (w.numerator i : ℚ) = w.weight i * w.denominator := by
  have hn : ((w.weight i).num.toNat : ℚ) = ((w.weight i).num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr (w.nonnegative i))
  have hd : ((w.weight i).den : ℚ) ≠ 0 := by
    exact_mod_cast (w.weight i).den_ne_zero
  have hdiv : ((w.denominator / (w.weight i).den : Nat) : ℚ) *
      (w.weight i).den = w.denominator := by
    exact_mod_cast Nat.div_mul_cancel (w.den_dvd_denominator i)
  have hnum : ((w.weight i).num : ℚ) = w.weight i * (w.weight i).den :=
    (div_eq_iff hd).mp (w.weight i).num_div_den
  rw [numerator, Nat.cast_mul, hn, hnum]
  calc
    w.weight i * (w.weight i).den * ↑(w.denominator / (w.weight i).den) =
        w.weight i * (↑(w.denominator / (w.weight i).den) * (w.weight i).den) := by ring
    _ = _ := by rw [hdiv]

/-- Every original weight is represented exactly. -/
theorem weight_eq_ratio (i : Fin h) :
    w.weight i = (w.numerator i : ℚ) / w.denominator := by
  have hq : (w.denominator : ℚ) ≠ 0 := by exact_mod_cast w.denominator_positive.ne'
  rw [w.numerator_cast]
  field_simp [hq]

theorem sum_numerator : ∑ i, w.numerator i = w.denominator := by
  have he : (∑ i, (w.numerator i : ℚ)) = (w.denominator : ℚ) := by
    simp_rw [w.numerator_cast]
    rw [← Finset.sum_mul, w.normalized, one_mul]
  exact_mod_cast he

theorem numerator_positive (i : Fin h) (hi : 0 < w.weight i) :
    0 < w.numerator i := by
  have hq : (0 : ℚ) < w.denominator := by exact_mod_cast w.denominator_positive
  have hn : (0 : ℚ) < w.numerator i := by
    rw [w.numerator_cast]
    exact mul_pos hi hq
  exact_mod_cast hn

/-- Exact positive-rational numerator conversion used for the tolerance. -/
theorem positive_ratio (τ : ℚ) (hτ : 0 < τ) :
    (τ.num.toNat : ℚ) / τ.den = τ := by
  have hn : (τ.num.toNat : ℚ) = (τ.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hτ.le)
  rw [hn]
  exact τ.num_div_den

theorem positive_numerator (τ : ℚ) (hτ : 0 < τ) : 0 < τ.num.toNat :=
  Int.pos_iff_toNat_pos.mp (Rat.num_pos.mpr hτ)

def outputSize (_w : RationalWeights h) (τ : ℚ) : Nat :=
  Rounding.denominator h τ.num.toNat τ.den

theorem outputSize_positive (τ : ℚ) (hτ : 0 < τ) : 0 < w.outputSize τ :=
  Rounding.denominator_positive _ _ _ w.length_positive
    (positive_numerator τ hτ) τ.den_pos

theorem outputSize_eq_ceil (τ : ℚ) (hτ : 0 < τ) :
    w.outputSize τ = Nat.ceil ((h : ℚ) / τ) := by
  rw [outputSize, Rounding.denominator_eq_ceil _ _ _ (positive_numerator τ hτ) τ.den_pos,
    positive_ratio τ hτ]

theorem outputSize_le (τ : ℚ) (hτ : 0 < τ) : w.outputSize τ ≤ τ.den * h :=
  Rounding.denominator_size _ _ _ (positive_numerator τ hτ)

/-- Largest-remainder multiplicities computed from the exact input weights. -/
def multiplicity (τ : ℚ) (i : Fin h) : Nat :=
  Rounding.count (w.outputSize τ) w.denominator w.numerator i

theorem sum_multiplicity (τ : ℚ) : ∑ i, w.multiplicity τ i = w.outputSize τ :=
  Rounding.sum_count _ _ _ w.denominator_positive w.sum_numerator

theorem multiplicity_weight_error (τ : ℚ) (hτ : 0 < τ) (i : Fin h) :
    |(w.multiplicity τ i : ℚ) / w.outputSize τ - w.weight i| ≤
      1 / (w.outputSize τ : ℚ) := by
  rw [w.weight_eq_ratio i]
  exact Rounding.count_ratio_error _ _ _ (w.outputSize_positive τ hτ)
    w.denominator_positive i

/-- Error for every labeling's satisfaction predicate on the original IDs. -/
theorem selected_weight_error (τ : ℚ) (hτ : 0 < τ) (keep : Fin h → Bool) :
    |(∑ i, if keep i then (w.multiplicity τ i : ℚ) / w.outputSize τ else 0) -
      (∑ i, if keep i then w.weight i else 0)| ≤ τ := by
  simp_rw [w.weight_eq_ratio]
  have he := Rounding.selected_weight_tolerance τ.num.toNat τ.den w.denominator
    w.numerator w.length_positive (positive_numerator τ hτ) τ.den_pos
    w.denominator_positive keep
  simpa only [outputSize, multiplicity, positive_ratio τ hτ] using he

/-- List of output IDs, preserving different occurrences with equal records. -/
def copies (τ : ℚ) : List (Fin h) :=
  Rounding.copies (w.outputSize τ) w.denominator w.numerator

theorem copies_length (τ : ℚ) : (w.copies τ).length = w.outputSize τ :=
  Rounding.copies_length _ _ _ w.denominator_positive w.sum_numerator

theorem copies_nonempty (τ : ℚ) (hτ : 0 < τ) : w.copies τ ≠ [] :=
  Rounding.copies_nonempty _ _ _ (w.outputSize_positive τ hτ)
    w.denominator_positive w.sum_numerator

theorem copies_filter_length (τ : ℚ) (keep : Fin h → Bool) :
    ((w.copies τ).filter keep).length = ∑ i, if keep i then w.multiplicity τ i else 0 :=
  Rounding.copies_filter_length _ _ _ keep

theorem copies_weight_error (τ : ℚ) (hτ : 0 < τ) (keep : Fin h → Bool) :
    |(((w.copies τ).filter keep).length : ℚ) / (w.copies τ).length -
      (∑ i, if keep i then w.weight i else 0)| ≤ τ := by
  rw [w.copies_length, w.copies_filter_length]
  simpa [Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul, ite_mul] using
    w.selected_weight_error τ hτ keep

end RationalWeights

/-!
The value bridge for rounding: integer multiplicities denote separate
occurrences, and the pointwise error estimate is transferred to the maximum
over the same original vertex labelings. These constructions retain occurrence
IDs even when endpoints or constraints coincide.
-/

namespace OccurrenceGame

variable {V E A : Type*} [Fintype E] [DecidableEq A]

noncomputable def weightedScore (g : OccurrenceGame V E A) (w : E → ℝ)
    (a : V → A) : ℝ := ∑ e, if g.Satisfied a e then w e else 0

variable [Fintype V] [Fintype A] [Nonempty A]

noncomputable def weightedValue (g : OccurrenceGame V E A) (w : E → ℝ) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty (weightedScore g w)

theorem weightedScore_le_weightedValue (g : OccurrenceGame V E A) (w : E → ℝ)
    (a : V → A) : g.weightedScore w a ≤ g.weightedValue w := by
  classical
  exact Finset.le_sup' (f := weightedScore g w) (Finset.mem_univ a)

theorem weightedValue_attained (g : OccurrenceGame V E A) (w : E → ℝ) :
    ∃ a, g.weightedScore w a = g.weightedValue w := by
  classical
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (weightedScore g w)
  exact ⟨a, ha.symm⟩

/-- A uniform per-labeling error controls both maxima, without identifying their
optimizing labelings. -/
theorem weightedValue_error (g : OccurrenceGame V E A) (w w' : E → ℝ) (τ : ℝ)
    (h : ∀ a, |g.weightedScore w' a - g.weightedScore w a| ≤ τ) :
    |g.weightedValue w' - g.weightedValue w| ≤ τ := by
  obtain ⟨a, ha⟩ := g.weightedValue_attained w
  obtain ⟨b, hb⟩ := g.weightedValue_attained w'
  have ha' := g.weightedScore_le_weightedValue w' a
  have hb' := g.weightedScore_le_weightedValue w b
  have h₁ := (abs_le.mp (h a)).1
  have h₂ := (abs_le.mp (h b)).2
  rw [ha] at h₁
  rw [hb] at h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

omit [Fintype V] [Fintype A] [Nonempty A] in
theorem weightedScore_uniform (g : OccurrenceGame V E A) (a : V → A) :
    g.weightedScore (fun _ => 1 / (Fintype.card E : ℝ)) a =
      (g.satisfiedCount a : ℝ) / Fintype.card E := by
  rw [satisfiedCount_eq_sum_satisfied]
  simp only [weightedScore, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  split <;> simp_all

theorem weightedValue_uniform (g : OccurrenceGame V E A) :
    g.weightedValue (fun _ => 1 / (Fintype.card E : ℝ)) = g.value := by
  obtain ⟨a, ha⟩ := g.weightedValue_attained (fun _ => 1 / (Fintype.card E : ℝ))
  obtain ⟨b, hb⟩ := g.maxSatisfied_attained
  apply le_antisymm
  · rw [← ha, weightedScore_uniform, value]
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast g.satisfiedCount_le_maxSatisfied a) (Nat.cast_nonneg _)
  · have h := g.weightedScore_le_weightedValue
      (fun _ => 1 / (Fintype.card E : ℝ)) b
    rw [weightedScore_uniform, hb] at h
    exact h

end OccurrenceGame

namespace Rounding

variable {V E A : Type*}

def copied (g : OccurrenceGame V E A) (n : E → Nat) :
    OccurrenceGame V (Σ e, Fin (n e)) A where
  source e := g.source e.1
  target e := g.target e.1
  permutation e := g.permutation e.1

@[simp] theorem copied_isTranslation [Add A] (g : OccurrenceGame V E A)
    (n : E → Nat) (hg : g.IsTranslation) : (copied g n).IsTranslation := by
  obtain ⟨c, hc⟩ := hg
  exact ⟨fun e => c e.1, fun e a => hc e.1 a⟩

theorem copied_card [Fintype E] (n : E → Nat) :
    Fintype.card (Σ e, Fin (n e)) = ∑ e, n e := by
  simp [Fintype.card_sigma]

theorem copied_satisfiedCount [Fintype E] [DecidableEq A]
    (g : OccurrenceGame V E A) (n : E → Nat) (a : V → A) :
    (copied g n).satisfiedCount a =
      ∑ e, if g.Satisfied a e then n e else 0 := by
  rw [OccurrenceGame.satisfiedCount_eq_sum_satisfied]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro e _
  change (∑ _ : Fin (n e), if g.Satisfied a e then 1 else 0) = _
  by_cases he : g.Satisfied a e <;> simp [he]

theorem copied_value [Fintype E] [Fintype V] [Fintype A] [Nonempty A]
    [DecidableEq A] (g : OccurrenceGame V E A) (n : E → Nat) :
    (copied g n).value =
      g.weightedValue (fun e => (n e : ℝ) / (∑ i, n i : Nat)) := by
  classical
  rw [← OccurrenceGame.weightedValue_uniform]
  unfold OccurrenceGame.weightedValue
  congr 1
  funext a
  rw [OccurrenceGame.weightedScore_uniform, copied_satisfiedCount, copied_card]
  simp only [OccurrenceGame.weightedScore, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_zero, div_eq_mul_inv, Finset.sum_mul, ite_mul, zero_mul]

variable {h : Nat} [Fintype V] [Fintype A] [Nonempty A] [DecidableEq A]

/-- The actual copied occurrence game's maximum differs from the input weighted
maximum by at most `h/Q`. -/
theorem rounded_value_error (g : OccurrenceGame V (Fin h) A)
    (Q q : Nat) (p : Fin h → Nat) (hQ : 0 < Q) (hq : 0 < q)
    (hmass : ∑ i, p i = q) :
    |(copied g (count Q q p)).value -
      g.weightedValue (fun e => (p e : ℝ) / q)| ≤ (h : ℝ) / Q := by
  rw [copied_value, sum_count Q q p hq hmass]
  apply OccurrenceGame.weightedValue_error
  intro labeling
  have he := selected_weight_error Q q p hQ hq (fun e => decide (g.Satisfied labeling e))
  simp only [decide_eq_true_eq] at he
  have hr := (Rat.cast_le (K := ℝ)).mpr he
  push_cast at hr
  have cast_sum (f : Fin h → ℚ) :
      ((∑ i, f i : ℚ) : ℝ) = ∑ i, (f i : ℝ) :=
    map_sum (Rat.castHom ℝ) f Finset.univ
  rw [cast_sum, cast_sum] at hr
  simpa only [OccurrenceGame.weightedScore, apply_ite, Rat.cast_div,
    Rat.cast_natCast, Rat.cast_zero] using hr

theorem rounded_value_tolerance (g : OccurrenceGame V (Fin h) A)
    (a b q : Nat) (p : Fin h → Nat) (hh : 0 < h)
    (ha : 0 < a) (hb : 0 < b) (hq : 0 < q) (hmass : ∑ i, p i = q) :
    |(copied g (count (denominator h a b) q p)).value -
      g.weightedValue (fun e => (p e : ℝ) / q)| ≤ (a : ℝ) / b := by
  apply (rounded_value_error g _ q p (denominator_positive h a b hh ha hb)
    hq hmass).trans
  have hr := (Rat.cast_le (K := ℝ)).mpr (denominator_ratio_budget h a b hh ha hb)
  push_cast at hr
  exact hr

/-- The rounding/subdivision error, for the constructed simple bipartite game. -/
theorem rounded_subdivision_value (g : OccurrenceGame V (Fin h) A)
    (a b q : Nat) (p : Fin h → Nat) (hh : 0 < h)
    (ha : 0 < a) (hb : 0 < b) (hq : 0 < q) (hmass : ∑ i, p i = q) :
    |(Subdivision.game (copied g (count (denominator h a b) q p))).value -
      (1 - (1 - g.weightedValue (fun e => (p e : ℝ) / q)) / 4)| ≤
      ((a : ℝ) / b) / 4 := by
  have hcard : 0 < Fintype.card (Σ e, Fin (count (denominator h a b) q p e)) := by
    rw [copied_card, sum_count _ q p hq hmass]
    exact denominator_positive h a b hh ha hb
  let : Nonempty (Σ e, Fin (count (denominator h a b) q p e)) :=
    Fintype.card_pos_iff.mp hcard
  rw [Subdivision.value_eq]
  have he := rounded_value_tolerance g a b q p hh ha hb hq hmass
  have hrewrite :
      (1 - (1 - (copied g (count (denominator h a b) q p)).value) / 4) -
        (1 - (1 - g.weightedValue (fun e => (p e : ℝ) / q)) / 4) =
      ((copied g (count (denominator h a b) q p)).value -
        g.weightedValue (fun e => (p e : ℝ) / q)) / 4 := by ring
  rw [hrewrite, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  exact div_le_div_of_nonneg_right he (by norm_num)

end Rounding

end UniqueGamesTheorem.Explicit

end OAI

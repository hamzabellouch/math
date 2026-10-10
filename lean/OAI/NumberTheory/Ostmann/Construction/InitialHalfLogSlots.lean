import OAI.NumberTheory.Ostmann.Construction.InitialHalfBulkProduct
import OAI.NumberTheory.Ostmann.Arithmetic.MovingBulkPairedCutoffs

namespace OAI

/-! # The exact two half-bulk cutoffs as a finite family of log weights -/
namespace Ostmann
open scoped Classical BigOperators

theorem initialHalfBulkProduct_eq_prod {P : Type*} (value : P → ℕ)
    (b d : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (n : ℕ)
    (slot : TreeLeafIndex n × Fin (b + b) → P) :
    initialHalfBulkProduct value b d cb cd sl sr n slot =
      ∏ j : TreeLeafIndex n, initialHalfBulkWeight value b d cb cd sl sr (fun i => slot (j, i)) := by
  induction n with
  | zero =>
    change _ = ∏ j : Unit, initialHalfBulkWeight value b d cb cd sl sr (fun i => slot (j, i))
    simp only [Fintype.prod_unique, initialHalfBulkProduct]
  | succ n ih =>
    change initialHalfBulkProduct value b d cb cd sl sr n (fun j => slot (.inl j.1, j.2)) *
      initialHalfBulkProduct value b d cb cd sl sr n (fun j => slot (.inr j.1, j.2)) =
      ∏ j : TreeLeafIndex n ⊕ TreeLeafIndex n,
        initialHalfBulkWeight value b d cb cd sl sr (fun i => slot (j, i))
    rw [Fintype.prod_sum_type, ih, ih]

theorem initialLogSumWeight_eq_cutoff {P : Type*} (value : P → ℕ)
    (hvalue : ∀ p, 0 < value p) (b : ℕ) (cb : ℝ) (x : Fin b → P) :
    initialLogSumWeight value cb x =
      bulkLogCutoffWeight (fun p => (value p : ℝ)) cb (List.ofFn x) := by
  have hp : 0 < ∏ i, (value (x i) : ℝ) :=
    Finset.prod_pos (fun i _ => by exact_mod_cast hvalue (x i))
  unfold bulkLogCutoffWeight realSlotProduct
  rw [List.map_ofFn, List.prod_ofFn]
  unfold positiveLogCutoff
  simp only [Function.comp_def]
  rw [ite_eq_left hp, Real.log_prod (fun i _ => by exact_mod_cast (hvalue (x i)).ne')]
  rfl

noncomputable def initialHalfBulkLeaves {B : Type*} (n b : ℕ)
    (slot : TreeLeafIndex n × Fin (b + b) → B) (side : Bool) : TreeLeafTuple (List B) n :=
  bulkSlotLeaves n b (fun j => slot (j.1, if side then Fin.natAdd b j.2 else j.2.castAdd b))

noncomputable def initialHalfLogSlots {B : Type*} (n b : ℕ)
    (slot : TreeLeafIndex n × Fin (b + b) → B) : Fin (2 ^ n + 2 ^ n) → List B :=
  movingBulkPairedCutoffSlots n (initialHalfBulkLeaves n b slot)

theorem initialHalfLogSlots_length {B : Type*} (n b : ℕ)
    (slot : TreeLeafIndex n × Fin (b + b) → B) (j : Fin (2 ^ n + 2 ^ n)) :
    (initialHalfLogSlots n b slot j).length ≤ b :=
  movingBulkPairedCutoffSlots_length n b _ (fun _ => bulkSlotLeaves_length n b _) j

theorem initialHalfBulkProduct_log_slots {P : Type*} (value : P → ℕ)
    (hvalue : ∀ p, 0 < value p) (b d : ℕ) (cb cd : ℝ) (sl sr : Fin d → P)
    (n : ℕ) (slot : TreeLeafIndex n × Fin (b + b) → P) :
    initialHalfBulkProduct value b d cb cd sl sr n slot =
      (initialLogSumWeight value cd sl * initialLogSumWeight value cd sr) ^ (2 ^ n) *
      ∏ j, bulkLogCutoffWeight (fun p => (value p : ℝ)) cb (initialHalfLogSlots n b slot j) := by
  rw [initialHalfBulkProduct_eq_prod]
  unfold initialHalfLogSlots
  rw [movingBulkPairedCutoffSlots_product]
  simp only [initialHalfBulkLeaves, treeLeafProduct_eq_prod, treeLeafTupleEquiv_map,
    bulkSlotLeaves, Equiv.apply_symm_apply, Bool.false_eq_true, ↓reduceIte]
  simp_rw [← initialLogSumWeight_eq_cutoff value hvalue]
  simp only [initialHalfBulkWeight, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, card_treeLeafIndex, mul_pow]
  ring

noncomputable def initialPairedHalfLogSlots {B : Type*} (n b : ℕ)
    (slot : Bool → TreeLeafIndex n × Fin (b + b) → B) :
    Fin ((2 ^ n + 2 ^ n) + (2 ^ n + 2 ^ n)) → List B :=
  Fin.append (initialHalfLogSlots n b (slot false)) (initialHalfLogSlots n b (slot true))

theorem initialPairedHalfLogSlots_length {B : Type*} (n b : ℕ)
    (slot : Bool → TreeLeafIndex n × Fin (b + b) → B)
    (j : Fin ((2 ^ n + 2 ^ n) + (2 ^ n + 2 ^ n))) :
    (initialPairedHalfLogSlots n b slot j).length ≤ b := by
  refine Fin.addCases ?_ ?_ j <;> intro i
  · simpa only [initialPairedHalfLogSlots, Fin.append_left] using
      initialHalfLogSlots_length n b (slot false) i
  · simpa only [initialPairedHalfLogSlots, Fin.append_right] using
      initialHalfLogSlots_length n b (slot true) i

theorem initialHalfBulkProduct_pair_log_slots {P : Type*} (value : P → ℕ)
    (hvalue : ∀ p, 0 < value p) (b d : ℕ) (cb cd : ℝ) (sl sr : Fin d → P)
    (n : ℕ) (slot : Bool → TreeLeafIndex n × Fin (b + b) → P) :
    (initialHalfBulkProduct value b d cb cd sl sr n (slot false) : ℂ) *
      star (initialHalfBulkProduct value b d cb cd sl sr n (slot true) : ℂ) =
    ((initialLogSumWeight value cd sl * initialLogSumWeight value cd sr) ^
      (2 ^ n + 2 ^ n) : ℝ) *
      ((∏ j, bulkLogCutoffWeight (fun p => (value p : ℝ)) cb
        (initialPairedHalfLogSlots n b slot j) : ℝ) : ℂ) := by
  rw [initialHalfBulkProduct_log_slots value hvalue b d cb cd sl sr n (slot false),
    initialHalfBulkProduct_log_slots value hvalue b d cb cd sl sr n (slot true)]
  simp only [initialPairedHalfLogSlots, Fin.prod_univ_add, Fin.append_left, Fin.append_right,
    Complex.ofReal_mul, Complex.star_def, map_mul, Complex.conj_ofReal, pow_add]
  ring

end Ostmann

end OAI

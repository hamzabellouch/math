import OAI.NumberTheory.TwoPoint.Walks.ProhibitedWeightSupport
import OAI.NumberTheory.TwoPoint.Bounds.ActualPaddingProduct

namespace OAI

/-! The actual departure product has the retained-column majorant and
the precise small-singleton crude bound used by the trace theorem. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

def columnTupleAtNat {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (i : ℕ) : ℕ :=
  if hi : i < R then columnTuple w ⟨i, hi⟩ else 1

def columnForwardAtNat {R : ℕ} (forward : Fin R → Bool) (i : ℕ) : Bool :=
  if hi : i < R then forward ⟨i, hi⟩ else false

def actualColumnNext {J R : ℕ} {P : Fin J → Finset ℕ}
    (h : ℕ) (forward : Fin R → Bool) (w : ColumnPrimeAssignment J R P)
    (i : ℕ) (n : ℤ) (q : ℕ) : ℤ :=
  n + (SignedStep.mk (columnForwardAtNat forward i) (columnTupleAtNat w i) q).displacement h

lemma columnTupleAtNat_val {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (i : Fin R) :
    columnTupleAtNat w i.val = columnTuple w i := by
  simp only [columnTupleAtNat, i.isLt, dite_true, Fin.eta]

lemma columnForwardAtNat_val {R : ℕ} (forward : Fin R → Bool) (i : Fin R) :
    columnForwardAtNat forward i.val = forward i := by
  simp only [columnForwardAtNat, i.isLt, dite_true, Fin.eta]

theorem retained_word_le_column {J k : ℕ} {P : Fin J → Finset ℕ}
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop) (g : ℤ → ℝ)
    (L K : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (hL : 0 ≤ L) (hu : ∀ q, 0 ≤ u q)
    (w : ColumnPrimeAssignment J (2 * k) P) (forward : Fin (2 * k) → Bool)
    (q : Fin (2 * k) → Q) (n : ℤ) :
    scalarWalkProduct h
      (retainedEdgeDeparture Q u (fun t => eligible t.tuple) g L K (fun t => extra t.tuple) h)
      n (columnTupleWord w forward (fun i => (q i).val)) ≤
      retainedColumnPaddingWeight Q u (fun w i => eligible (columnTupleAtNat w i)) g L K
        (fun w i => extra (columnTupleAtNat w i)) (actualColumnNext h forward) n w q := by
  rw [retainedColumnPaddingWeight_eq_departure_product Q u _ g L K _ _ h n w forward q]
  · unfold columnTupleWord
    rw [scalarWalkProduct_ofFn]
    apply prod_le_prod₀
    · intro i _
      exact retainedEdgeDeparture_nonneg Q u _ g L K _ h hL hu _ _
    · intro i _
      simp only [columnTupleAtNat_val]
      exact retainedEdgeDeparture_le_atom Q u _ g L K _ h hL hu _ _
  · intro i z
    simp only [actualColumnNext, columnForwardAtNat_val, columnTupleAtNat_val]

noncomputable def columnCrudeCap {J R : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    (L : ℝ) (a : ColumnPrimeAssignment J R P × (Fin R → Q)) : ℝ :=
  ∏ i, L * crudePaddingWeight (a.2 i).val

lemma columnCrudeCap_nonneg {J R : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    (L : ℝ) (hL : 0 ≤ L) (a : ColumnPrimeAssignment J R P × (Fin R → Q)) :
    0 ≤ columnCrudeCap L a := by
  unfold columnCrudeCap crudePaddingWeight
  positivity

theorem columnCrudeCap_small {J R S T : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    (L : ℝ) (hL : 0 ≤ L) (a : ColumnPrimeAssignment J R P × (Fin R → Q)) (hST : S ≤ T) :
    columnCrudeCap L a * 2 ^ S ≤ crudeTraceWeight R T (fun i => (a.2 i).val) L 1 := by
  unfold crudeTraceWeight
  rw [one_mul, mul_comm (2 ^ T)]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hST) (columnCrudeCap_nonneg L hL a)

theorem columnCrudeCap_exp {J R S : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    (L Cs : ℝ) (a : ColumnPrimeAssignment J R P × (Fin R → Q))
    (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) (hR : (R : ℝ) ≤ 2 * L)
    (hS : (S : ℝ) ≤ Cs * L * Real.log L)
    (hq : ∀ i, (((a.2 i).val).primeFactors.card : ℝ) ≤ 100 * Real.log L) :
    columnCrudeCap L a * 2 ^ S ≤ Real.exp ((Cs + 402) * L * (Real.log L) ^ 2) := by
  have hb := crudeTraceWeight_exp_bound R S (fun i => (a.2 i).val) L 1 0 Cs
    hL hlog hR hS (by norm_num) (by simp) hq
  simpa only [crudeTraceWeight, columnCrudeCap, one_mul, zero_add, mul_comm] using hb

end TwoPointCorrelations

end OAI

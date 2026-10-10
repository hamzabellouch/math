import OAI.NumberTheory.TwoPoint.Walks.ColumnPaddingBridge
import OAI.NumberTheory.TwoPoint.Walks.ColumnMatrixTrace

namespace OAI

/-! Verify all weight hypotheses of the trace estimate for the literal
departure product appearing in the matrix expansion. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def actualColumnWeight {h J M R B : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : ℕ → ℤ → Prop) (forward : Fin R → Bool)
    (a : ColumnPrimeAssignment J R P × (Fin R → Q))
    (x : ↥(data.P ∪ data.Q) → Fin B) : ℝ :=
  data.residueValue (fun n => scalarWalkProduct h
    (retainedEdgeDeparture Q u (fun t => eligible t.tuple) g L K (fun t => extra t.tuple) h)
    n (columnTupleWord a.1 forward (fun i => (a.2 i).val))) x

lemma actualColumnWeight_nonneg {h J M R B : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : ℕ → ℤ → Prop) (forward : Fin R → Bool)
    (hL : 0 ≤ L) (hu : ∀ q, 0 ≤ u q)
    (a : ColumnPrimeAssignment J R P × (Fin R → Q))
    (x : ↥(data.P ∪ data.Q) → Fin B) :
    0 ≤ actualColumnWeight data u eligible g L K extra forward a x :=
  scalarWalkProduct_nonneg h _
    (retainedEdgeDeparture_nonneg Q u _ g L K _ h hL hu) _ _

lemma actualColumnWeight_le_cap {h J M R B : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : ℕ → ℤ → Prop) (forward : Fin R → Bool)
    (hL : 0 ≤ L) (hu : ∀ q, 0 ≤ u q) (hub : ∀ q, u q ≤ crudePaddingWeight q)
    (hg : ∀ n, 1 ≤ (g n) ^ 2)
    (a : ColumnPrimeAssignment J R P × (Fin R → Q))
    (x : ↥(data.P ∪ data.Q) → Fin B) :
    actualColumnWeight data u eligible g L K extra forward a x ≤ columnCrudeCap L a :=
  retained_word_le_crude Q u _ g L K _ h hL hu hub hg
    (fun i => SignedStep.mk (forward i) (columnTuple a.1 i) (a.2 i).val) _

lemma actualColumnWeight_padding {h J M R B : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : ℕ → ℤ → Prop) (forward : Fin R → Bool)
    (a : ColumnPrimeAssignment J R P × (Fin R → Q))
    (x : ↥(data.P ∪ data.Q) → Fin B)
    (hx : actualColumnWeight data u eligible g L K extra forward a x ≠ 0) :
    MainPaddingTests Subtype.val h B (columnTupleWord a.1 forward (fun i => (a.2 i).val)) x :=
  lifted_retained_word_padding_tests data Q u _ g L K _
    (fun i => SignedStep.mk (forward i) (columnTuple a.1 i) (a.2 i).val) x hx

lemma actualColumnWeight_independent {h J M R B : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (hP : ∀ j, P j ⊆ data.P)
    (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ)
    (extra : ℕ → ℤ → Prop) (forward : Fin R → Bool)
    (hsq : ∀ q ∈ Q, Squarefree q) (hpool : ∀ q ∈ Q, q.primeFactors ⊆ data.Q)
    (hg : ∀ n m : ℤ, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) → g n = g m)
    (hextra : ∀ d n m, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) →
      (extra d n ↔ extra d m))
    (a : ColumnPrimeAssignment J R P × (Fin R → Q))
    (x y : ↥(data.P ∪ data.Q) → Fin B)
    (hxy : ∀ p, p ∉ univ.image (actualColumnLabel data hP a.1) → x p = y p) :
    actualColumnWeight data u eligible g L K extra forward a x =
      actualColumnWeight data u eligible g L K extra forward a y := by
  apply lifted_retained_word_independent_tuple data Q u _ g L K _
    (fun i => SignedStep.mk (forward i) (columnTuple a.1 i) (a.2 i).val)
    hsq hpool hg (fun t => hextra t.tuple) (actualColumnLabel data hP a.1) _ x y hxy
  intro p hp
  obtain ⟨i, _, rfl⟩ := mem_image.mp hp
  exact hP i.2 (a.1 i.2 i.1).property

lemma actualColumnWeight_le_retained {h J M B k : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : ℕ → ℤ → Prop) (forward : Fin (2 * k) → Bool)
    (hL : 0 ≤ L) (hu : ∀ q, 0 ≤ u q)
    (a : ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q))
    (x : ↥(data.P ∪ data.Q) → Fin B) :
    actualColumnWeight data u eligible g L K extra forward a x ≤
      retainedColumnPaddingWeight Q u (fun w i => eligible (columnTupleAtNat w i)) g L K
        (fun w i => extra (columnTupleAtNat w i)) (actualColumnNext h forward)
        (data.residueOrigin x) a.1 a.2 :=
  retained_word_le_column Q u eligible g L K extra h hL hu a.1 forward a.2 _

end TwoPointCorrelations

end OAI

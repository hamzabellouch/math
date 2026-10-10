import OAI.NumberTheory.TwoPoint.Walks.ColumnHarmonicSum
import OAI.NumberTheory.TwoPoint.Bounds.NumericalColumnCover

namespace OAI

/-! Each actual tuple word has the one-column resampling form used by the forest proof. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

private def cyclicIndex (R : ℕ) (hR : 0 < R) (t : ℕ) : Fin R :=
  ⟨t % R, Nat.mod_lt _ hR⟩

private lemma cyclicIndex_val {R : ℕ} (hR : 0 < R) (t : Fin R) :
    cyclicIndex R hR t.val = t := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt t.isLt

def columnTuple {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (i : Fin R) : ℕ := ∏ j, (w j i).val

def columnTupleWord {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (forward : Fin R → Bool) (padding : Fin R → ℕ) :
    List SignedStep := List.ofFn (fun i => ⟨forward i, columnTuple w i, padding i⟩)

noncomputable def tupleColumnPattern {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J) : ColumnWordPattern (P j) where
  length := R
  label t := w j (cyclicIndex R hR t)
  forward t := forward (cyclicIndex R hR t)
  padding t := padding (cyclicIndex R hR t)
  otherColumns t := ∏ l ∈ univ.erase j, (w l (cyclicIndex R hR t)).val

lemma tupleColumnPattern_label {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J) (i : Fin R) :
    (tupleColumnPattern w hR forward padding j).label i.val = w j i := by
  simp only [tupleColumnPattern, cyclicIndex_val]

lemma columnTuple_split {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (i : Fin R) (j : Fin J) :
    (w j i).val * (∏ l ∈ univ.erase j, (w l i).val) = columnTuple w i := by
  exact mul_prod_erase univ (fun l => (w l i).val) (mem_univ j)

lemma tupleColumnPattern_step {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J) (i : Fin R) :
    (tupleColumnPattern w hR forward padding j).step Subtype.val i.val =
      ⟨forward i, columnTuple w i, padding i⟩ := by
  simp only [ColumnWordPattern.step, tupleColumnPattern, cyclicIndex_val, columnTuple_split]

lemma tupleColumnPattern_word {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J) :
    (tupleColumnPattern w hR forward padding j).word Subtype.val =
      columnTupleWord w forward padding := by
  unfold ColumnWordPattern.word columnTupleWord
  congr 1
  funext i
  exact tupleColumnPattern_step w hR forward padding j i

/-- Disjoint column pools ensure the resampled prime cannot divide any
of the fixed other-column coefficients. -/
lemma tupleColumnPattern_not_dvd_other {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J)
    (hprime : ∀ l, ∀ p ∈ P l, p.Prime) (hdisjoint : ∀ l, l ≠ j → Disjoint (P j) (P l)) :
    ∀ p : P j, ∀ t < R,
      ¬p.val ∣ (tupleColumnPattern w hR forward padding j).otherColumns t := by
  intro p t _ hdiv
  have hp := hprime j p.val p.property
  change p.val ∣ ∏ l ∈ univ.erase j, (w l (cyclicIndex R hR t)).val at hdiv
  have hex := (hp.prime.dvd_finsetProd_iff (S := univ.erase j) (fun l => (w l (cyclicIndex R hR t)).val)).mp hdiv
  obtain ⟨l, hl, hpl⟩ := hex
  have hlne := (mem_erase.mp hl).1
  have hq : (w l (cyclicIndex R hR t)).val = p.val :=
    ((Nat.prime_dvd_prime_iff_eq hp (hprime l _ (w l _).property)).mp hpl).symm
  exact (disjoint_left.mp (hdisjoint l hlne)) p.property (hq ▸ (w l _).property)

end TwoPointCorrelations

end OAI

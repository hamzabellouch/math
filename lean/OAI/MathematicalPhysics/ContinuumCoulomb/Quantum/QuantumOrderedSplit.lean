import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedSupport
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumEntryParity

namespace OAI

/-! Deterministic balanced support factors.  The actual compiler carries
ordered lists of sites and splits them with take/drop; no chosen finite
subset is needed by either subdivision stage. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedSplit
open Matrix
open scoped BigOperators Classical
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def left (xs : List ι) (d : ℕ) : Finset ι := (xs.take d).toFinset
def right (xs : List ι) (d : ℕ) : Finset ι := (xs.drop d).toFinset

omit [Fintype ι] in
theorem union (xs : List ι) (d : ℕ) : left xs d ∪ right xs d = xs.toFinset := by
  rw [left,right,← List.toFinset_append,List.take_append_drop]

omit [Fintype ι] in
theorem disjoint (xs : List ι) (hx : xs.Nodup) (d : ℕ) :
    Disjoint (left xs d) (right xs d) := by
  apply List.disjoint_toFinset_iff_disjoint.mpr
  apply List.disjoint_of_nodup_append
  simpa only [List.take_append_drop] using hx

omit [Fintype ι] in
theorem left_card (xs : List ι) (d : ℕ) : (left xs d).card ≤ d := by
  exact (List.toFinset_card_le _).trans (by simp)

omit [Fintype ι] in
theorem right_card (xs : List ι) (d : ℕ) (hx : xs.length ≤ 2*d) :
    (right xs d).card ≤ d := by
  apply (List.toFinset_card_le _).trans
  rw [List.length_drop]
  omega

def firstWord (xs : List ι) (d : ℕ) (w : ι → Fin 4) : ι → Fin 4 :=
  qmaPauliRestrict (left xs d) w

def secondWord (xs : List ι) (d : ℕ) (w : ι → Fin 4) : ι → Fin 4 :=
  qmaPauliRestrict (right xs d) w

theorem first_support (xs : List ι) (d : ℕ) (w : ι → Fin 4) :
    (qmaPauliSupport (firstWord xs d w)).card ≤ d :=
  (Finset.card_le_card (qmaPauliRestrict_support _ _)).trans (left_card xs d)

theorem second_support (xs : List ι) (d : ℕ) (w : ι → Fin 4)
    (hx : xs.length ≤ 2*d) : (qmaPauliSupport (secondWord xs d w)).card ≤ d :=
  (Finset.card_le_card (qmaPauliRestrict_support _ _)).trans (right_card xs d hx)

theorem factor (xs : List ι) (hx : xs.Nodup) (d : ℕ) (w : ι → Fin 4)
    (hw : qmaPauliSupport w ⊆ xs.toFinset) :
    qmaPauliWord (firstWord xs d w)*qmaPauliWord (secondWord xs d w) = qmaPauliWord w := by
  apply qmaPauliRestrict_factor _ _ _ (disjoint xs hx d)
  rwa [union]

theorem commute (xs : List ι) (hx : xs.Nodup) (d : ℕ) (w : ι → Fin 4) :
    qmaPauliWord (firstWord xs d w)*qmaPauliWord (secondWord xs d w) =
      qmaPauliWord (secondWord xs d w)*qmaPauliWord (firstWord xs d w) :=
  qmaPauliRestrict_commute _ _ _ (disjoint xs hx d)

theorem same_parity (xs : List ι) (hx : xs.Nodup) (d : ℕ) (w : ι → Fin 4)
    (hw : qmaPauliSupport w ⊆ xs.toFinset) (he : Even (qmaPauliYCount w)) :
    decide (Odd (qmaPauliYCount (firstWord xs d w))) =
      decide (Odd (qmaPauliYCount (secondWord xs d w))) := by
  apply qmaPauliRestrict_same_parity _ _ _ (disjoint xs hx d) _ he
  rwa [union]

end ContinuumCoulomb.QuantumOrderedSplit

end

end OAI

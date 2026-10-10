import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedTriple

namespace OAI

/-! Exact Pauli factors from the ordered three-site partition.  The first
two factors have matching Y parity and the last is real. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedTriple
open scoped Classical
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def first (xs : List ι) (w : ι → Fin 4) : ι → Fin 4 :=
  QuantumOrderedSplit.firstWord (partition xs w).1 1 w

def second (xs : List ι) (w : ι → Fin 4) : ι → Fin 4 :=
  QuantumOrderedSplit.secondWord (partition xs w).1 1 w

def third (xs : List ι) (w : ι → Fin 4) : ι → Fin 4 :=
  qmaPauliRestrict (partition xs w).2.toFinset w

def pairWord (xs : List ι) (w : ι → Fin 4) : ι → Fin 4 :=
  qmaPauliRestrict (partition xs w).1.toFinset w

theorem third_yCount (xs : List ι) (w : ι → Fin 4) (hlen : xs.length ≤ 3)
    (hx : xs.Nodup) (hcover : qmaPauliSupport w ⊆ xs.toFinset)
    (he : Even (qmaPauliYCount w)) : qmaPauliYCount (third xs w) = 0 := by
  apply qmaPauliYCount_zero
  intro i
  by_cases hi : i ∈ (partition xs w).2.toFinset
  · simpa only [third,qmaPauliRestrict,hi,ite_true] using
      real_part xs w hlen hx hcover he i (List.mem_toFinset.mp hi)
  · simp [third,qmaPauliRestrict,hi]

theorem pair_support (xs : List ι) (w : ι → Fin 4) (hlen : xs.length ≤ 3) :
    (qmaPauliSupport (pairWord xs w)).card ≤ 2 :=
  (Finset.card_le_card (qmaPauliRestrict_support _ _)).trans
    ((List.toFinset_card_le _).trans (partition_spec xs w hlen).2.1)

theorem pair_even (xs : List ι) (w : ι → Fin 4) (hlen : xs.length ≤ 3)
    (hx : xs.Nodup) (hcover : qmaPauliSupport w ⊆ xs.toFinset)
    (he : Even (qmaPauliYCount w)) : Even (qmaPauliYCount (pairWord xs w)) := by
  have hs := qmaPauliYCount_split (partition xs w).1.toFinset
    (partition xs w).2.toFinset w (partition_disjoint xs w hlen hx)
    (by rw [partition_cover xs w hlen]; exact hcover)
  change qmaPauliYCount (pairWord xs w)+qmaPauliYCount (third xs w) = qmaPauliYCount w at hs
  rw [third_yCount xs w hlen hx hcover he,add_zero] at hs
  rwa [hs]

theorem factors (xs : List ι) (w : ι → Fin 4) (hlen : xs.length ≤ 3)
    (hx : xs.Nodup) (hcover : qmaPauliSupport w ⊆ xs.toFinset)
    (he : Even (qmaPauliYCount w)) :
    (qmaPauliSupport (first xs w)).card ≤ 1 ∧
    (qmaPauliSupport (second xs w)).card ≤ 1 ∧
    (qmaPauliSupport (third xs w)).card ≤ 1 ∧
    qmaPauliWord (first xs w)*qmaPauliWord (second xs w) = qmaPauliWord (pairWord xs w) ∧
    qmaPauliWord (first xs w)*qmaPauliWord (second xs w)*qmaPauliWord (third xs w) = qmaPauliWord w ∧
    qmaPauliWord (first xs w)*qmaPauliWord (second xs w) =
      qmaPauliWord (second xs w)*qmaPauliWord (first xs w) ∧
    qmaPauliWord (first xs w)*qmaPauliWord (third xs w) =
      qmaPauliWord (third xs w)*qmaPauliWord (first xs w) ∧
    qmaPauliWord (second xs w)*qmaPauliWord (third xs w) =
      qmaPauliWord (third xs w)*qmaPauliWord (second xs w) ∧
    decide (Odd (qmaPauliYCount (first xs w))) =
      decide (Odd (qmaPauliYCount (second xs w))) ∧
    Even (qmaPauliYCount (third xs w)) := by
  let P := (partition xs w).1.toFinset
  let C := (partition xs w).2.toFinset
  let L := QuantumOrderedSplit.left (partition xs w).1 1
  let T := QuantumOrderedSplit.right (partition xs w).1 1
  have hplen := (partition_spec xs w hlen).2.1
  have hclen := (partition_spec xs w hlen).2.2
  have hPC : Disjoint P C := partition_disjoint xs w hlen hx
  have hwhole : P ∪ C = xs.toFinset := partition_cover xs w hlen
  have hLT : Disjoint L T := QuantumOrderedSplit.disjoint _ (pair_nodup xs w hlen hx) 1
  have hunion : L ∪ T = P := QuantumOrderedSplit.union _ 1
  have hLP : L ⊆ P := by rw [← hunion]; exact Finset.subset_union_left
  have hTP : T ⊆ P := by rw [← hunion]; exact Finset.subset_union_right
  have hvcover : qmaPauliSupport (pairWord xs w) ⊆ L ∪ T := by
    rw [hunion]
    exact qmaPauliRestrict_support _ _
  have hc0 := third_yCount xs w hlen hx hcover he
  have hv : Even (qmaPauliYCount (pairWord xs w)) := by
    have hs := qmaPauliYCount_split P C w hPC (by rw [hwhole]; exact hcover)
    change qmaPauliYCount (pairWord xs w)+qmaPauliYCount (third xs w) = qmaPauliYCount w at hs
    rw [hc0,add_zero] at hs
    rwa [hs]
  have hab : qmaPauliWord (first xs w)*qmaPauliWord (second xs w) =
      qmaPauliWord (pairWord xs w) := by
    have h := qmaPauliRestrict_factor L T (pairWord xs w) hLT hvcover
    change qmaPauliWord (qmaPauliRestrict L (qmaPauliRestrict P w)) *
      qmaPauliWord (qmaPauliRestrict T (qmaPauliRestrict P w)) = qmaPauliWord (pairWord xs w) at h
    rw [qmaPauliRestrict_restrict L P w hLP,qmaPauliRestrict_restrict T P w hTP] at h
    exact h
  refine ⟨QuantumOrderedSplit.first_support _ 1 w,
    QuantumOrderedSplit.second_support _ 1 w hplen,
    (Finset.card_le_card (qmaPauliRestrict_support _ _)).trans
      ((List.toFinset_card_le _).trans hclen),hab,?_,?_,?_,?_,?_,?_⟩
  · rw [hab]
    exact qmaPauliRestrict_factor P C w hPC (by rw [hwhole]; exact hcover)
  · exact qmaPauliRestrict_commute L T w hLT
  · exact qmaPauliRestrict_commute L C w (hPC.mono_left hLP)
  · exact qmaPauliRestrict_commute T C w (hPC.mono_left hTP)
  · have h := qmaPauliRestrict_same_parity L T (pairWord xs w) hLT hvcover hv
    change decide (Odd (qmaPauliYCount (qmaPauliRestrict L (qmaPauliRestrict P w)))) =
      decide (Odd (qmaPauliYCount (qmaPauliRestrict T (qmaPauliRestrict P w)))) at h
    rw [qmaPauliRestrict_restrict L P w hLP,qmaPauliRestrict_restrict T P w hTP] at h
    exact h
  · rw [hc0]
    norm_num

end ContinuumCoulomb.QuantumOrderedTriple

end

end OAI

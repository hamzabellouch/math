import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPauliLocal

namespace OAI

/-! Balanced disjoint factorizations for the two subdivision stages. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaPauliRestrict (S : Finset ι) (w : ι → Fin 4) : ι → Fin 4 :=
  fun i => if i ∈ S then w i else 0

theorem qmaPauliRestrict_support (S : Finset ι) (w : ι → Fin 4) :
    qmaPauliSupport (qmaPauliRestrict S w) ⊆ S := by
  intro i hi
  by_contra h
  simp [qmaPauliSupport,qmaPauliRestrict,h] at hi

theorem qmaPauliRestrict_commute (S T : Finset ι) (w : ι → Fin 4) (hST : Disjoint S T) :
    qmaPauliWord (qmaPauliRestrict S w)*qmaPauliWord (qmaPauliRestrict T w) =
      qmaPauliWord (qmaPauliRestrict T w)*qmaPauliWord (qmaPauliRestrict S w) := by
  apply qmaPauliWord_disjoint_commute
  intro i
  by_cases hi : i ∈ S
  · right
    have ht : i ∉ T := fun ht => Finset.disjoint_left.mp hST hi ht
    simp [qmaPauliRestrict,ht]
  · left
    simp [qmaPauliRestrict,hi]

theorem qmaPauliRestrict_factor (S T : Finset ι) (w : ι → Fin 4)
    (hST : Disjoint S T) (hcover : qmaPauliSupport w ⊆ S ∪ T) :
    qmaPauliWord (qmaPauliRestrict S w)*qmaPauliWord (qmaPauliRestrict T w) = qmaPauliWord w := by
  ext s t
  rw [qmaPauliWord_mul_apply]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hs : i ∈ S
  · have ht : i ∉ T := fun ht => Finset.disjoint_left.mp hST hs ht
    simp [qmaPauliRestrict,hs,ht,qmaPauli_zero]
  · by_cases ht : i ∈ T
    · simp [qmaPauliRestrict,hs,ht,qmaPauli_zero]
    · have hw : w i = 0 := by
        by_contra h
        have hm := hcover (show i ∈ qmaPauliSupport w by simp [qmaPauliSupport,h])
        simp [hs,ht] at hm
      simp [qmaPauliRestrict,hs,ht,hw,qmaPauli_zero]

omit [Fintype ι] in
theorem qmaBalancedSupport (S : Finset ι) (k : ℕ) (hS : S.card ≤ 2*k) :
    ∃ L R : Finset ι, L.card ≤ k ∧ R.card ≤ k ∧ Disjoint L R ∧ L ∪ R = S := by
  obtain ⟨L,hLS,hL⟩ := Finset.exists_subset_card_eq (s := S) (Nat.min_le_right k S.card)
  refine ⟨L,S \ L,?_,?_,?_,?_⟩
  · rw [hL]
    exact Nat.min_le_left _ _
  · rw [Finset.card_sdiff_of_subset hLS,hL]
    omega
  · exact Finset.disjoint_left.mpr (fun i hi hR => (Finset.mem_sdiff.mp hR).2 hi)
  · ext i
    constructor
    · intro hi
      rcases Finset.mem_union.mp hi with h | h
      · exact hLS h
      · exact (Finset.mem_sdiff.mp h).1
    · intro hi
      by_cases hL : i ∈ L
      · exact Finset.mem_union_left _ hL
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hi,hL⟩)

theorem qmaPauliWord_balanced_factor (w : ι → Fin 4) (k : ℕ)
    (hw : (qmaPauliSupport w).card ≤ 2*k) :
    ∃ a b : ι → Fin 4, (qmaPauliSupport a).card ≤ k ∧ (qmaPauliSupport b).card ≤ k ∧
      qmaPauliWord a*qmaPauliWord b = qmaPauliWord w ∧
      qmaPauliWord a*qmaPauliWord b = qmaPauliWord b*qmaPauliWord a := by
  obtain ⟨L,R,hL,hR,hLR,hcover⟩ := qmaBalancedSupport (qmaPauliSupport w) k hw
  refine ⟨qmaPauliRestrict L w,qmaPauliRestrict R w,
    (Finset.card_le_card (qmaPauliRestrict_support L w)).trans hL,
    (Finset.card_le_card (qmaPauliRestrict_support R w)).trans hR,?_,
    qmaPauliRestrict_commute L R w hLR⟩
  apply qmaPauliRestrict_factor L R w hLR
  rw [hcover]

end ContinuumCoulomb

end

end OAI

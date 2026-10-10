import OAI.Analysis.LipschitzHilbert.Trees.SourceOrdinaryDensityForest

namespace OAI

/-! Exact grouping by an assignment defined only on the selected packets. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

def assignedPacketSet {ι J : Type*} (S : Finset ι) (assigned : S → J) (j : J) : Finset ι :=
  S.filter fun q => ∃ hq : q∈S, assigned ⟨q,hq⟩=j

theorem assignedPacketSet_subset {ι J : Type*} (S : Finset ι) (assigned : S → J) (j : J) :
    assignedPacketSet S assigned j ⊆ S := Finset.filter_subset _ _

theorem mem_assignedPacketSet {ι J : Type*} (S : Finset ι) (assigned : S → J)
    (j : J) (q : ι) (hq : q∈assignedPacketSet S assigned j) :
    ∃ hqS : q∈S, assigned ⟨q,hqS⟩=j := (Finset.mem_filter.mp hq).2

theorem sum_assignedPacketSets {ι J V : Type*} [Fintype J] [AddCommMonoid V]
    (S : Finset ι) (assigned : S → J) (F : ι → V) :
    (∑ j, ∑ q∈assignedPacketSet S assigned j, F q)=∑ q∈S, F q := by
  classical
  simp only [assignedPacketSet,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  have hpred (j : J) : (∃ h : q∈S, assigned ⟨q,h⟩=j) ↔ assigned ⟨q,hq⟩=j := by
    constructor
    · rintro ⟨h,he⟩
      exact he
    · intro he
      exact ⟨hq,he⟩
  simp only [hpred]
  simp

end LipschitzHilbert

end

end OAI

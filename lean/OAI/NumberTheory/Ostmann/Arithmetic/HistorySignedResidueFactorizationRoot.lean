import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSupportReductionArithmetic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidueFactorization
open Construction HistorySignedDecode HistorySignedSupportReduction

def RootSmallUnits {l : ℕ} (h : History l) (Xp Xm : ℤ) : Prop :=
  Nat.Coprime Xp.natAbs (h.root.small.map SmallSlot.value).prod ∧
    Nat.Coprime Xm.natAbs (h.root.small.map SmallSlot.value).prod

theorem rootSmallUnits_iff {l : ℕ} (h : History l) (Xp Xm : ℤ) :
    RootSmallUnits h Xp Xm ↔ ∀q∈h.root.small,
      Nat.Coprime Xp.natAbs q.value ∧ Nat.Coprime Xm.natAbs q.value := by
  simp only [RootSmallUnits,Nat.coprime_list_prod_right_iff,List.mem_map]
  constructor
  · rintro ⟨hp,hm⟩ q hq
    exact ⟨hp q.value ⟨q,hq,rfl⟩,hm q.value ⟨q,hq,rfl⟩⟩
  · intro hu
    constructor <;> intro n hn <;> obtain ⟨q,hq,rfl⟩ := hn
    · exact (hu q hq).1
    · exact (hu q hq).2

theorem root_small_outside_pairwise {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) :
    (h.root.small.map SmallSlot.value++outside).Pairwise Nat.Coprime := by
  have hc := History.supported_root_coprime hs
  change ((h.root.giantPlus::h.root.giantMinus::h.root.small.map SmallSlot.value)++outside).Pairwise
    Nat.Coprime at hc
  simp only [List.cons_append,List.pairwise_cons] at hc
  exact hc.2.2

theorem residueRootCoprime_rebuild_iff {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (Xp Xm : ℤ)
    (ho : ∀q∈outside,Nat.Coprime Xp.natAbs q ∧ Nat.Coprime Xm.natAbs q) :
    ResidueRootCoprime outside (rebuild h Xp Xm).root ↔ RootSmallUnits h Xp Xm := by
  rw [rebuild_root]
  change ((h.root.small.map SmallSlot.value++outside).Pairwise Nat.Coprime ∧
    ∀q∈h.root.small.map SmallSlot.value++outside,
      Nat.Coprime Xp.natAbs q ∧ Nat.Coprime Xm.natAbs q) ↔ _
  rw [rootSmallUnits_iff]
  constructor
  · intro hr q hq
    exact hr.2 q.value (List.mem_append_left _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  · intro hr
    refine ⟨root_small_outside_pairwise h hs,?_⟩
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
      exact hr p hp
    · exact ho q hq

end Ostmann.Arithmetic.HistorySignedResidueFactorization

end

end OAI

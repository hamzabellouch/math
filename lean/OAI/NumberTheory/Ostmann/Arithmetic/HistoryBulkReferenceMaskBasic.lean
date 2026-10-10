import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorizationBlockDefs

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceMask
open Construction HistorySignedResidueFactorization HistoryCRTIntegration

theorem state_coprime_iff (a : State) (outside : List ℕ) :
    a.Coprime outside ↔
      (a.small.map SmallSlot.value++outside).Pairwise Nat.Coprime ∧
      Nat.Coprime a.giantPlus a.giantMinus ∧
      (Nat.Coprime a.giantPlus (a.small.map SmallSlot.value).prod ∧
        Nat.Coprime a.giantMinus (a.small.map SmallSlot.value).prod) ∧
      (∀q∈outside,Nat.Coprime a.giantPlus q ∧ Nat.Coprime a.giantMinus q) := by
  simp only [State.Coprime,State.values,List.cons_append,List.pairwise_cons,
    List.mem_cons,List.mem_append,or_imp,forall_and,forall_eq,
    Nat.coprime_list_prod_right_iff]
  tauto

theorem root_small_units_nat_iff {l : ℕ} (h : History l) (P Q : ℕ) :
    (Nat.Coprime P (rootModulus h) ∧ Nat.Coprime Q (rootModulus h)) ↔
      IsUnit (P:ZMod (rootModulus h)) ∧ IsUnit (Q:ZMod (rootModulus h)) := by
  have hu := rootSmallUnits_iff_isUnit h (P:ℤ) (Q:ℤ)
  simp only [RootSmallUnits,Int.natAbs_natCast,Int.cast_natCast] at hu
  simpa only [rootModulus] using hu

theorem root_coprime_iff_of_outside_units {l : ℕ} (h : History l) (outside : List ℕ)
    (ho : ∀q∈outside,Nat.Coprime h.root.giantPlus q ∧ Nat.Coprime h.root.giantMinus q) :
    h.root.Coprime outside ↔
      (h.root.small.map SmallSlot.value++outside).Pairwise Nat.Coprime ∧
      Nat.Coprime h.root.giantPlus h.root.giantMinus ∧
      (IsUnit (h.root.giantPlus:ZMod (rootModulus h)) ∧
        IsUnit (h.root.giantMinus:ZMod (rootModulus h))) := by
  rw [state_coprime_iff]
  change (_ ∧ _ ∧ ((Nat.Coprime h.root.giantPlus (rootModulus h) ∧
    Nat.Coprime h.root.giantMinus (rootModulus h)) ∧ _)) ↔ _
  rw [root_small_units_nat_iff]
  tauto

theorem root_mask_eq_of_outside_units {l : ℕ} (h : History l) (outside : List ℕ)
    (ho : ∀q∈outside,Nat.Coprime h.root.giantPlus q ∧ Nat.Coprime h.root.giantMinus q) :
    guardIndicator (h.root.Coprime outside) =
      guardIndicator ((h.root.small.map SmallSlot.value++outside).Pairwise Nat.Coprime)*
      guardIndicator (Nat.Coprime h.root.giantPlus h.root.giantMinus)*
      rootResidueIndicator h (h.root.giantPlus,h.root.giantMinus) := by
  rw [root_coprime_iff_of_outside_units h outside ho,guardIndicator_and,guardIndicator_and]
  simp only [rootResidueIndicator,mul_assoc]

end Ostmann.Arithmetic.HistoryBulkReferenceMask

end

end OAI

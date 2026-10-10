import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceMaskBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceMask
open Construction HistorySignedResidueFactorization HistoryCRTIntegration

theorem pair_root_coprime_iff_of_outside_units {l : ℕ} (h k : History l)
    (outside : List ℕ)
    (hp : k.root.giantPlus=h.root.giantPlus)
    (hm : k.root.giantMinus=h.root.giantMinus)
    (hmod : rootModulus k=rootModulus h)
    (ho : ∀q∈outside,Nat.Coprime h.root.giantPlus q ∧ Nat.Coprime h.root.giantMinus q) :
    (h.root.Coprime outside ∧ k.root.Coprime outside) ↔
      ((h.root.small.map SmallSlot.value++outside).Pairwise Nat.Coprime ∧
        (k.root.small.map SmallSlot.value++outside).Pairwise Nat.Coprime) ∧
      Nat.Coprime h.root.giantPlus h.root.giantMinus ∧
      (IsUnit (h.root.giantPlus:ZMod (rootModulus h)) ∧
        IsUnit (h.root.giantMinus:ZMod (rootModulus h))) := by
  rw [←root_small_units_nat_iff]
  rw [state_coprime_iff,state_coprime_iff]
  simp only [rootModulus] at hmod ⊢
  simp only [hp,hm,hmod]
  tauto

theorem pair_root_mask_eq_of_outside_units {l : ℕ} (h k : History l)
    (outside : List ℕ)
    (hp : k.root.giantPlus=h.root.giantPlus)
    (hm : k.root.giantMinus=h.root.giantMinus)
    (hmod : rootModulus k=rootModulus h)
    (ho : ∀q∈outside,Nat.Coprime h.root.giantPlus q ∧ Nat.Coprime h.root.giantMinus q) :
    guardIndicator (h.root.Coprime outside ∧ k.root.Coprime outside) =
      guardIndicator ((h.root.small.map SmallSlot.value++outside).Pairwise Nat.Coprime ∧
        (k.root.small.map SmallSlot.value++outside).Pairwise Nat.Coprime)*
      guardIndicator (Nat.Coprime h.root.giantPlus h.root.giantMinus)*
      rootResidueIndicator h (h.root.giantPlus,h.root.giantMinus) := by
  rw [pair_root_coprime_iff_of_outside_units h k outside hp hm hmod ho]
  simp only [rootResidueIndicator,guardIndicator_and,mul_assoc]

end Ostmann.Arithmetic.HistoryBulkReferenceMask

end

end OAI

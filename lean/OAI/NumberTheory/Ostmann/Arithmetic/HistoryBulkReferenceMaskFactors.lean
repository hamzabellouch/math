import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceMaskPair
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceMaskSpectator

namespace OAI

open Erdos970

noncomputable section
open scoped Classical
namespace Ostmann.Arithmetic.HistoryBulkReferenceMask
open Construction HistorySignedResidueFactorization HistoryCRTIntegration HistorySignedSpectatorCRT

theorem pair_root_mask_mul_spectator {l : ℕ} (h k : History l)
    (g : (q:ℕ)→ZMod q→ℂ) (outside : List ℕ)
    (hprime : ∀q∈outside,q.Prime) (hg : ∀q∈outside,g q 0=0)
    (P Q : ℤ) (hP : (h.root.giantPlus:ℤ)=P) (hQ : (h.root.giantMinus:ℤ)=Q)
    (hp : k.root.giantPlus=h.root.giantPlus) (hm : k.root.giantMinus=h.root.giantMinus)
    (hmod : rootModulus k=rootModulus h) :
    guardIndicator (h.root.Coprime outside ∧ k.root.Coprime outside)*
      residuePairSpectator g outside outside.prod h k (P,Q) =
    guardIndicator ((h.root.small.map SmallSlot.value++outside).Pairwise Nat.Coprime ∧
      (k.root.small.map SmallSlot.value++outside).Pairwise Nat.Coprime)*
      guardIndicator (Nat.Coprime P.natAbs Q.natAbs)*rootResidueIndicator h (P,Q)*
      residuePairSpectator g outside outside.prod h k (P,Q) := by
  by_cases hz : residuePairSpectator g outside outside.prod h k (P,Q)=0
  · simp only [hz,mul_zero]
  have hu := residuePairSpectator_nonzero_outsideCoprime_prod g outside hprime hg h k P Q hz
  have hPa : h.root.giantPlus=P.natAbs := by
    simpa only [Int.natAbs_natCast] using congrArg Int.natAbs hP
  have hQa : h.root.giantMinus=Q.natAbs := by
    simpa only [Int.natAbs_natCast] using congrArg Int.natAbs hQ
  have ho : ∀q∈outside,Nat.Coprime h.root.giantPlus q ∧ Nat.Coprime h.root.giantMinus q := by
    simpa only [hPa,hQa] using hu
  have hmask := pair_root_mask_eq_of_outside_units h k outside hp hm hmod ho
  have hPc : (h.root.giantPlus:ZMod (rootModulus h))=(P:ZMod (rootModulus h)) := by
    rw [←Int.cast_natCast,hP]
  have hQc : (h.root.giantMinus:ZMod (rootModulus h))=(Q:ZMod (rootModulus h)) := by
    rw [←Int.cast_natCast,hQ]
  rw [hPc,hQc,hPa,hQa] at hmask
  rw [hmask]

theorem pair_guarded_product_eq {l : ℕ} (h k : History l)
    (g : (q:ℕ)→ZMod q→ℂ) (outside : List ℕ)
    (hprime : ∀q∈outside,q.Prime) (hg : ∀q∈outside,g q 0=0)
    (P Q : ℤ) (hP : (h.root.giantPlus:ℤ)=P) (hQ : (h.root.giantMinus:ℤ)=Q)
    (hp : k.root.giantPlus=h.root.giantPlus) (hm : k.root.giantMinus=h.root.giantMinus)
    (hmod : rootModulus k=rootModulus h) (F : ℂ) :
    (if h.root.Coprime outside ∧ k.root.Coprime outside then
      F*residuePairSpectator g outside outside.prod h k (P,Q) else 0) =
    guardIndicator ((h.root.small.map SmallSlot.value++outside).Pairwise Nat.Coprime ∧
      (k.root.small.map SmallSlot.value++outside).Pairwise Nat.Coprime)*
      guardIndicator (Nat.Coprime P.natAbs Q.natAbs)*rootResidueIndicator h (P,Q)*
      F*residuePairSpectator g outside outside.prod h k (P,Q) := by
  classical
  have hmasks := congrArg (fun z:ℂ => F*z)
    (pair_root_mask_mul_spectator h k g outside hprime hg P Q hP hQ hp hm hmod)
  calc
    _ = F*(guardIndicator (h.root.Coprime outside ∧ k.root.Coprime outside)*
        residuePairSpectator g outside outside.prod h k (P,Q)) := by
      by_cases hc : h.root.Coprime outside ∧ k.root.Coprime outside <;>
        simp [guardIndicator,hc]
    _ = _ := by rw [hmasks]; ring

end Ostmann.Arithmetic.HistoryBulkReferenceMask

end

end OAI

import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCRTIntegrationModuli
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorizationRoot

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidueFactorization
open Construction HistoryCRTIntegration

theorem rootSmallUnits_iff_isUnit {l : ℕ} (h : History l) (Xp Xm : ℤ) :
    RootSmallUnits h Xp Xm ↔
      IsUnit (Xp:ZMod (rootModulus h)) ∧ IsUnit (Xm:ZMod (rootModulus h)) := by
  have hu (z : ℤ) : Nat.Coprime z.natAbs (rootModulus h) ↔
      IsUnit (z:ZMod (rootModulus h)) := by
    rw [ZMod.coe_int_isUnit_iff_isCoprime,Int.isCoprime_iff_nat_coprime,
      Int.natAbs_natCast]
    exact Nat.coprime_comm
  exact and_congr (hu Xp) (hu Xm)

theorem rootSmallUnits_pair_iff_isUnit {l : ℕ} (h k : History l)
    (hsmall : h.root.small.Perm k.root.small) (Xp Xm : ℤ) :
    (RootSmallUnits h Xp Xm ∧ RootSmallUnits k Xp Xm) ↔
      IsUnit (Xp:ZMod (rootModulus h)) ∧ IsUnit (Xm:ZMod (rootModulus h)) := by
  have he : rootModulus h=rootModulus k := (hsmall.map SmallSlot.value).prod_eq
  rw [rootSmallUnits_iff_isUnit,rootSmallUnits_iff_isUnit,←he,and_self]

end Ostmann.Arithmetic.HistorySignedResidueFactorization

end

end OAI

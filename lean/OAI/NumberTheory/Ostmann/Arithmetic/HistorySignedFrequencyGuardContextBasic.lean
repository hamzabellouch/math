import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyContext
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesModulus

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryFrequencyResidues
open Construction HistorySignedDecode HistorySignedSupportReduction

def knownRootFrequencyUnits (R j : ℕ) (F : List ℤ) (g : KnownGiants R) : Prop :=
  ∀s∈F, IsUnit (ZMod.cast (g j).1 : ZMod s.natAbs) ∧
    IsUnit (ZMod.cast (g j).2 : ZMod s.natAbs)

theorem knownRootFrequencyUnits_iff (R j : ℕ) (F : List ℤ)
    (hF : ∀s∈F,s.natAbs∣R) (g : KnownGiants R) (Xp Xm : ℤ)
    (hg : SignedGiantsMatch R j g Xp Xm) :
    knownRootFrequencyUnits R j F g ↔
      ∀s∈F,Nat.Coprime Xp.natAbs s.natAbs ∧ Nat.Coprime Xm.natAbs s.natAbs := by
  apply forall_congr'
  intro s
  apply forall_congr'
  intro hs
  have hd : s.natAbs∣R^(j+2) := (hF s hs).trans (dvd_pow_self R (by omega))
  change (IsUnit (ZMod.cast (g j).1:ZMod s.natAbs) ∧
    IsUnit (ZMod.cast (g j).2:ZMod s.natAbs)) ↔ _
  rw [hg.1,hg.2,ZMod.cast_intCast hd,ZMod.cast_intCast hd,
    ZMod.coe_int_isUnit_iff_isCoprime,ZMod.coe_int_isUnit_iff_isCoprime,
    Int.isCoprime_iff_nat_coprime,Int.isCoprime_iff_nat_coprime,
    Int.natAbs_natCast]
  exact and_congr Nat.coprime_comm Nat.coprime_comm

end Ostmann.Arithmetic.HistoryFrequencyResidues

end

end OAI

import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorCRTResidue

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedSpectatorDiagram
open Construction HistorySignedResidues HistorySignedSpectatorCRT

theorem zmod_cast_inv_of_unit {N q : ℕ} (hq : q ∣ N) (a : ZMod N) (ha : IsUnit a) :
    (ZMod.cast (a⁻¹) : ZMod q) = (ZMod.cast a : ZMod q)⁻¹ := by
  symm
  apply ZMod.inv_eq_of_mul_eq_one
  have he := congrArg (ZMod.castHom hq (ZMod q)) (ZMod.mul_inv_of_unit a ha)
  simpa only [map_mul,map_one,ZMod.castHom_apply] using he

theorem residuePivot_cast {N q : ℕ} (hq : q ∣ N) (a : State) (v w : ℤ)
    (u hp hm : List SmallSlot) (Xp Xm : ZMod N)
    (hc : Nat.Coprime (a.frequency*((u.map SmallSlot.value).prod:ℤ)).natAbs N) :
    (ZMod.cast (residuePivot N a v w u hp hm Xp Xm) : ZMod q) =
      residuePivot q a v w u hp hm (ZMod.cast Xp) (ZMod.cast Xm) := by
  have hu' : IsUnit ((a.frequency*((u.map SmallSlot.value).prod:ℤ):ℤ):ZMod N) :=
    (ZMod.coe_int_isUnit_iff_isCoprime _ N).mpr
      (Int.isCoprime_iff_gcd_eq_one.mpr
        (by simpa only [Int.gcd,Int.natAbs_natCast] using hc.symm))
  have hu : IsUnit ((a.frequency:ZMod N)*((u.map SmallSlot.value).prod:ZMod N)) := by
    simpa only [Int.cast_mul,Int.cast_natCast] using hu'
  simp only [residuePivot,ZMod.cast_mul hq,zmod_cast_inv_of_unit hq _ hu,
    ZMod.cast_sub hq,ZMod.cast_intCast hq,ZMod.cast_natCast hq]

end Ostmann.Arithmetic.HistorySignedSpectatorDiagram

end

end OAI

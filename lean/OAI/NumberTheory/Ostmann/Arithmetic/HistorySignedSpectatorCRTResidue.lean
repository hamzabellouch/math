import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorCRTBasic

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Arithmetic.HistorySignedSpectatorCRT
open Construction HistorySignedDecode HistorySignedResidues

def residuePivot (N : ℕ) (a : State) (v w : ℤ) (u hp hm : List SmallSlot)
    (Xp Xm : ZMod N) : ZMod N :=
  ((v:ZMod N)*(Xm*((hm.map SmallSlot.value).prod:ZMod N))-
    (w:ZMod N)*(Xp*((hp.map SmallSlot.value).prod:ZMod N)))*
    ((a.frequency:ZMod N)*((u.map SmallSlot.value).prod:ZMod N))⁻¹

def residueLeaf (g : (q:ℕ)→ZMod q→ℂ) (outside : List ℕ) (N : ℕ) (a : State)
    (Xp Xm : ZMod N) : ℂ :=
  (outside.map (fun q=>g q ((a.frequency:ZMod q)*
    (((outsideProduct outside/q:ℕ):ZMod q)*
      ((ZMod.cast Xp:ZMod q)*(ZMod.cast Xm:ZMod q)*
        ((a.small.map SmallSlot.value).prod:ZMod q)))⁻¹))).prod

def residueSpectator (g : (q:ℕ)→ZMod q→ℂ) (outside : List ℕ) (N : ℕ) :
    {l : ℕ}→History l→ZMod N→ZMod N→ℂ
  | _,.leaf a,Xp,Xm => residueLeaf g outside N a Xp Xm
  | _,.node a _ u hp hm left right,Xp,Xm =>
    let p := residuePivot N a left.root.frequency right.root.frequency u hp hm Xp Xm
    residueSpectator g outside N left p Xp*conj (residueSpectator g outside N right p Xm)

def residuePairSpectator (g : (q:ℕ)→ZMod q→ℂ) (outside : List ℕ) (N : ℕ)
    {l : ℕ} (h k : History l) (z : ZMod N×ZMod N) : ℂ :=
  residueSpectator g outside N h z.1 z.2*conj (residueSpectator g outside N k z.1 z.2)

theorem quotient_intCast {a d : ℤ} {N : ℕ} (ha : d∣a)
    (hc : Nat.Coprime d.natAbs N) : ((a/d:ℤ):ZMod N)=(a:ZMod N)*(d:ZMod N)⁻¹ := by
  have hu : IsUnit (d:ZMod N) := (ZMod.coe_int_isUnit_iff_isCoprime d N).mpr
    (Int.isCoprime_iff_gcd_eq_one.mpr (by simpa only [Int.gcd,Int.natAbs_natCast] using hc.symm))
  have he : (d:ZMod N)*((a/d:ℤ):ZMod N)=(a:ZMod N) := by
    simpa only [Int.cast_mul] using congrArg (fun z : ℤ=>(z:ZMod N)) (Int.mul_ediv_cancel' ha)
  calc
    ((a/d:ℤ):ZMod N)=((a/d:ℤ):ZMod N)*((d:ZMod N)*(d:ZMod N)⁻¹) := by
      rw [ZMod.mul_inv_of_unit _ hu,mul_one]
    _ = (a:ZMod N)*(d:ZMod N)⁻¹ := by
      rw [←mul_assoc,mul_comm ((a/d:ℤ):ZMod N),he]

theorem residuePivot_intCast {N : ℕ} (a : State) (v w : ℤ)
    (u hp hm : List SmallSlot) (Xp Xm : ℤ)
    (hc : Nat.Coprime (a.frequency*((u.map SmallSlot.value).prod:ℤ)).natAbs N)
    (hi : a.frequency*((u.map SmallSlot.value).prod:ℤ)∣
      reversalNumerator v w (Xp*((hp.map SmallSlot.value).prod:ℤ))
        (Xm*((hm.map SmallSlot.value).prod:ℤ))) :
    residuePivot N a v w u hp hm Xp Xm=
      (signedPivot ⟨a.frequency,Xp,Xm,a.small⟩ v w u hp hm:ZMod N) := by
  simpa only [residuePivot,signedPivot,reversalNumerator,Int.cast_sub,Int.cast_mul,
    Int.cast_natCast] using (quotient_intCast hi hc).symm

theorem residueLeaf_intCast {N : ℕ} (g : (q:ℕ)→ZMod q→ℂ) (outside : List ℕ)
    (hd : ∀q∈outside,q∣N) (a : State) (Xp Xm : ℤ) :
    residueLeaf g outside N a Xp Xm=
      HistorySignedSpectator.spectatorFactor g outside ⟨a.frequency,Xp,Xm,a.small⟩ := by
  unfold residueLeaf HistorySignedSpectator.spectatorFactor
  congr 1
  apply List.map_congr_left
  intro q hq
  simp only [ZMod.cast_intCast (hd q hq),HistorySignedSpectator.argument,
    HistorySignedSpectator.stateProduct,Int.cast_mul,Int.cast_natCast]

theorem residueSpectator_intCast {l : ℕ} (h : History l)
    (g : (q:ℕ)→ZMod q→ℂ) (outside : List ℕ) (R : ℤ) (N : ℕ)
    (hd : ∀q∈outside,q∣N) (hdiv : DivisorData R h) (hc : Nat.Coprime R.natAbs N)
    (Xp Xm : ℤ) (hi : (rebuild h Xp Xm).IntegralGuard) :
    residueSpectator g outside N h Xp Xm=
      HistorySignedSpectator.spectatorProduct g outside (rebuild h Xp Xm) := by
  induction h generalizing Xp Xm with
  | leaf a => exact residueLeaf_intCast g outside hd a Xp Xm
  | node a p u hp hm left right il ir =>
    simp only [rebuild,SignedHistory.IntegralGuard,rebuild_root] at hi
    have hcop := hc.of_dvd_left (Int.natAbs_dvd_natAbs.mpr hdiv.2.1)
    simp only [residueSpectator]
    rw [residuePivot_intCast a left.root.frequency right.root.frequency u hp hm Xp Xm hcop hi.2.1,
      il hdiv.2.2.1 _ _ hi.2.2.1,ir hdiv.2.2.2 _ _ hi.2.2.2]
    rfl

end Ostmann.Arithmetic.HistorySignedSpectatorCRT

end

end OAI

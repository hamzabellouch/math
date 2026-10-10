import Mathlib.Data.ZMod.Units
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedDecodeRebuild
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorBasic

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Arithmetic.HistorySignedSpectator
open Construction HistorySignedDecode

def GiantOutsideUnits (outside : List ℕ) (a : SignedState) : Prop :=
  ∀ q ∈ outside, Nat.Coprime a.giantPlus.natAbs q ∧ Nat.Coprime a.giantMinus.natAbs q

def OutsideUnits (outside : List ℕ) : {l : ℕ} → SignedHistory l → Prop
  | _, .leaf a => GiantOutsideUnits outside a
  | _, .node a p _ _ _ left right =>
    GiantOutsideUnits outside a ∧ (∀ q ∈ outside, Nat.Coprime p.natAbs q) ∧
      OutsideUnits outside left ∧ OutsideUnits outside right

theorem OutsideUnits.root {outside : List ℕ} {l : ℕ} {h : SignedHistory l}
    (hu : OutsideUnits outside h) : GiantOutsideUnits outside h.root := by
  cases h
  · exact hu
  · exact hu.1

theorem spectatorFactor_component_ne_zero (g : (q : ℕ) → ZMod q → ℂ)
    (outside : List ℕ) (a : SignedState) (hz : spectatorFactor g outside a ≠ 0)
    (q : ℕ) (hq : q ∈ outside) : g q (argument outside q a) ≠ 0 := by
  intro heq
  apply hz
  apply List.prod_eq_zero_iff.mpr
  exact List.mem_map.mpr ⟨q, hq, heq⟩

theorem spectatorFactor_denominator_ne_zero (g : (q : ℕ) → ZMod q → ℂ)
    (outside : List ℕ) (a : SignedState) (hz : spectatorFactor g outside a ≠ 0)
    (q : ℕ) (hq : q ∈ outside) (hg : g q 0 = 0) :
    ((((outsideProduct outside / q : ℕ) : ℤ) * stateProduct a : ℤ) : ZMod q) ≠ 0 := by
  intro hd
  apply spectatorFactor_component_ne_zero g outside a hz q hq
  simp only [argument, hd, ZMod.inv_zero, mul_zero, hg]

theorem spectatorFactor_nonzero_giantOutsideUnits (g : (q : ℕ) → ZMod q → ℂ)
    (outside : List ℕ) (hprime : ∀ q ∈ outside, q.Prime)
    (hg : ∀ q ∈ outside, g q 0 = 0) (a : SignedState)
    (hz : spectatorFactor g outside a ≠ 0) : GiantOutsideUnits outside a := by
  intro q hq
  let : Fact q.Prime := ⟨hprime q hq⟩
  have hd := spectatorFactor_denominator_ne_zero g outside a hz q hq (hg q hq)
  have hplus : (a.giantPlus : ZMod q) ≠ 0 := by
    intro hp
    apply hd
    simp only [stateProduct, Int.cast_mul, hp, zero_mul, mul_zero]
  have hminus : (a.giantMinus : ZMod q) ≠ 0 := by
    intro hm
    apply hd
    simp only [stateProduct, Int.cast_mul, hm, mul_zero, zero_mul]
  have hcop (z : ℤ) (hz : (z : ZMod q) ≠ 0) : Nat.Coprime z.natAbs q := by
    have hc := (ZMod.coe_int_isUnit_iff_isCoprime z q).mp (isUnit_iff_ne_zero.mpr hz)
    simpa only [Int.natAbs_natCast] using (Int.isCoprime_iff_nat_coprime.mp hc).symm
  exact ⟨hcop _ hplus, hcop _ hminus⟩

theorem spectatorProduct_nonzero_rebuild_outsideUnits
    (g : (q : ℕ) → ZMod q → ℂ) (outside : List ℕ)
    (hprime : ∀ q ∈ outside, q.Prime) (hg : ∀ q ∈ outside, g q 0 = 0)
    {l : ℕ} (h : History l) (Xp Xm : ℤ)
    (hz : spectatorProduct g outside (rebuild h Xp Xm) ≠ 0) :
    OutsideUnits outside (rebuild h Xp Xm) := by
  induction h generalizing Xp Xm with
  | leaf a => exact spectatorFactor_nonzero_giantOutsideUnits g outside hprime hg _ hz
  | node a p u hp hm left right ihl ihr =>
    let P := signedPivot ⟨a.frequency, Xp, Xm, a.small⟩
      left.root.frequency right.root.frequency u hp hm
    have hzL : spectatorProduct g outside (rebuild left P Xp) ≠ 0 := by
      intro hzero
      apply hz
      change spectatorProduct g outside (rebuild left P Xp) *
        conj (spectatorProduct g outside (rebuild right P Xm)) = 0
      rw [hzero, zero_mul]
    have hzR : spectatorProduct g outside (rebuild right P Xm) ≠ 0 := by
      intro hzero
      apply hz
      change spectatorProduct g outside (rebuild left P Xp) *
        conj (spectatorProduct g outside (rebuild right P Xm)) = 0
      rw [hzero, map_zero, mul_zero]
    have hl := ihl P Xp hzL
    have hr := ihr P Xm hzR
    refine ⟨?_, ?_, hl, hr⟩
    · intro q hq
      have hleft := hl.root q hq
      have hright := hr.root q hq
      simpa only [rebuild_root] using And.intro hleft.2 hright.2
    · intro q hq
      simpa only [rebuild_root] using (hl.root q hq).1

theorem pairSpectator_nonzero_rebuild_outsideUnits
    (g : (q : ℕ) → ZMod q → ℂ) (outside : List ℕ)
    (hprime : ∀ q ∈ outside, q.Prime) (hg : ∀ q ∈ outside, g q 0 = 0)
    {l : ℕ} (h k : History l) (Xp Xm Yp Ym : ℤ)
    (hz : pairSpectator g outside (rebuild h Xp Xm) (rebuild k Yp Ym) ≠ 0) :
    OutsideUnits outside (rebuild h Xp Xm) ∧ OutsideUnits outside (rebuild k Yp Ym) := by
  have hzL : spectatorProduct g outside (rebuild h Xp Xm) ≠ 0 := by
    intro hzero
    exact hz (by simp only [pairSpectator, hzero, zero_mul])
  have hzR : spectatorProduct g outside (rebuild k Yp Ym) ≠ 0 := by
    intro hzero
    exact hz (by simp only [pairSpectator, hzero, map_zero, mul_zero])
  exact ⟨spectatorProduct_nonzero_rebuild_outsideUnits g outside hprime hg h Xp Xm hzL,
    spectatorProduct_nonzero_rebuild_outsideUnits g outside hprime hg k Yp Ym hzR⟩

theorem pairSpectator_eq_zero_of_not_rebuild_outsideUnits
    (g : (q : ℕ) → ZMod q → ℂ) (outside : List ℕ)
    (hprime : ∀ q ∈ outside, q.Prime) (hg : ∀ q ∈ outside, g q 0 = 0)
    {l : ℕ} (h k : History l) (Xp Xm Yp Ym : ℤ)
    (hu : ¬(OutsideUnits outside (rebuild h Xp Xm) ∧ OutsideUnits outside (rebuild k Yp Ym))) :
    pairSpectator g outside (rebuild h Xp Xm) (rebuild k Yp Ym) = 0 := by
  by_contra hz
  exact hu (pairSpectator_nonzero_rebuild_outsideUnits g outside hprime hg h k Xp Xm Yp Ym hz)

end Ostmann.Arithmetic.HistorySignedSpectator

end

end OAI

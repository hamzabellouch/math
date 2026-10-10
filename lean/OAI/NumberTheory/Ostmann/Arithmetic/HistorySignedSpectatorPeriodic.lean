import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorBasic

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Arithmetic.HistorySignedSpectator
open Construction HistorySignedDecode HistorySignedResidues

theorem argument_eq_of_congruent {N : ℤ} (outside : List ℕ) (q : ℕ)
    (hd : (q:ℤ)∣N) (a b : SignedState) (hc : StateCongruent N a b) :
    argument outside q a=argument outside q b := by
  have hp : (a.giantPlus:ZMod q)=(b.giantPlus:ZMod q) :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mpr (hc.2.2.1.of_dvd hd)
  have hm : (a.giantMinus:ZMod q)=(b.giantMinus:ZMod q) :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mpr (hc.2.2.2.of_dvd hd)
  simp only [argument,stateProduct,Int.cast_mul,Int.cast_natCast,hc.1,hc.2.1,hp,hm]

theorem spectatorFactor_eq_of_congruent {N : ℤ} (g : (q:ℕ)→ZMod q→ℂ) (outside : List ℕ)
    (hd : ∀q∈outside,(q:ℤ)∣N) (a b : SignedState) (hc : StateCongruent N a b) :
    spectatorFactor g outside a=spectatorFactor g outside b := by
  unfold spectatorFactor
  congr 1
  apply List.map_congr_left
  intro q hq
  rw [argument_eq_of_congruent outside q (hd q hq) a b hc]

theorem spectatorProduct_eq_of_congruent {N : ℤ} (g : (q:ℕ)→ZMod q→ℂ) (outside : List ℕ)
    (hd : ∀q∈outside,(q:ℤ)∣N) {l : ℕ} (h k : SignedHistory l) (hc : Congruent N h k) :
    spectatorProduct g outside h=spectatorProduct g outside k := by
  induction h with
  | leaf a =>
    cases k with
    | leaf b => exact spectatorFactor_eq_of_congruent g outside hd a b hc
  | node a p u hp hm left right il ir =>
    cases k with
    | node b q v kp km left' right' =>
      change spectatorProduct g outside left*conj (spectatorProduct g outside right)=
        spectatorProduct g outside left'*conj (spectatorProduct g outside right')
      rw [il left' hc.2.2.2.2.2.1,ir right' hc.2.2.2.2.2.2]

theorem pairSpectator_eq_of_congruent {N : ℤ} (g : (q:ℕ)→ZMod q→ℂ) (outside : List ℕ)
    (hd : ∀q∈outside,(q:ℤ)∣N) {l : ℕ} (h k h' k' : SignedHistory l)
    (hh : Congruent N h h') (hk : Congruent N k k') :
    pairSpectator g outside h k=pairSpectator g outside h' k' := by
  rw [pairSpectator,pairSpectator,spectatorProduct_eq_of_congruent g outside hd h h' hh,
    spectatorProduct_eq_of_congruent g outside hd k k' hk]

theorem pair_rebuild_eq_of_modEq {l : ℕ} (h k : History l)
    (g : (q:ℕ)→ZMod q→ℂ) (outside : List ℕ) (R N Xp Xm Yp Ym : ℤ)
    (hd : ∀q∈outside,(q:ℤ)∣N) (hh : DivisorData R h) (hk : DivisorData R k)
    (hp : Xp≡Yp [ZMOD R^l*N]) (hm : Xm≡Ym [ZMOD R^l*N]) :
    pairSpectator g outside (rebuild h Xp Xm) (rebuild k Xp Xm)=
      pairSpectator g outside (rebuild h Yp Ym) (rebuild k Yp Ym) :=
  pairSpectator_eq_of_congruent g outside hd _ _ _ _
    (rebuild_congruent h R N Xp Xm Yp Ym hh hp hm)
    (rebuild_congruent k R N Xp Xm Yp Ym hk hp hm)

end Ostmann.Arithmetic.HistorySignedSpectator

end

end OAI

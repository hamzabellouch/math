import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedDecodeBasic
import OAI.NumberTheory.Ostmann.Construction.BaseFactors

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Arithmetic.HistorySignedSpectator
open Construction HistorySignedDecode

def stateProduct (a : SignedState) : ℤ :=
  a.giantPlus*a.giantMinus*((a.small.map SmallSlot.value).prod:ℤ)

def argument (outside : List ℕ) (q : ℕ) (a : SignedState) : ZMod q :=
  (a.frequency:ZMod q)*((((outsideProduct outside/q:ℕ):ℤ)*stateProduct a:ℤ):ZMod q)⁻¹

def spectatorFactor (g : (q:ℕ)→ZMod q→ℂ) (outside : List ℕ) (a : SignedState) : ℂ :=
  (outside.map (fun q=>g q (argument outside q a))).prod

def leafProduct (f : SignedState→ℂ) : {l : ℕ}→SignedHistory l→ℂ
  | _,.leaf a => f a
  | _,.node _ _ _ _ _ left right => leafProduct f left*conj (leafProduct f right)

def spectatorProduct (g : (q:ℕ)→ZMod q→ℂ) (outside : List ℕ)
    {l : ℕ} (h : SignedHistory l) : ℂ := leafProduct (spectatorFactor g outside) h

def pairSpectator (g : (q:ℕ)→ZMod q→ℂ) (outside : List ℕ)
    {l : ℕ} (h k : SignedHistory l) : ℂ :=
  spectatorProduct g outside h*conj (spectatorProduct g outside k)

theorem stateProduct_eq_projection (a : SignedState) (ha : a.Nonnegative) :
    stateProduct a=(a.toState.product:ℤ) := by
  simp only [stateProduct,State.product,State.values,SignedState.toState,List.prod_cons,
    Nat.cast_mul,Int.toNat_of_nonneg ha.1,Int.toNat_of_nonneg ha.2]
  ring

theorem argument_eq_projection (outside : List ℕ) (q : ℕ) (a : SignedState) (ha : a.Nonnegative) :
    argument outside q a=modFraction q a.toState.frequency
      ((outsideProduct outside/q)*a.toState.product) := by
  rw [argument,stateProduct_eq_projection a ha]
  simp only [modFraction,SignedState.toState,Int.cast_mul,Int.cast_natCast,Nat.cast_mul]

theorem spectatorFactor_eq_projection (g : (q:ℕ)→ZMod q→ℂ) (outside : List ℕ)
    (a : SignedState) (ha : a.Nonnegative) :
    spectatorFactor g outside a=Construction.spectatorFactor g outside a.toState := by
  unfold spectatorFactor Construction.spectatorFactor
  congr 1
  apply List.map_congr_left
  intro q _
  rw [argument_eq_projection outside q a ha]

theorem spectatorProduct_eq_projection (g : (q:ℕ)→ZMod q→ℂ) (outside : List ℕ)
    {l : ℕ} (h : SignedHistory l) (hn : h.Nonnegative) :
    spectatorProduct g outside h=h.toHistory.leafProduct (Construction.spectatorFactor g outside) := by
  induction h with
  | leaf a => exact spectatorFactor_eq_projection g outside a hn
  | node a p u hp hm left right il ir =>
    change spectatorProduct g outside left*conj (spectatorProduct g outside right)=_
    rw [il hn.2.2.1,ir hn.2.2.2]
    rfl

theorem pairSpectator_eq_projection (g : (q:ℕ)→ZMod q→ℂ) (outside : List ℕ)
    {l : ℕ} (h k : SignedHistory l) (hh : h.Nonnegative) (hk : k.Nonnegative) :
    pairSpectator g outside h k=
      h.toHistory.leafProduct (Construction.spectatorFactor g outside)*
        conj (k.toHistory.leafProduct (Construction.spectatorFactor g outside)) := by
  rw [pairSpectator,spectatorProduct_eq_projection g outside h hh,
    spectatorProduct_eq_projection g outside k hk]

end Ostmann.Arithmetic.HistorySignedSpectator

end

end OAI

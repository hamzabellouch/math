import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorCRTResidue
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySpectatorEvaluation

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Arithmetic.HistorySignedSpectatorDiagram
open Construction HistorySignedSpectatorCRT

def primeArgument (q : ℕ) (D : ZMod q) (a : State) (Xp Xm : ZMod q) : ZMod q :=
  (a.frequency:ZMod q)*(D*(Xp*Xm*((a.small.map SmallSlot.value).prod:ZMod q)))⁻¹

def primeSpectator (q : ℕ) (g : ZMod q→ℂ) (D : ZMod q) :
    {l : ℕ}→History l→ZMod q→ZMod q→ℂ
  | _,.leaf a,Xp,Xm => g (primeArgument q D a Xp Xm)
  | _,.node a _ u hp hm left right,Xp,Xm =>
    let p := residuePivot q a left.root.frequency right.root.frequency u hp hm Xp Xm
    primeSpectator q g D left p Xp*conj (primeSpectator q g D right p Xm)

theorem primeSpectator_zero_of_giant (q : ℕ) [Fact q.Prime]
    (g : ZMod q→ℂ) (hg : g 0=0) (D : ZMod q) {l : ℕ} (h : History l)
    (Xp Xm : ZMod q) (hz : Xp=0 ∨ Xm=0) : primeSpectator q g D h Xp Xm=0 := by
  induction h generalizing Xp Xm with
  | leaf a => rcases hz with rfl | rfl <;> simp [primeSpectator,primeArgument,hg]
  | node a p u hp hm left right il ir =>
    rcases hz with rfl | rfl
    · simp only [primeSpectator]
      rw [il _ 0 (Or.inr rfl),zero_mul]
    · simp only [primeSpectator]
      rw [ir _ 0 (Or.inr rfl),map_zero,mul_zero]

end Ostmann.Arithmetic.HistorySignedSpectatorDiagram

end

end OAI

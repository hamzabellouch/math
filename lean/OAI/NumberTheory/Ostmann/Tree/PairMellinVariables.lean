import OAI.NumberTheory.Ostmann.Tree.DiagonalMellin
import OAI.NumberTheory.Ostmann.Tree.DifferenceConvolution

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

inductive PairMode
  | friendly
  | bad
  deriving DecidableEq

def PairMode.multiplier : PairMode → ZMod p → ZMod p → ZMod p
  | .friendly,d,_ => d
  | .bad,_,e => e⁻¹

def PairMode.unitMultiplier : PairMode → (ZMod p)ˣ → (ZMod p)ˣ → (ZMod p)ˣ
  | .friendly,d,_ => d
  | .bad,_,e => e⁻¹

theorem PairMode.coe_unitMultiplier (m : PairMode) (d e : (ZMod p)ˣ) :
    ((m.unitMultiplier d e:(ZMod p)ˣ):ZMod p)=m.multiplier d e := by
  cases m with
  | friendly => rfl
  | bad => exact Units.val_inv_eq_inv_val e

def leftPairTwist (L R : PairMode) (ν χ ψ : MulChar (ZMod p) ℂ) : MulChar (ZMod p) ℂ :=
  ν*(match L with | .friendly => χ | .bad => 1)*(match R with | .friendly => 1 | .bad => ψ⁻¹)

def rightPairTwist (L R : PairMode) (ν χ ψ : MulChar (ZMod p) ℂ) : MulChar (ZMod p) ℂ :=
  ν⁻¹*(match R with | .friendly => ψ | .bad => 1)*(match L with | .friendly => 1 | .bad => χ⁻¹)

theorem pairTest_mellin_mul (g : ZMod p → ℂ) (σ k : (ZMod p)ˣ)
    (χ : MulChar (ZMod p) ℂ) (d : ZMod p) (hd : d≠0) (hg0 : g 0=0) :
    mellin (fun lam : (ZMod p)ˣ => pairTest g σ d ((lam:ZMod p)*k)) χ =
      χ k*pairSpectrum g χ ((σ:ZMod p)*d) := by
  let D : (ZMod p)ˣ := Units.mk0 d hd
  have he : (fun lam : (ZMod p)ˣ => pairTest g σ d ((lam:ZMod p)*k)) =
      fun lam : (ZMod p)ˣ => bottomPair g (σ*D) (lam*k) := by
    funext lam
    dsimp [pairTest,bottomPair,pairMobiusValue,pairFirst,pairSecond,D]
  rw [he]
  have hm := mellin_mulRight (fun t : (ZMod p)ˣ => bottomPair g (σ*D) t) k χ
  simp only [Units.val_mul] at hm
  rw [hm,← pairSpectrum_unit g χ (σ*D) hg0]
  rfl

theorem doubleMellin_product (f h : (ZMod p)ˣ → ℂ) (c : ℂ)
    (χ ψ : MulChar (ZMod p) ℂ) :
    doubleMellin (fun lam mu => (f lam*h mu)*c) χ ψ=mellin f χ*mellin h ψ*c := by
  have hi (mu : (ZMod p)ˣ) :
      mellin (fun lam => (f lam*h mu)*c) χ=(h mu*c)*mellin f χ := by
    have he : (fun lam => (f lam*h mu)*c)=fun lam => (h mu*c)*f lam := by funext lam; ring
    rw [he,mellin_const_mul]
  unfold doubleMellin
  simp_rw [hi]
  have he : (fun mu => (h mu*c)*mellin f χ)=fun mu => (mellin f χ*c)*h mu := by funext mu; ring
  rw [he,mellin_const_mul]
  ring

def twoPairValue (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (L R : PairMode) (ν : MulChar (ZMod p) ℂ)
    (d e : ZMod p) (lam mu : (ZMod p)ˣ) : ℂ :=
  (pairTest g σ d ((lam:ZMod p)*L.multiplier d e)*
    pairTest h τ e ((mu:ZMod p)*R.multiplier e d))*(ν d*ν⁻¹ e)

end
end Ostmann.FiniteField

end OAI

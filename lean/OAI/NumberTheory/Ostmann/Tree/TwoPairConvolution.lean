import OAI.NumberTheory.Ostmann.Tree.DoubleMellinEnergy
import OAI.NumberTheory.Ostmann.Tree.TwoPairMellin

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

def twoPairConvolution (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (L R : PairMode) (ν : MulChar (ZMod p) ℂ)
    (lam mu : (ZMod p)ˣ) (y : ZMod p) : ℂ :=
  mean (fun d => twoPairValue g h σ τ L R ν d (d-y) lam mu)

theorem twoPairConvolution_doubleMellin (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (L R : PairMode) (ν χ ψ : MulChar (ZMod p) ℂ) (y : ZMod p)
    (hg0 : g 0=0) (hh0 : h 0=0) :
    doubleMellin (fun lam mu => twoPairConvolution g h σ τ L R ν lam mu y) χ ψ =
      differenceConvolution
        (fun d => pairSpectrum g χ ((σ:ZMod p)*d)*(leftPairTwist L R ν χ ψ) d)
        (fun e => pairSpectrum h ψ ((τ:ZMod p)*e)*(rightPairTwist L R ν χ ψ) e) y := by
  unfold twoPairConvolution
  rw [doubleMellin_mean]
  simp_rw [twoPairValue_doubleMellin g h σ τ L R ν χ ψ _ _ hg0 hh0]
  rfl

theorem twoPairConvolution_energy (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (L R : PairMode) (ν : MulChar (ZMod p) ℂ) (hg0 : g 0=0) (hh0 : h 0=0) :
    (Fintype.card (ZMod p)ˣ:ℝ)⁻¹^2*
      (∑ lam : (ZMod p)ˣ,∑ mu : (ZMod p)ˣ,l2Sq (twoPairConvolution g h σ τ L R ν lam mu)) =
      ∑ χ : MulChar (ZMod p) ℂ,∑ ψ : MulChar (ZMod p) ℂ,∑ a : ZMod p,
        ‖twistedPairFourier g σ χ (leftPairTwist L R ν χ ψ) a‖^2 *
        ‖twistedPairFourier h τ ψ (rightPairTwist L R ν χ ψ) (-a)‖^2 := by
  rw [doubleMellin_mean_energy]
  apply Finset.sum_congr rfl
  intro χ _
  apply Finset.sum_congr rfl
  intro ψ _
  simp_rw [twoPairConvolution_doubleMellin g h σ τ L R ν χ ψ _ hg0 hh0]
  exact differenceConvolution_parseval _ _

end
end Ostmann.FiniteField

end OAI

import OAI.NumberTheory.Ostmann.Tree.AffinePairIdentity
import OAI.NumberTheory.Ostmann.Tree.MellinTransform
import OAI.NumberTheory.Ostmann.Tree.PairSpectrum

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

theorem diagonalPair_mellin_inner (g : ZMod p → ℂ) (χ η : MulChar (ZMod p) ℂ)
    (a : ZMod p) (σ : (ZMod p)ˣ) (d : ZMod p) (hg0 : g 0=0) :
    mellin (fun lam : (ZMod p)ˣ => diagonalPairValue g η a σ lam d) χ =
      pairSpectrum g χ ((σ:ZMod p)*d)*χ d*η d*ZMod.stdAddChar (-(a*d)) := by
  by_cases hd : d=0
  · subst d
    simp [diagonalPairValue,η.map_zero,χ.map_zero,mellin]
  let D : (ZMod p)ˣ := Units.mk0 d hd
  have he : (fun lam : (ZMod p)ˣ => diagonalPairValue g η a σ lam d) =
      (fun lam : (ZMod p)ˣ => (η d*ZMod.stdAddChar (-(a*d)))*bottomPair g (σ*D) (lam*D)) := by
    funext lam
    dsimp [diagonalPairValue,pairTest,bottomPair,pairMobiusValue,pairFirst,pairSecond,D]
    ring
  have hm := mellin_mulRight (fun t : (ZMod p)ˣ => bottomPair g (σ*D) t) D χ
  simp only [Units.val_mul] at hm
  rw [he,mellin_const_mul,hm,← pairSpectrum_unit g χ (σ*D) hg0]
  change (η d*ZMod.stdAddChar (-(a*d)))*(χ d*pairSpectrum g χ ((σ:ZMod p)*d)) = _
  ring

theorem diagonalPair_mellin (g : ZMod p → ℂ) (χ η : MulChar (ZMod p) ℂ)
    (a : ZMod p) (σ : (ZMod p)ˣ) (hg0 : g 0=0) :
    mellin (fun lam : (ZMod p)ˣ => mean (diagonalPairValue g η a σ lam)) χ =
      fourier (fun d => pairSpectrum g χ ((σ:ZMod p)*d)*χ d*η d) a := by
  unfold mean
  rw [mellin_const_mul,mellin_sum,fourier_apply]
  simp_rw [diagonalPair_mellin_inner g χ η a σ _ hg0]

end
end Ostmann.FiniteField

end OAI

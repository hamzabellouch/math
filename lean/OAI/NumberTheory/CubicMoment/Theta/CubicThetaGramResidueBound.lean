import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramKloosterman
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveNormalizedResidue

namespace OAI

/-! The finite Kloosterman Gram formula controls the actual arithmetic
residue observations by the Hilbert-space Cauchy--Schwarz inequality. -/
noncomputable section
open scoped CompactlySupported ContDiff
namespace CubicFirstMoment

lemma cubicThetaPositiveMass_gram (h k : Eisenstein) (W V : C_c(ℝ,ℂ))
    (hsmW : ContDiff ℝ ∞ (W : ℝ → ℂ)) (hsmV : ContDiff ℝ ∞ (V : ℝ → ℂ))
    {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ) (hW : ∀ v≤ε,W v=0) (hV : ∀ v≤δ,V v=0) :
    inner ℂ (cubicThetaPositiveFourierMass h W hε hW hsmW)
      (cubicThetaPositiveFourierMass k V hδ hV hsmV)=
      cubicThetaKloostermanGram h k W V ε δ :=
  cubicThetaPositiveGram_kloosterman h k W V hsmV hε hδ hW hV

lemma cubicThetaKloostermanGram_self (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) {ε : ℝ} (hε : 0<ε)
    (hW : ∀ v≤ε,W v=0) :
    cubicThetaKloostermanGram h h W W ε ε=
      ((‖cubicThetaPositiveFourierMass h W hε hW hsm‖^2:ℝ):ℂ) := by
  rw [←cubicThetaPositiveGram_kloosterman h h W W hsm hε hε hW hW]
  change inner ℂ (cubicThetaPositiveFourierMass h W hε hW hsm)
    (cubicThetaPositiveFourierMass h W hε hW hsm)=_
  rw [inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (E:=cubicThetaAutomorphicL2)]
  push_cast
  rfl

lemma cubicThetaKloostermanGram_self_nonneg (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) {ε : ℝ} (hε : 0<ε)
    (hW : ∀ v≤ε,W v=0) :
    0≤(cubicThetaKloostermanGram h h W W ε ε).re := by
  rw [cubicThetaKloostermanGram_self h W hsm hε hW,Complex.ofReal_re]
  exact sq_nonneg _

theorem cubicThetaFourierResidue_gram_bound {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) {ε : ℝ}
    (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    ‖((Real.pi:ℂ)/Complex.Gamma (4/3))*cubicThetaArithmeticFourierResidue h (4/3)*
        cubicThetaPositiveRadialTest h W ε (4/3)‖^2≤
      (cubicThetaKloostermanGram h h W W ε ε).re*‖cubicThetaArithmeticResidueL2‖^2 := by
  rw [←cubicThetaPositiveFourierMass_residue hh W hε hW hsm,
    cubicThetaKloostermanGram_self h W hsm hε hW,Complex.ofReal_re]
  have hn := norm_inner_le_norm (𝕜:=ℂ)
    (cubicThetaPositiveFourierMass h W hε hW hsm) cubicThetaArithmeticResidueL2
  simpa only [mul_pow] using pow_le_pow_left₀ (_root_.norm_nonneg _) hn 2

end CubicFirstMoment

end

end OAI

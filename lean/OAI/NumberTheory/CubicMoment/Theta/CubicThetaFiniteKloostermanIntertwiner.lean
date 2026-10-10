import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKloostermanInvolution

namespace OAI

/-! The finite Fourier-conjugated Kloosterman operator. It is Hermitian
and squares to the actual primary Fourier projection. Its entries are
the normalized signed Kloosterman kernel from the Gram expansion. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaFiniteFourierAdjoint_neg (q : Eisenstein) (hq : q≠0)
    [Fintype (Residues q)] (f : Residues q → ℂ) (x : Residues q) :
    cubicThetaFiniteFourierAdjoint q hq f x=cubicThetaFiniteFourier q hq f (-x) := by
  unfold cubicThetaFiniteFourierAdjoint cubicThetaFiniteFourier
  apply Finset.sum_congr rfl
  intro a _
  rw [cubicThetaResidueFourier_star]
  congr 2
  ring

def cubicThetaFiniteKloostermanIntertwiner (c : Eisenstein) (hc0 : c≠0)
    [Fintype (Residues (3*c))] (f : Residues (3*c) → ℂ) (x : Residues (3*c)) : ℂ :=
  (Fintype.card (Residues (3*c)):ℂ)⁻¹*
    cubicThetaFiniteFourierAdjoint (3*c) (mul_ne_zero (by norm_num) hc0)
      (cubicThetaWeightedResidueInversion c
        (cubicThetaFiniteFourier (3*c) (mul_ne_zero (by norm_num) hc0) f)) x

theorem cubicThetaFiniteKloostermanIntertwiner_kernel (c : Eisenstein) (hc0 : c≠0)
    [Fintype (Residues (3*c))] (f : Residues (3*c) → ℂ) (x : Residues (3*c)) :
    cubicThetaFiniteKloostermanIntertwiner c hc0 f x=
      (Fintype.card (Residues (3*c)):ℂ)⁻¹*cubicThetaFiniteKloostermanApply c hc0 f (-x) := by
  rw [cubicThetaFiniteKloostermanApply_factor]
  exact congrArg ((Fintype.card (Residues (3*c)):ℂ)⁻¹*·)
    (cubicThetaFiniteFourierAdjoint_neg (3*c) (mul_ne_zero (by norm_num) hc0) _ x)

theorem cubicThetaFiniteKloostermanIntertwiner_fourier (c : Eisenstein) (hc0 : c≠0)
    [Fintype (Residues (3*c))] (f : Residues (3*c) → ℂ) (x : Residues (3*c)) :
    cubicThetaFiniteFourier (3*c) (mul_ne_zero (by norm_num) hc0)
      (cubicThetaFiniteKloostermanIntertwiner c hc0 f) x=
      cubicThetaWeightedResidueInversion c
        (cubicThetaFiniteFourier (3*c) (mul_ne_zero (by norm_num) hc0) f) x := by
  have hn : (Fintype.card (Residues (3*c)):ℂ)≠0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Residues (3*c)))).ne'
  unfold cubicThetaFiniteKloostermanIntertwiner
  rw [cubicThetaFiniteFourier_const_mul,cubicThetaFiniteFourier_inverse_adjoint,
    ←mul_assoc,inv_mul_cancel₀ hn,one_mul]

theorem cubicThetaFiniteKloostermanIntertwiner_square {c : Eisenstein}
    (hc : (3:Eisenstein)∣c) (hc0 : c≠0) [Fintype (Residues (3*c))]
    (f : Residues (3*c) → ℂ) :
    cubicThetaFiniteKloostermanIntertwiner c hc0 (cubicThetaFiniteKloostermanIntertwiner c hc0 f)=
      cubicThetaFinitePrimaryProjection c hc0 f := by
  apply cubicThetaFiniteFourier_injective (3*c) (mul_ne_zero (by norm_num) hc0)
  funext x
  rw [cubicThetaFiniteKloostermanIntertwiner_fourier,cubicThetaFinitePrimaryProjection_fourier]
  have he : cubicThetaFiniteFourier (3*c) (mul_ne_zero (by norm_num) hc0)
      (cubicThetaFiniteKloostermanIntertwiner c hc0 f)=
      cubicThetaWeightedResidueInversion c
        (cubicThetaFiniteFourier (3*c) (mul_ne_zero (by norm_num) hc0) f) :=
    funext (cubicThetaFiniteKloostermanIntertwiner_fourier c hc0 f)
  rw [he,cubicThetaWeightedResidueInversion_square hc]

theorem cubicThetaFiniteKloostermanIntertwiner_symmetric {c : Eisenstein}
    (hc : (3:Eisenstein)∣c) (hc0 : c≠0) [Fintype (Residues (3*c))]
    (f g : Residues (3*c) → ℂ) :
    (∑ x : Residues (3*c),cubicThetaFiniteKloostermanIntertwiner c hc0 f x*star (g x))=
      ∑ x : Residues (3*c),f x*star (cubicThetaFiniteKloostermanIntertwiner c hc0 g x) := by
  have hn : (Fintype.card (Residues (3*c)):ℂ)≠0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Residues (3*c)))).ne'
  apply mul_left_cancel₀ hn
  rw [←cubicThetaFiniteFourier_parseval (3*c) (mul_ne_zero (by norm_num) hc0)
      (cubicThetaFiniteKloostermanIntertwiner c hc0 f) g,
    ←cubicThetaFiniteFourier_parseval (3*c) (mul_ne_zero (by norm_num) hc0)
      f (cubicThetaFiniteKloostermanIntertwiner c hc0 g)]
  simp_rw [cubicThetaFiniteKloostermanIntertwiner_fourier]
  exact cubicThetaWeightedResidueInversion_symmetric hc _ _

end CubicFirstMoment

end

end OAI

import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootL2Algebra
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteFourierParseval

namespace OAI

/-! Actual finite Fourier averages at the cube modulus, on sections
and on their completed domain space. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaPrimeCubeRootFiniteFourier {p : Eisenstein} (hp : primaryPrime p)
    (k : Residues (p^3)) : cubicThetaPrimeCubeRootFiniteSections hp →ₗ[ℂ]
      cubicThetaPrimeCubeRootFiniteSections hp := by
  let : Finite (Residues (p^3)) := finite_residues (pow_ne_zero 3 hp.2.ne_zero)
  let : Fintype (Residues (p^3)) := Fintype.ofFinite _
  exact (norm (p^3):ℂ)⁻¹ • ∑ r : Residues (p^3),
    star (residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero) (k*r)) •
      cubicThetaPrimeCubeRootFiniteTranslate hp (residueRepresentative (p^3) r)

lemma cubicThetaPrimeCubeRootFiniteFourier_apply {p : Eisenstein} (hp : primaryPrime p)
    [Fintype (Residues (p^3))] (k : Residues (p^3)) (F : cubicThetaPrimeCubeRootFiniteSections hp) :
    cubicThetaPrimeCubeRootFiniteFourier hp k F=(norm (p^3):ℂ)⁻¹ • ∑ r : Residues (p^3),
      star (residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero) (k*r)) •
        cubicThetaPrimeCubeRootFiniteTranslate hp (residueRepresentative (p^3) r) F := by
  classical
  simp only [cubicThetaPrimeCubeRootFiniteFourier,LinearMap.smul_apply,LinearMap.sum_apply]
  congr 1
  apply Finset.sum_congr
  · ext r
    simp
  · intro r _
    rfl

def cubicThetaPrimeCubeRootFourierL2 {p : Eisenstein} (hp : primaryPrime p)
    (k : Residues (p^3)) : cubicThetaPrimeCubeRootAutomorphicL2 hp →L[ℂ]
      cubicThetaPrimeCubeRootAutomorphicL2 hp := by
  let : Finite (Residues (p^3)) := finite_residues (pow_ne_zero 3 hp.2.ne_zero)
  let : Fintype (Residues (p^3)) := Fintype.ofFinite _
  exact (norm (p^3):ℂ)⁻¹ • ∑ r : Residues (p^3),
    star (residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero) (k*r)) •
      (cubicThetaPrimeCubeRootResidueL2 hp r).toContinuousLinearMap

lemma cubicThetaPrimeCubeRootFourierL2_apply {p : Eisenstein} (hp : primaryPrime p)
    [Fintype (Residues (p^3))] (k : Residues (p^3))
    (u : cubicThetaPrimeCubeRootAutomorphicL2 hp) :
    cubicThetaPrimeCubeRootFourierL2 hp k u=(norm (p^3):ℂ)⁻¹ • ∑ r : Residues (p^3),
      star (residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero) (k*r)) •
        cubicThetaPrimeCubeRootResidueL2 hp r u := by
  classical
  simp only [cubicThetaPrimeCubeRootFourierL2,smul_apply,sum_apply,
    LinearIsometry.coe_toContinuousLinearMap]
  congr 1
  apply Finset.sum_congr
  · ext r
    simp
  · intro r _
    rfl

lemma cubicThetaPrimeCubeRootFourierL2_finite {p : Eisenstein} (hp : primaryPrime p)
    (k : Residues (p^3)) (F : cubicThetaPrimeCubeRootFiniteSections hp) :
    cubicThetaPrimeCubeRootFourierL2 hp k (cubicThetaPrimeCubeRootFiniteEmbedding hp F)=
      cubicThetaPrimeCubeRootFiniteEmbedding hp (cubicThetaPrimeCubeRootFiniteFourier hp k F) := by
  let : Finite (Residues (p^3)) := finite_residues (pow_ne_zero 3 hp.2.ne_zero)
  let : Fintype (Residues (p^3)) := Fintype.ofFinite _
  rw [cubicThetaPrimeCubeRootFourierL2_apply,cubicThetaPrimeCubeRootFiniteFourier_apply,
    map_smul,map_sum]
  simp only [map_smul,cubicThetaPrimeCubeRootResidueL2,cubicThetaPrimeCubeRootTranslateL2_finite]

theorem cubicThetaPrimeCubeRootFourierL2_norm_le {p : Eisenstein} (hp : primaryPrime p)
    (k : Residues (p^3)) (u : cubicThetaPrimeCubeRootAutomorphicL2 hp) :
    ‖cubicThetaPrimeCubeRootFourierL2 hp k u‖≤‖u‖ := by
  let : Finite (Residues (p^3)) := finite_residues (pow_ne_zero 3 hp.2.ne_zero)
  let : Fintype (Residues (p^3)) := Fintype.ofFinite _
  have hcard : (Fintype.card (Residues (p^3)):ℝ)=norm (p^3) := by
    rw [←Nat.card_eq_fintype_card,residues_card (pow_ne_zero 3 hp.2.ne_zero)]
    exact normNat_cast (p^3)
  rw [cubicThetaPrimeCubeRootFourierL2_apply,norm_smul,norm_inv,
    Complex.norm_of_nonneg (norm_nonneg (p^3))]
  calc
    _ ≤ (norm (p^3))⁻¹*∑ r : Residues (p^3),
        ‖star (residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero) (k*r)) •
          cubicThetaPrimeCubeRootResidueL2 hp r u‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (norm_nonneg (p^3)))
    _ = ‖u‖ := by
      simp only [norm_smul,norm_star,cubicThetaResidueFourier_norm,
        LinearIsometry.norm_map,one_mul,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hcard]
      rw [inv_mul_cancel_left₀ (norm_pos_of_ne_zero (pow_ne_zero 3 hp.2.ne_zero)).ne']

end CubicFirstMoment

end

end OAI

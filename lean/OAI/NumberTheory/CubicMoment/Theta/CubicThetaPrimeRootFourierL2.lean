import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootL2Algebra
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootFourierResolution

namespace OAI

/-! Actual finite Fourier projections on the completed root-cover space,
with their exact agreement on square-integrable sections. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaPrimeRootFiniteFourier {p : Eisenstein} (hp : primaryPrime p)
    (k : Residues p) : cubicThetaPrimeRootFiniteSections hp →ₗ[ℂ]
      cubicThetaPrimeRootFiniteSections hp := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  exact (norm p:ℂ)⁻¹ • ∑ r : Residues p,
    star (residueFourierChar p hp.2.ne_zero (k*r)) • cubicThetaPrimeRootFiniteResidue hp r

lemma cubicThetaPrimeRootFiniteFourier_apply {p : Eisenstein} (hp : primaryPrime p)
    [Fintype (Residues p)] (k : Residues p) (F : cubicThetaPrimeRootFiniteSections hp) :
    cubicThetaPrimeRootFiniteFourier hp k F=(norm p:ℂ)⁻¹ • ∑ r : Residues p,
      star (residueFourierChar p hp.2.ne_zero (k*r)) • cubicThetaPrimeRootFiniteResidue hp r F := by
  classical
  simp only [cubicThetaPrimeRootFiniteFourier,LinearMap.smul_apply,LinearMap.sum_apply]
  congr 1
  apply Finset.sum_congr
  · ext r
    simp
  · intro r _
    rfl

lemma cubicThetaPrimeRootFiniteFourier_val {p : Eisenstein} (hp : primaryPrime p)
    (k : Residues p) (F : cubicThetaPrimeRootFiniteSections hp) :
    (cubicThetaPrimeRootFiniteFourier hp k F).val=
      cubicThetaPrimeRootFourierProjection hp k F.val := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  change (cubicThetaPrimeRootFiniteSections hp).subtype (cubicThetaPrimeRootFiniteFourier hp k F)=_
  rw [cubicThetaPrimeRootFiniteFourier_apply,map_smul,map_sum,
    cubicThetaPrimeRootFourierProjection_apply]
  simp only [map_smul]
  rfl

def cubicThetaPrimeRootFourierL2 {p : Eisenstein} (hp : primaryPrime p)
    (k : Residues p) : cubicThetaPrimeRootAutomorphicL2 hp →L[ℂ]
      cubicThetaPrimeRootAutomorphicL2 hp := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  exact (norm p:ℂ)⁻¹ • ∑ r : Residues p,
    star (residueFourierChar p hp.2.ne_zero (k*r)) •
      (cubicThetaPrimeRootResidueL2 hp r).toContinuousLinearMap

lemma cubicThetaPrimeRootFourierL2_apply {p : Eisenstein} (hp : primaryPrime p)
    [Fintype (Residues p)] (k : Residues p) (u : cubicThetaPrimeRootAutomorphicL2 hp) :
    cubicThetaPrimeRootFourierL2 hp k u=(norm p:ℂ)⁻¹ • ∑ r : Residues p,
      star (residueFourierChar p hp.2.ne_zero (k*r)) • cubicThetaPrimeRootResidueL2 hp r u := by
  classical
  simp only [cubicThetaPrimeRootFourierL2,smul_apply,
    sum_apply,LinearIsometry.coe_toContinuousLinearMap]
  congr 1
  apply Finset.sum_congr
  · ext r
    simp
  · intro r _
    rfl

lemma cubicThetaPrimeRootFourierL2_finite {p : Eisenstein} (hp : primaryPrime p)
    (k : Residues p) (F : cubicThetaPrimeRootFiniteSections hp) :
    cubicThetaPrimeRootFourierL2 hp k (cubicThetaPrimeRootFiniteEmbedding hp F)=
      cubicThetaPrimeRootFiniteEmbedding hp (cubicThetaPrimeRootFiniteFourier hp k F) := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  rw [cubicThetaPrimeRootFourierL2_apply,cubicThetaPrimeRootFiniteFourier_apply,map_smul,map_sum]
  simp only [map_smul,cubicThetaPrimeRootResidueL2_finite]

theorem cubicThetaPrimeRootFourierL2_idempotent {p : Eisenstein} (hp : primaryPrime p)
    (k : Residues p) (u : cubicThetaPrimeRootAutomorphicL2 hp) :
    cubicThetaPrimeRootFourierL2 hp k (cubicThetaPrimeRootFourierL2 hp k u)=
      cubicThetaPrimeRootFourierL2 hp k u := by
  refine (cubicThetaPrimeRootFiniteEmbedding_dense hp).induction_on u
    (isClosed_eq ((cubicThetaPrimeRootFourierL2 hp k).continuous.comp
      (cubicThetaPrimeRootFourierL2 hp k).continuous) (cubicThetaPrimeRootFourierL2 hp k).continuous) ?_
  intro F
  rw [cubicThetaPrimeRootFourierL2_finite,cubicThetaPrimeRootFourierL2_finite]
  apply congrArg (cubicThetaPrimeRootFiniteEmbedding hp)
  apply Subtype.ext
  rw [cubicThetaPrimeRootFiniteFourier_val,cubicThetaPrimeRootFiniteFourier_val,
    cubicThetaPrimeRootFourierProjection_idempotent]

end CubicFirstMoment

end

end OAI

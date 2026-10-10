import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootTraceNormalized
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaResidueSourceOrbit

namespace OAI

/-! The once-cubic overlap of the actual arithmetic residue follows
from the proved Hecke eigenvalue and exact trace normalization. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootHecke_ratio {p : Eisenstein} (hp : primaryPrime p) :
    ((cubicThetaPrimeIwahori (p^3)).index:ℂ)⁻¹*((norm p:ℂ)^2+norm p)=(norm p:ℂ)⁻¹ := by
  have hN : (normNat p:ℂ)=(norm p:ℂ) := by
    simpa only [Complex.ofReal_natCast] using congrArg Complex.ofReal (normNat_cast p)
  rw [cubicThetaPrimeCubeIwahori_index hp,Nat.cast_add,Nat.cast_pow,Nat.cast_pow,hN]
  have hq : (norm p:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero hp.2.ne_zero).ne'
  have hq1 : (norm p:ℂ)+1≠0 := by
    have h : (norm p+1:ℝ)≠0 := (add_pos_of_nonneg_of_pos (norm_nonneg p) zero_lt_one).ne'
    simpa only [Complex.ofReal_add,Complex.ofReal_one] using Complex.ofReal_ne_zero.mpr h
  have hd : (norm p:ℂ)^3+(norm p:ℂ)^2≠0 := by
    rw [show (norm p:ℂ)^3+(norm p:ℂ)^2=(norm p:ℂ)^2*((norm p:ℂ)+1) by ring]
    exact mul_ne_zero (pow_ne_zero 2 hq) hq1
  field_simp [hd,hq]

theorem cubicThetaPrimeCubeRootResidue_overlap {p : Eisenstein} (hp : primaryPrime p) :
    inner ℂ (cubicThetaPrimeCubeRootLiftL2 hp cubicThetaArithmeticResidueL2)
      (cubicThetaPrimeCubeRootDilationL2 hp cubicThetaArithmeticResidueL2)=
      (norm p:ℂ)⁻¹*(‖cubicThetaArithmeticResidueL2‖^2:ℂ) := by
  rw [cubicThetaPrimeCubeRootTrace_normalized,cubicThetaArithmeticResidueL2_hecke,
    inner_smul_right (𝕜:=ℂ) (E:=cubicThetaAutomorphicL2),←mul_assoc,
    cubicThetaPrimeCubeRootHecke_ratio hp]
  exact congrArg (fun z : ℂ => (norm p:ℂ)⁻¹*z)
    (inner_self_eq_norm_sq_to_K (𝕜:=ℂ) cubicThetaArithmeticResidueL2)

end CubicFirstMoment

end

end OAI

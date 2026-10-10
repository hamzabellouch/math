import OAI.NumberTheory.DirichletL.Foundation
import OAI.NumberTheory.DirichletL.Hecke.Family
import OAI.NumberTheory.DirichletL.Detector.Completed

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbeRow
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve InitialMeanSquare ProbeCompleted

local notation "O" => ActualEisensteinCubic.O

def targetMonoid (η : HeckeFamily.Character) : O →* ℂ where
  toFun := HeckeFamily.elementCoeff η
  map_one' := HeckeFamily.elementCoeff_one η
  map_mul' := HeckeFamily.elementCoeff_mul η

theorem targetMonoid_norm_le_one (η : HeckeFamily.Character) (a : O) :
    ‖targetMonoid η a‖ ≤ 1 := by
  let : Finite (O ⧸ η.modulus) := Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Fintype (O ⧸ η.modulus) := Fintype.ofFinite _
  exact FiniteRayExpansion.norm_char_le_one η.residue (Ideal.Quotient.mk η.modulus a)

def rowCoefficient (η : HeckeFamily.Character) (Xi : O →* ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) (m : O) : O →* ℂ :=
  targetMonoid η * conjugateMonoid Xi * reciprocityPhaseMonoid s hs *
    (idealRowHom m).toMonoidHom.comp principalIdealHom.toMonoidHom

theorem rowCoefficient_apply (η : HeckeFamily.Character) (Xi : O →* ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) (m a : O) :
    rowCoefficient η Xi s hs m a = HeckeFamily.elementCoeff η a * star (Xi a) *
      sexticReciprocityPhase s a * idealRowHom m (Ideal.span {a}) := rfl

theorem rowCoefficient_apply_unit (η : HeckeFamily.Character) (Xi : O →* ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) (m a : O) (hXi : ‖Xi a‖ = 1) :
    rowCoefficient η Xi s hs m a = HeckeFamily.elementCoeff η a * (Xi a)⁻¹ *
      sexticReciprocityPhase a s * idealRowHom m (Ideal.span {a}) := by
  rw [rowCoefficient_apply]
  have hc : star (Xi a) = (Xi a)⁻¹ := (Complex.inv_eq_conj hXi).symm
  have hsym : sexticReciprocityPhase s a = sexticReciprocityPhase a s := by
    simp only [sexticReciprocityPhase, QuadraticAllOddCRT.quadraticRaySign_symm]
  rw [hc, hsym]

theorem rowCoefficient_norm_le_one (η : HeckeFamily.Character) (Xi : O →* ℂ)
    (hXi : ∀ a, ‖Xi a‖ ≤ 1) (s : O) (hs : Supported (Ideal.span {s})) (m a : O) :
    ‖rowCoefficient η Xi s hs m a‖ ≤ 1 := by
  rw [rowCoefficient_apply]
  simp only [norm_mul, norm_star]
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (idealRowHom_norm _ _)
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (sexticReciprocityPhase_norm _ _)
  exact (mul_le_of_le_one_left (norm_nonneg _) (targetMonoid_norm_le_one η a)).trans (hXi a)

def spectralSummand (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (t : ℂ) (I J : Ideal O) : ℂ :=
  (completedMask S D I J * completedCorrection I J *
    (columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I) : ℂ)) * cubeWeight Ψ J) *
      (CubicEisenstein.fullIdealWeight t I * CubicEisenstein.fullIdealWeight (3 * t) J)

def spectralRow (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ) (t : ℂ) : ℂ :=
  ∑' p : Ideal O × Ideal O, spectralSummand S D Ψ t p.1 p.2

theorem spectralSummand_norm_le (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (t : ℂ) (I J : Ideal O) :
    ‖spectralSummand S D Ψ t I J‖ ≤
      2 * (‖CubicEisenstein.fullIdealWeight t I‖ *
        ‖CubicEisenstein.fullIdealWeight (3 * t) J‖) := by
  have hmc : ‖completedMask S D I J * completedCorrection I J‖ ≤ 2 := by
    rw [norm_mul]
    exact (mul_le_mul (completedMask_norm_le_one S D I J)
      (completedCorrection_norm_le_two I J) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hcol := columnWeight_div_sqrt_norm_le_one Ψ hΨ I
  have hcube := cubeWeight_norm_le_one Ψ hΨ J
  have hc : ‖completedMask S D I J * completedCorrection I J *
      (columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I) : ℂ)) * cubeWeight Ψ J‖ ≤ 2 := by
    rw [norm_mul, norm_mul]
    exact (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hcube).trans
      ((mul_le_of_le_one_right (norm_nonneg _) hcol).trans hmc)
  unfold spectralSummand
  simpa only [norm_mul] using mul_le_mul_of_nonneg_right hc (mul_nonneg
    (norm_nonneg (CubicEisenstein.fullIdealWeight t I))
    (norm_nonneg (CubicEisenstein.fullIdealWeight (3 * t) J)))

theorem spectralRow_summable (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (t : ℂ) (ht : 1 < t.re) :
    Summable (fun p : Ideal O × Ideal O => spectralSummand S D Ψ t p.1 p.2) := by
  have ht3 : 1 < (3 * t).re := by
    norm_num [Complex.mul_re]
    linarith
  have h1 := CubicEisenstein.fullIdealWeight_summable_norm t ht
  have h3 := CubicEisenstein.fullIdealWeight_summable_norm (3 * t) ht3
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => spectralSummand_norm_le S D Ψ hΨ t p.1 p.2)
    ((h1.mul_of_nonneg h3 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_left 2)

end SevenEighths.ProbeRow
end

end OAI

import OAI.NumberTheory.DirichletL.RayOrthogonality
import OAI.NumberTheory.DirichletL.Hecke.LogDerivative

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeRayFamily
open HeckeFamily

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

def character (χ : RayOrthogonality.rayCharacters M) : Character :=
  Character.ofResidue M (NeZero.ne M) χ.val ((RayOrthogonality.mem_rayCharacters_iff M χ.val).mp χ.property)

theorem idealCoeff_character (χ : RayOrthogonality.rayCharacters M) (I : Ideal O) :
    idealCoeff (character M χ) I = RayOrthogonality.idealCharacter M χ I := rfl

theorem principal_iff (χ : RayOrthogonality.rayCharacters M) :
    (character M χ).residue = 1 ↔ χ = 1 := by
  change χ.val = 1 ↔ χ = 1
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem character_entire (χ : RayOrthogonality.rayCharacters M) (hχ : χ ≠ 1) :
    Differentiable ℂ (LFunction (character M χ)) :=
  LFunction_entire_nonprincipal _ (fun h => hχ ((principal_iff M χ).mp h))

theorem character_boundary_ne_zero (χ : RayOrthogonality.rayCharacters M)
    {s : ℂ} (hs : 1 ≤ s.re) (hpole : s ≠ 1 ∨ χ ≠ 1) :
    LFunction (character M χ) s ≠ 0 := by
  apply LFunction_ne_zero_of_one_le_re _ hs
  exact hpole.imp id (fun h hn => h ((principal_iff M χ).mp hn))

theorem principal_pole_ne_zero : HeckeOrigin.poleRemoved (character M 1) 1 ≠ 0 :=
  HeckeOrigin.poleRemoved_one_ne_zero _ rfl

theorem average_idealCoeff (I : Ideal O) :
    (RayOrthogonality.rayCard M : ℂ)⁻¹ *
      ∑ χ : RayOrthogonality.rayCharacters M, idealCoeff (character M χ) I =
      if I ∈ RayOrthogonality.principalIdeals M then 1 else 0 := by
  simp only [idealCoeff_character]
  simpa only [div_eq_mul_inv, mul_comm] using RayOrthogonality.average_idealCharacters M I

theorem mangoldt_LSeries (χ : RayOrthogonality.rayCharacters M)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (IdealLogDerivative.coeff (RayOrthogonality.idealCharacter M χ)) s =
      (if χ = 1 then (1 : ℂ)/(s-1) else 0) +
        HeckeLogDerivative.poleSubtracted (character M χ) s := by
  have h := HeckeLogDerivative.coeff_LSeries_eq_poleSubtracted (character M χ) hs
  change LSeries (IdealLogDerivative.coeff (idealCoeff (character M χ))) s = _ at h
  have heq : idealCoeff (character M χ) = RayOrthogonality.idealCharacter M χ := rfl
  rw [heq, principal_iff] at h
  by_cases hc : χ = 1 <;> simpa [hc] using h

theorem poleSubtracted_analyticAt (χ : RayOrthogonality.rayCharacters M)
    {s : ℂ} (hs : 1 ≤ s.re) :
    AnalyticAt ℂ (HeckeLogDerivative.poleSubtracted (character M χ)) s :=
  HeckeLogDerivative.poleSubtracted_analyticAt _ hs

end SevenEighths.HeckeRayFamily

end

end OAI

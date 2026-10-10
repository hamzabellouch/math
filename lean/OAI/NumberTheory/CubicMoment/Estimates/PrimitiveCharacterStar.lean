import OAI.NumberTheory.CubicMoment.Angular.AngularHeckeCharacter

namespace OAI

/-! Conjugation preserves the actual finite conductor. For a cubic
character, its square is precisely its conjugate, including the zero extension. -/
noncomputable section
namespace CubicFirstMoment

lemma ResidueCharacterInduces.star {q d : Eisenstein}
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (h : ResidueCharacterInduces q d χ ψ) :
    ResidueCharacterInduces q d (star χ) (star ψ) := by
  refine ⟨h.1,?_⟩
  intro x hx
  exact congrArg (Star.star : ℂ → ℂ) (h.2 x hx)

lemma PrimitiveResidueCharacter.star {q : Eisenstein} {χ : MulChar (Residues q) ℂ}
    (h : PrimitiveResidueCharacter q χ) : PrimitiveResidueCharacter q (star χ) := by
  intro d ψ hi
  apply h d (Star.star ψ)
  simpa only [star_star] using hi.star

lemma cubic_residue_character_sq_eq_star {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (h3 : χ^3=1) : χ^2=star χ := by
  let : Finite (Residues q) := finite_residues hq
  rw [MulChar.star_eq_inv]
  have he : χ^2*χ=1 := by simpa only [←pow_succ] using h3
  calc
    χ^2 = (χ^2*χ)*χ⁻¹ := by group
    _ = χ⁻¹ := by rw [he,one_mul]

lemma star_residue_character_ne_one {q : Eisenstein} {χ : MulChar (Residues q) ℂ}
    (h : χ ≠ 1) : star χ ≠ 1 := by
  intro he
  have hh := congrArg star he
  simp only [star_star,star_one] at hh
  exact h hh

lemma star_residue_character_units {q : Eisenstein} {χ : MulChar (Residues q) ℂ}
    (h : ∀ u : Eisensteinˣ, χ (Ideal.Quotient.mk (modulus q) u)=1) :
    ∀ u : Eisensteinˣ, (star χ) (Ideal.Quotient.mk (modulus q) u)=1 := by
  intro u
  rw [MulChar.star_apply,h u,star_one]

lemma residueIdealChar_cubic_square {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (h3 : χ^3=1) (ν : EisensteinIdealExponent) :
    (residueIdealChar q χ ν)^2=residueIdealChar q (star χ) ν := by
  rw [←cubic_residue_character_sq_eq_star hq χ h3]
  exact (MulChar.pow_apply' χ (by norm_num : (2:ℕ) ≠ 0) _).symm

end CubicFirstMoment

end

end OAI

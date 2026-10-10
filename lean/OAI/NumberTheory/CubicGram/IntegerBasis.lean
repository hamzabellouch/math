import Mathlib
import OAI.NumberTheory.CubicGram.Coordinates

namespace OAI

/-! The integral basis, multiplication norm and finite residue quotients. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
def coordinatesMap : (Fin 2 → ℤ) →ₗ[ℤ] Eisenstein where
  toFun v := ofCoords (v 0) (v 1)
  map_add' v w := by simp [ofCoords, add_mul]; ring
  map_smul' n v := by simp [ofCoords]; ring

lemma coordinatesMap_bijective : Function.Bijective coordinatesMap := by
  constructor
  · intro v w h
    have hh := coordinates_unique (congrArg (fun z : Eisenstein => (z : ℂ)) h)
    funext i
    fin_cases i
    · exact hh.1
    · exact hh.2
  · intro z
    obtain ⟨a,b,h⟩ := exists_coordinates z
    exact ⟨![a,b], Subtype.ext h.symm⟩

def coordinatesEquiv : (Fin 2 → ℤ) ≃ₗ[ℤ] Eisenstein :=
  LinearEquiv.ofBijective coordinatesMap coordinatesMap_bijective

def integerBasis : Basis (Fin 2) ℤ Eisenstein :=
  (Pi.basisFun ℤ (Fin 2)).map coordinatesEquiv

instance : Module.Free ℤ Eisenstein := Module.Free.of_basis integerBasis
instance : Module.Finite ℤ Eisenstein := Module.Finite.of_basis integerBasis

@[simp] lemma integerBasis_zero : integerBasis 0 = 1 := by
  simp [integerBasis, coordinatesEquiv, coordinatesMap, ofCoords, Pi.basisFun_apply]

@[simp] lemma integerBasis_one : integerBasis 1 = omegaE := by
  simp [integerBasis, coordinatesEquiv, coordinatesMap, ofCoords, Pi.basisFun_apply]

lemma integerBasis_repr_ofCoords (a b : ℤ) :
    integerBasis.repr (ofCoords a b) = Finsupp.equivFunOnFinite.symm ![a,b] := by
  apply Finsupp.equivFunOnFinite.injective
  change coordinatesEquiv.symm (ofCoords a b) = ![a,b]
  apply coordinatesEquiv.injective
  simp only [LinearEquiv.apply_symm_apply]
  rfl

lemma ofCoords_mul (a b c d : ℤ) :
    ofCoords a b * ofCoords c d = ofCoords (a*c-b*d) (a*d+b*c-b*d) := by
  apply Subtype.ext
  change ((a : ℂ) + b * omega) * (c + d * omega) = _
  rw [ofCoords_coe]
  have h : omega^2 = -omega - 1 := by linear_combination omega_quadratic
  push_cast
  ring_nf
  rw [h]
  ring

lemma ofCoords_mul_omega (a b : ℤ) : ofCoords a b * omegaE = ofCoords (-b) (a-b) := by
  rw [show omegaE = ofCoords 0 1 by simp [ofCoords], ofCoords_mul]
  simp

lemma leftMulMatrix_ofCoords (a b : ℤ) :
    Algebra.leftMulMatrix integerBasis (ofCoords a b) = !![a, -b; b, a-b] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Algebra.leftMulMatrix_eq_repr_mul, ofCoords_mul_omega, integerBasis_repr_ofCoords]

lemma algebra_norm_ofCoords (a b : ℤ) :
    Algebra.norm ℤ (ofCoords a b) = a^2 - a*b + b^2 := by
  rw [Algebra.norm_eq_matrix_det integerBasis, leftMulMatrix_ofCoords, Matrix.det_fin_two]
  simp
  ring

lemma algebra_norm_cast (z : Eisenstein) : (Algebra.norm ℤ z : ℝ) = norm z := by
  obtain ⟨⟨a,b⟩,rfl⟩ := ofCoords_surjective z
  rw [algebra_norm_ofCoords, norm, ofCoords_coe, coordinates_norm]

lemma residues_card {z : Eisenstein} (hz : z ≠ 0) : Nat.card (Residues z) = normNat z := by
  have hdet := Submodule.natAbs_det_basis_change integerBasis
    ((modulus z).restrictScalars ℤ) (Ideal.basisSpanSingleton integerBasis hz)
  have hh : integerBasis.det (fun i =>
      ((Ideal.basisSpanSingleton integerBasis hz i : modulus z) : Eisenstein)) =
      Algebra.norm ℤ z := by
    rw [Algebra.norm_eq_matrix_det integerBasis, Basis.det_apply]
    congr 1
    ext i j
    simp [Basis.toMatrix_apply, Ideal.basisSpanSingleton_apply,
      Algebra.leftMulMatrix_eq_repr_mul]
  change (integerBasis.det (fun i =>
    ((Ideal.basisSpanSingleton integerBasis hz i : modulus z) : Eisenstein))).natAbs =
    Nat.card (Residues z) at hdet
  rw [hh] at hdet
  have hn : 0 ≤ Algebra.norm ℤ z := by
    exact_mod_cast (algebra_norm_cast z).symm ▸ norm_nonneg z
  rw [← hdet]
  apply Nat.cast_injective (R := ℝ)
  rw [normNat_cast, ← Int.cast_natCast, Int.natCast_natAbs, abs_of_nonneg hn, algebra_norm_cast]

lemma norm_eq_zero_iff {z : Eisenstein} : norm z = 0 ↔ z = 0 := by
  rw [norm, Complex.normSq_eq_zero]
  constructor
  · exact fun h => Subtype.ext h
  · rintro rfl
    rfl

lemma normNat_ne_zero {z : Eisenstein} (hz : z ≠ 0) : normNat z ≠ 0 := by
  intro h
  apply hz
  apply norm_eq_zero_iff.mp
  rw [← normNat_cast, h, Nat.cast_zero]

lemma finite_residues {z : Eisenstein} (hz : z ≠ 0) : Finite (Residues z) :=
  Nat.finite_of_card_ne_zero (by rw [residues_card hz]; exact normNat_ne_zero hz)

end CubicFirstMoment
end
end

end OAI

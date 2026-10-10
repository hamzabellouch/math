import OAI.NumberTheory.CubicMoment.Estimates.PrimitiveResidueFourier

namespace OAI

/-! Finite Fourier inversion for the periodic numerator twists in the
cubic theta formula. The trace pairing is perfect for primary moduli. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

/-- The source trace character, without the inverse-different factor.
For primary q the removed factor is a unit modulo q. -/
def cubicThetaResidueChar (q : Eisenstein) (hq : q ≠ 0) : AddChar (Residues q) ℂ :=
  (residueFourierChar q hq).mulShift (Ideal.Quotient.mk (modulus q) lambdaE)

lemma cubicThetaResidueChar_mk (q : Eisenstein) (hq : q ≠ 0) (a : Eisenstein) :
    cubicThetaResidueChar q hq (Ideal.Quotient.mk (modulus q) a) =
      (Real.fourierChar (tracePair (a:ℂ) (1/(q:ℂ))):ℂ) := by
  rw [cubicThetaResidueChar,AddChar.mulShift_apply,←map_mul,residueFourierChar_mk]
  congr 2
  unfold tracePair
  congr 2
  push_cast
  rw [lambdaE_coe]
  field_simp [traceLambda_ne_zero]

lemma cubicThetaResidueChar_primitive {q : Eisenstein} (hq : primary q) :
    (cubicThetaResidueChar q (primary_ne_zero hq)).IsPrimitive := by
  let u : (Residues q)ˣ := (residue_isUnit_of_isCoprime (primary_coprime_lambda hq)).unit
  have hu : (u : Residues q) = Ideal.Quotient.mk (modulus q) lambdaE :=
    (residue_isUnit_of_isCoprime (primary_coprime_lambda hq)).unit_spec
  intro a ha he
  have hna : (u:Residues q)*a ≠ 0 := by
    intro hz
    apply ha
    have h := congrArg (fun x : Residues q => (u⁻¹:((Residues q)ˣ))*x) hz
    simpa only [←mul_assoc,Units.inv_mul,mul_zero,one_mul] using h
  apply residueFourierChar_isPrimitive q (primary_ne_zero hq)
    (a := (u:Residues q)*a) hna
  simpa only [cubicThetaResidueChar,AddChar.mulShift_mulShift,←hu] using he

/-- Finite numerator Fourier transform in the exact trace normalization. -/
def cubicThetaTwistTransform (q : Eisenstein) (hq : q ≠ 0)
    [Fintype (Residues q)] (ψ : Residues q → ℂ) (u : Residues q) : ℂ :=
  ∑ x : Residues q, ψ x*cubicThetaResidueChar q hq (u*x)

lemma cubicThetaTwist_fourier_sum {q : Eisenstein} (hq : primary q)
    [Fintype (Residues q)] (ψ : Residues q → ℂ) (y : Residues q) :
    (∑ u : Residues q, cubicThetaTwistTransform q (primary_ne_zero hq) ψ u*
      cubicThetaResidueChar q (primary_ne_zero hq) (-u*y)) = (norm q:ℂ)*ψ y := by
  classical
  let χ := cubicThetaResidueChar q (primary_ne_zero hq)
  have hp : χ.IsPrimitive := cubicThetaResidueChar_primitive hq
  unfold cubicThetaTwistTransform
  rw [show (fun u : Residues q =>
      (∑ x : Residues q, ψ x*χ (u*x))*χ (-u*y)) =
      fun u => ∑ x : Residues q, ψ x*χ (u*(x-y)) by
    funext u
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    rw [mul_assoc,←χ.map_add_eq_mul]
    congr 2
    ring]
  rw [Finset.sum_comm]
  calc
    _ = ∑ x : Residues q, ψ x*∑ u : Residues q, χ (u*(x-y)) := by
      simp only [Finset.mul_sum]
    _ = ∑ x : Residues q, ψ x*(if x=y then (Fintype.card (Residues q):ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [AddChar.sum_mulShift (x-y) hp,sub_eq_zero]
      split_ifs <;> simp
    _ = (norm q:ℂ)*ψ y := by
      simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      rw [←Nat.card_eq_fintype_card,residues_card (primary_ne_zero hq)]
      have hn : (normNat q:ℂ) = (norm q:ℂ) := by exact_mod_cast normNat_cast q
      rw [hn]
      ring

/-- Fourier inversion for an arbitrary periodic coefficient twist. -/
theorem cubicThetaTwist_fourier_inversion {q : Eisenstein} (hq : primary q)
    [Fintype (Residues q)] (ψ : Residues q → ℂ) (y : Residues q) :
    ψ y = (norm q:ℂ)⁻¹*∑ u : Residues q,
      cubicThetaTwistTransform q (primary_ne_zero hq) ψ u*
        cubicThetaResidueChar q (primary_ne_zero hq) (-u*y) := by
  rw [cubicThetaTwist_fourier_sum hq]
  have hN : (norm q:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (norm_pos_of_ne_zero (primary_ne_zero hq))
  rw [←mul_assoc,inv_mul_cancel₀ hN,one_mul]

end CubicFirstMoment

end

end OAI

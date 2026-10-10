import OAI.NumberTheory.Ostmann.Tree.ConstrainedCharacterSum
import OAI.NumberTheory.Ostmann.Tree.TensorParseval

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {F I : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [DecidableEq I]
local instance tensorProjectionFintype : Fintype (MulChar F ℂ) := Fintype.ofFinite _

def signedUnit (b : Bool) (z : Fˣ) : Fˣ := if b then z else z⁻¹

def signedCharacter (b : Bool) (χ : MulChar F ℂ) : MulChar F ℂ := if b then χ else χ⁻¹

def signedCharacterEquiv (b : Bool) : MulChar F ℂ ≃ MulChar F ℂ :=
  if b then Equiv.refl _ else Equiv.inv _

omit [Fintype F] [DecidableEq F] in
theorem signedCharacterEquiv_apply (b : Bool) (χ : MulChar F ℂ) :
    signedCharacterEquiv b χ=signedCharacter b χ := by cases b <;> rfl

omit [Fintype F] [DecidableEq F] in
theorem signedCharacter_apply (b : Bool) (χ : MulChar F ℂ) (z : Fˣ) :
    signedCharacter b χ z=χ (signedUnit b z) := by
  cases b
  · simp only [signedCharacter,signedUnit,Bool.false_eq_true,ite_false,MulChar.inv_apply',
      Units.val_inv_eq_inv_val]
  · rfl

def tensorConstraint (sign : I → Bool) (ρ : I → MulChar F ℂ) : MulChar F ℂ :=
  ∏ i,signedCharacter (sign i) (ρ i)

def tensorSignedProjection (f : I → Fˣ → ℂ) (sign : I → Bool) (t : I → Fˣ) : ℂ :=
  (Fintype.card Fˣ:ℂ)⁻¹*∑ z : Fˣ,∏ i,f i (t i*signedUnit (sign i) z)

def tensorProjectedCoefficient (f : I → Fˣ → ℂ) (sign : I → Bool)
    (ρ : I → MulChar F ℂ) : ℂ := by
  classical
  exact if tensorConstraint sign ρ=1 then tensorCoefficient f ρ else 0

omit [Fintype F] [DecidableEq F] [DecidableEq I] in
theorem tensorCharacter_signed_action (ρ : I → MulChar F ℂ) (sign : I → Bool)
    (t : I → Fˣ) (z : Fˣ) :
    tensorCharacter ρ (fun i => t i*signedUnit (sign i) z)=
      tensorCharacter ρ t*tensorConstraint sign ρ z := by
  simp only [tensorCharacter,Units.val_mul,map_mul,Finset.prod_mul_distrib,
    tensorConstraint,character_product_apply,signedCharacter_apply]

theorem tensorSignedProjection_series (f : I → Fˣ → ℂ) (sign : I → Bool) (t : I → Fˣ) :
    tensorSignedProjection f sign t=tensorSeries (tensorProjectedCoefficient f sign) t := by
  classical
  have hN : (Fintype.card Fˣ:ℂ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold tensorSignedProjection
  simp_rw [tensor_mellin_expansion,tensorCharacter_signed_action]
  rw [Finset.sum_comm,Finset.mul_sum]
  unfold tensorSeries
  apply Finset.sum_congr rfl
  intro ρ _
  have hp (z : Fˣ) :
      tensorCoefficient f ρ*(tensorCharacter ρ t*tensorConstraint sign ρ z)=
      (tensorCoefficient f ρ*tensorCharacter ρ t)*tensorConstraint sign ρ z := by ring
  simp_rw [hp]
  rw [← Finset.mul_sum,sum_units_mulChar]
  unfold tensorProjectedCoefficient
  split_ifs <;> simp_all
  field_simp

theorem tensorSignedProjection_parseval (f : I → Fˣ → ℂ) (sign : I → Bool) :
    (Fintype.card (I → Fˣ):ℝ)⁻¹*
      (∑ t : I → Fˣ,‖tensorSignedProjection f sign t‖^2) =
      ∑ ρ : I → MulChar F ℂ,
        if tensorConstraint sign ρ=1 then ∏ i,‖mellin (f i) (ρ i)‖^2 else 0 := by
  classical
  simp_rw [tensorSignedProjection_series]
  rw [tensorSeries_parseval]
  apply Finset.sum_congr rfl
  intro ρ _
  unfold tensorProjectedCoefficient
  split_ifs <;> simp [tensorCoefficient,norm_prod,Finset.prod_pow]

end
end Ostmann.FiniteField

end OAI

import Mathlib
import OAI.Analysis.WeakInfiniteness.FiniteUnitaryLog

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint

namespace WeakPureInfiniteness

universe u

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def pairUnitary (x : A) (b : Bool) : unitary A :=
  selfAdjoint.expUnitary ((2 * Real.pi) • (if b then realPart x else imaginaryPart x))

def pairGroup (x : A) : FreeGroup Bool →* unitary A :=
  FreeGroup.lift (pairUnitary x)

@[simp] lemma pairGroup_of (x : A) (b : Bool) :
    pairGroup x (FreeGroup.of b) = pairUnitary x b := by simp [pairGroup]

lemma map_pairUnitary (f : A →⋆ₐ[ℂ] B) (x : A) (b : Bool) :
    f (pairUnitary x b) = (pairUnitary (f x) b : B) := by
  cases b <;> simp only [pairUnitary, Bool.false_eq_true, ite_false, ite_true,
    selfAdjoint.expUnitary_coe]
  all_goals
    let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
    let : NormedAlgebra ℚ B := NormedAlgebra.restrictScalars ℚ ℂ B
    have hf : Continuous f := (f.toAlgHom.toLinearMap.mkContinuous 1
      (fun x => by
        change ‖f x‖ ≤ 1 * ‖x‖
        rw [one_mul]
        exact NonUnitalStarAlgHom.norm_apply_le f x)).continuous
    rw [NormedSpace.map_exp f hf]
    congr 1
    change f (I • ((2 * Real.pi) • (_ : A))) = I • ((2 * Real.pi) • (_ : B))
    rw [map_smul, ← Complex.coe_smul, map_smul]
    simp only [map_realPart, map_imaginaryPart, Complex.coe_smul]

lemma map_pairGroup (f : A →⋆ₐ[ℂ] B) (x : A) (g : FreeGroup Bool) :
    f (pairGroup x g) = (pairGroup (f x) g : B) := by
  have h : (Unitary.map ({ f.toMonoidHom with map_star' := map_star f } : A →⋆* B)).toMonoidHom.comp (pairGroup x) =
      pairGroup (f x) := by
    apply FreeGroup.ext_hom
    intro b
    apply Subtype.ext
    change f (pairGroup x (FreeGroup.of b)) = (pairGroup (f x) (FreeGroup.of b) : B)
    rw [pairGroup_of, pairGroup_of]
    exact map_pairUnitary f x b
  exact congrArg (fun ρ : FreeGroup Bool →* unitary B => (ρ g : B)) h

def logarithmContraction (S T : unitary A) : A :=
  (2 * Real.pi)⁻¹ • ((Unitary.argSelfAdjoint S : A) +
    Complex.I • (Unitary.argSelfAdjoint T : A))

lemma norm_logarithmContraction_le (S T : unitary A) :
    ‖logarithmContraction S T‖ ≤ 1 := by
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  rw [logarithmContraction, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hp]
  apply (mul_le_mul_of_nonneg_left (norm_add_le _ _) (inv_nonneg.mpr hp.le)).trans
  rw [norm_smul, Complex.norm_I, one_mul]
  have hS : ‖(Unitary.argSelfAdjoint S : A)‖ ≤ Real.pi := Unitary.norm_argSelfAdjoint_le_pi S
  have hT : ‖(Unitary.argSelfAdjoint T : A)‖ ≤ Real.pi := Unitary.norm_argSelfAdjoint_le_pi T
  have hn := add_le_add hS hT
  have hn' : ‖(Unitary.argSelfAdjoint S : A)‖ + ‖(Unitary.argSelfAdjoint T : A)‖ ≤
      2 * Real.pi := by simpa only [two_mul] using hn
  exact (mul_le_mul_of_nonneg_left hn' (inv_nonneg.mpr hp.le)).trans_eq
    (inv_mul_cancel₀ (ne_of_gt hp))

lemma realPart_logarithmContraction (S T : unitary A) :
    (2 * Real.pi) • realPart (logarithmContraction S T) = Unitary.argSelfAdjoint S := by
  have hr (h : selfAdjoint A) : realPart (h : A) = h := Subtype.ext h.property.coe_realPart
  simp only [logarithmContraction, map_smul, map_add, realPart_I_smul, hr,
    (Unitary.argSelfAdjoint T).property.imaginaryPart, neg_zero, add_zero, smul_smul]
  rw [mul_inv_cancel₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero), one_smul]

lemma imaginaryPart_logarithmContraction (S T : unitary A) :
    (2 * Real.pi) • imaginaryPart (logarithmContraction S T) = Unitary.argSelfAdjoint T := by
  have hr (h : selfAdjoint A) : realPart (h : A) = h := Subtype.ext h.property.coe_realPart
  simp only [logarithmContraction, map_smul, map_add, imaginaryPart_I_smul, hr,
    (Unitary.argSelfAdjoint S).property.imaginaryPart, zero_add, smul_smul]
  rw [mul_inv_cancel₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero), one_smul]

lemma pairUnitary_logarithmContraction {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (S T : unitary (H →L[ℂ] H)) (b : Bool) :
    pairUnitary (logarithmContraction S T) b = if b then S else T := by
  let : CompleteSpace H := FiniteDimensional.complete ℂ H
  cases b <;> simp only [pairUnitary, Bool.false_eq_true, ite_false, ite_true]
  · rw [imaginaryPart_logarithmContraction, finite_expUnitary_argSelfAdjoint]
  · rw [realPart_logarithmContraction, finite_expUnitary_argSelfAdjoint]

end WeakPureInfiniteness
end

end OAI

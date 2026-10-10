import Mathlib
import OAI.Geometry.PrescribedPotential.CalabiTensorAlgebra

namespace OAI

/-! Calabi Frame Algebra. -/

section

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

def pullConnectionTensor (C : Matrix (Fin n) (Fin n) ℂ) (T : ConnectionTensor n) : ConnectionTensor n :=
  fun i => C⁻¹*(∑ p, C p i • T p)*C

lemma tensor_trace_changeBasis (C P M T U : Matrix (Fin n) (Fin n) ℂ) (hC : IsUnit C) :
    ((C⁻¹*T*C)*(C⁻¹*P*(Cᴴ)⁻¹)*(C⁻¹*U*C)ᴴ*(Cᴴ*M*C)).trace = (T*P*Uᴴ*M).trace := by
  have hc : C*C⁻¹=1 := Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hC)
  have hd : (Cᴴ)⁻¹*Cᴴ=1 := by
    rw [← Matrix.conjTranspose_nonsing_inv,← Matrix.conjTranspose_mul,hc,Matrix.conjTranspose_one]
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_nonsing_inv,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc C C⁻¹,hc,Matrix.one_mul,
    ← Matrix.mul_assoc (Cᴴ)⁻¹ Cᴴ,hd,Matrix.one_mul,
    ← Matrix.mul_assoc (Cᴴ)⁻¹ Cᴴ,hd,Matrix.one_mul]
  calc
    _ = ((C⁻¹*(T*P*Uᴴ*M))*C).trace := by simp only [mul_assoc]
    _ = ((C*C⁻¹)*(T*P*Uᴴ*M)).trace := Matrix.trace_mul_cycle _ _ _
    _ = _ := by simp only [hc,one_mul,mul_assoc]

lemma tensor_pair_mixed (P M Q C : Matrix (Fin n) (Fin n) ℂ) (T U : ConnectionTensor n) :
    (∑ i, ∑ j, Q i j * ((∑ p, C p i • T p)*P*(∑ q, C q j • U q)ᴴ*M).trace) =
      ∑ p, ∑ q, (C*Q*Cᴴ) p q*(T p*P*(U q)ᴴ*M).trace := by
  have he (i j) : ((∑ p, C p i • T p)*P*(∑ q, C q j • U q)ᴴ*M).trace =
      ∑ p, ∑ q, C p i * star (C q j) * (T p*P*(U q)ᴴ*M).trace := by
    simp only [Matrix.sum_mul,Matrix.conjTranspose_sum,Matrix.trace_sum,
      Matrix.smul_mul,Matrix.mul_smul,Matrix.conjTranspose_smul,Matrix.trace_smul,
      smul_eq_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  simp_rw [he]
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Finset.mul_sum,Finset.sum_mul]
  calc
    _ = ∑ p, ∑ q, ∑ i, ∑ j,
        Q i j * (C p i * star (C q j) * (T p*P*(U q)ᴴ*M).trace) := by
      conv_lhs => arg 2; ext i; rw [Finset.sum_comm]; arg 2; ext p; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring

lemma tensorPairAt_changeBasis (C P M : Matrix (Fin n) (Fin n) ℂ) (hC : IsUnit C)
    (T U : ConnectionTensor n) :
    tensorPairAt (C⁻¹*P*(Cᴴ)⁻¹) (Cᴴ*M*C) (pullConnectionTensor C T) (pullConnectionTensor C U) =
      tensorPairAt P M T U := by
  unfold tensorPairAt pullConnectionTensor
  simp_rw [tensor_trace_changeBasis C P M _ _ hC]
  rw [tensor_pair_mixed]
  have hc : C*C⁻¹=1 := Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hC)
  have hd : (Cᴴ)⁻¹*Cᴴ=1 := by
    rw [← Matrix.conjTranspose_nonsing_inv,← Matrix.conjTranspose_mul,hc,Matrix.conjTranspose_one]
  have he : C*(C⁻¹*P*(Cᴴ)⁻¹)*Cᴴ = P := by
    simp only [mul_assoc]
    rw [← mul_assoc C C⁻¹,hc,one_mul]
    simp only [hd,mul_one]
  simp only [he]
end KaehlerCalculus

end
end

end OAI

import Mathlib
import OAI.RepresentationTheory.PartialPermutation.FourierBessel
import OAI.RepresentationTheory.PartialPermutation.Characters
import OAI.RepresentationTheory.PartialPermutation.CosetCaps

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
namespace PartialPermutation
open scoped BigOperators ComplexConjugate

noncomputable section

def RightCosetCap {G : Type*} [Group G] [Fintype G]
    (f : G → ℝ) (H : Subgroup G) (B : ℝ) : Prop :=
  by classical exact ∀ g, ∑ h : H, f (h * g) ≤ B / H.index

section
variable {G : Type*} [Group G] [Fintype G]

def leftKernel (H : Subgroup G) (k : H → ℂ) (f : G → ℝ) (g : G) : ℂ :=
  by classical exact ∑ h : H, k h * (f ((h : G)⁻¹ * g) : ℂ)

lemma leftKernel_l2 (H : Subgroup G) (k : H → ℂ) (f : G → ℝ) (B : ℝ)
    (hf : ∀ g, 0 ≤ f g) (hcap : RightCosetCap f H B) :
    ∑ g, ‖leftKernel H k f g‖ ^ 2 ≤
      B / H.index * mass f * ∑ h : H, ‖k h‖ ^ 2 := by
  classical
  have hp (g : G) : ∑ h : H, f ((h : G)⁻¹ * g) ≤ B / H.index := by
    have he : ∑ h : H, f ((h : G)⁻¹ * g) = ∑ h : H, f ((h : G) * g) := by
      exact Fintype.sum_equiv (Equiv.inv H) _ _ (fun h => rfl)
    rw [he]
    exact hcap g
  have hpt (g : G) : ‖leftKernel H k f g‖ ^ 2 ≤
      B / H.index * ∑ h : H, f ((h : G)⁻¹ * g) * ‖k h‖ ^ 2 := by
    have h := norm_sum_weighted_sq_le (fun h : H => f ((h : G)⁻¹ * g))
      (fun h => hf _) k
    change ‖∑ h : H, k h * (f ((h : G)⁻¹ * g) : ℂ)‖ ^ 2 ≤ _
    simp_rw [mul_comm (k _)]
    exact h.trans (mul_le_mul_of_nonneg_right (hp g)
      (Finset.sum_nonneg fun h _ => mul_nonneg (hf _) (sq_nonneg _)))
  calc
    _ ≤ ∑ g, B / H.index * ∑ h : H, f ((h : G)⁻¹ * g) * ‖k h‖ ^ 2 :=
      Finset.sum_le_sum fun g _ => hpt g
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      have he (h : H) : ∑ g, f ((h : G)⁻¹ * g) = mass f := by
        exact Fintype.sum_equiv (Equiv.mulLeft (h : G)⁻¹) _ _ (fun g => rfl)
      simp_rw [← Finset.sum_mul, he]
      rw [← Finset.mul_sum, mul_assoc]

lemma complexFourier_leftKernel {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (H : Subgroup G) (k : H → ℂ) (f : G → ℝ) :
    complexFourier ρ (leftKernel H k f) =
      complexFourier (ρ.comp H.subtype) k * complexFourier ρ (fun g => (f g : ℂ)) := by
  classical
  unfold complexFourier leftKernel
  simp_rw [Finset.sum_smul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  apply Fintype.sum_equiv (Equiv.mulLeft (h : G)⁻¹)
  intro g
  simp only [smul_mul_smul_comm, ← map_mul, MonoidHom.comp_apply, Equiv.coe_mulLeft,
    Subgroup.subtype_apply, mul_inv_cancel_left]

lemma kernel_hs_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    [Representation.IsIrreducible ρ] (H : Subgroup G) (k : H → ℂ)
    (d : ℕ) (hk : ∑ h : H, ‖k h‖ ^ 2 = (d : ℝ)^2 / Fintype.card H)
    (f : G → ℝ) (B : ℝ) (hf : ∀ g, 0 ≤ f g) (hcap : RightCosetCap f H B) :
    (Module.finrank ℂ V : ℝ) *
      hsNormSq (complexFourier (ρ.comp H.subtype) k * complexFourier ρ (fun g => f g)) ≤
      B * mass f * (d : ℝ)^2 := by
  classical
  have hc : (H.index : ℝ) * (Fintype.card H : ℝ) = (Fintype.card G : ℝ) := by
    exact_mod_cast (by simpa only [Nat.card_eq_fintype_card] using H.index_mul_card)
  have hi : (H.index : ℝ) ≠ 0 := by
    exact_mod_cast H.index_ne_zero_of_finite
  have hh : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ (Fintype.card G : ℝ) * ∑ g, ‖leftKernel H k f g‖ ^ 2 := by
      rw [← complexFourier_leftKernel]
      exact fourier_bessel ρ hρ _
    _ ≤ (Fintype.card G : ℝ) * (B / H.index * mass f * ∑ h : H, ‖k h‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (leftKernel_l2 H k f B hf hcap) (by positivity)
    _ = _ := by rw [hk, ← hc]; field_simp

lemma inverse_rightCap (H : Subgroup G) (f : G → ℝ) (B : ℝ)
    (hcap : LeftCosetCap f H B) : RightCosetCap (fun g => f g⁻¹) H B := by
  intro g
  have he : ∑ h : H, f (((h : G) * g)⁻¹) = ∑ h : H, f (g⁻¹ * h) := by
    apply Fintype.sum_equiv (Equiv.inv H)
    intro h
    simp
  rw [he]
  exact hcap g⁻¹

lemma mass_inverse (f : G → ℝ) : mass (fun g => f g⁻¹) = mass f := by
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun g => rfl)

lemma complexFourier_adjoint {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (f : G → ℂ) :
    LinearMap.adjoint (complexFourier ρ f) = complexFourier ρ (fun g => conj (f g⁻¹)) := by
  unfold complexFourier
  simp only [map_sum, map_smulₛₗ, unitary_adjoint ρ hρ]
  apply Fintype.sum_equiv (Equiv.inv G)
  intro g
  simp

lemma complexFourier_selfAdjoint {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (f : G → ℂ) (hf : ∀ g, f g⁻¹ = conj (f g)) :
    LinearMap.adjoint (complexFourier ρ f) = complexFourier ρ f := by
  rw [complexFourier_adjoint ρ hρ]
  simp [hf]

lemma kernel_hs_bound_right {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    [Representation.IsIrreducible ρ] (H : Subgroup G) (k : H → ℂ)
    (d : ℕ) (hk : ∑ h : H, ‖k h‖ ^ 2 = (d : ℝ)^2 / Fintype.card H)
    (hki : ∀ h, k h⁻¹ = conj (k h))
    (f : G → ℝ) (B : ℝ) (hf : ∀ g, 0 ≤ f g) (hcap : LeftCosetCap f H B) :
    (Module.finrank ℂ V : ℝ) *
      hsNormSq (complexFourier ρ (fun g => f g) * complexFourier (ρ.comp H.subtype) k) ≤
      B * mass f * (d : ℝ)^2 := by
  have hi := kernel_hs_bound ρ hρ H k d hk (fun g => f g⁻¹) B
    (fun g => hf _) (inverse_rightCap H f B hcap)
  rw [mass_inverse] at hi
  have hP := complexFourier_selfAdjoint (ρ.comp H.subtype) (fun g => hρ g) k hki
  have hA : LinearMap.adjoint (complexFourier ρ (fun g => (f g⁻¹ : ℂ))) =
      complexFourier ρ (fun g => (f g : ℂ)) := by
    rw [complexFourier_adjoint ρ hρ]
    simp
  rw [← hsNormSq_adjoint (_ * _), adjoint_mul_eq, hA, hP] at hi
  exact hi

lemma projection_kernel_mul {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (W : Submodule ℂ V) (P : Module.End ℂ V)
    (hP : LinearMap.adjoint P = P) (hact : ∀ x ∈ W, P x = x) :
    W.starProjection.toLinearMap * P = W.starProjection.toLinearMap := by
  have he : P * W.starProjection.toLinearMap = W.starProjection.toLinearMap := by
    ext x
    exact hact _ (W.starProjection_apply_mem x)
  have he' := congrArg LinearMap.adjoint he
  simpa only [adjoint_mul_eq, adjoint_projection_eq, hP] using he'

lemma hsNormSq_projection_kernel_left {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (W : Submodule ℂ V)
    (P A : Module.End ℂ V) (hP : LinearMap.adjoint P = P)
    (hact : ∀ x ∈ W, P x = x) :
    hsNormSq (W.starProjection.toLinearMap * A) ≤ hsNormSq (P * A) := by
  have h := hsNormSq_projection_left W (P * A)
  rw [← mul_assoc, projection_kernel_mul W P hP hact] at h
  exact h

lemma hsNormSq_projection_kernel_right {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (W : Submodule ℂ V)
    (P A : Module.End ℂ V) (hP : LinearMap.adjoint P = P)
    (hact : ∀ x ∈ W, P x = x) :
    hsNormSq (A * W.starProjection.toLinearMap) ≤ hsNormSq (A * P) := by
  rw [← hsNormSq_adjoint (A * _), adjoint_mul_eq, adjoint_projection_eq,
    ← hsNormSq_adjoint (A * P), adjoint_mul_eq, hP]
  exact hsNormSq_projection_kernel_left W P (LinearMap.adjoint A) hP hact

end
end
end PartialPermutation

end

end OAI

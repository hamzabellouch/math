import Mathlib
import OAI.RepresentationTheory.PartialPermutation.SmallKernels

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
namespace PartialPermutation
noncomputable section
variable {G : Type*} [Group G] [Fintype G]

def smallDegreeSum (G : Type*) [Group G] [Fintype G] (R : ℝ) : ℝ :=
  ∑ c : IrreducibleIndex G, if (irreducibleDegree c : ℝ) ≤ R then
    (irreducibleDegree c : ℝ)^2 else 0

lemma smallTypeKernel_energy (R : ℝ) :
    (Fintype.card G : ℝ) * ∑ g, ‖smallTypeKernel G R g‖^2 = smallDegreeSum G R := by
  rw [finite_group_plancherel]
  unfold smallDegreeSum
  apply Finset.sum_congr rfl
  intro c _
  rw [complexFourier_smallTypeKernel]
  split_ifs <;> simp [hsNormSq, LinearMap.trace_one, pow_two]

lemma kernel_hs_energy {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    [Representation.IsIrreducible ρ] (H : Subgroup G) (k : H → ℂ)
    (f : G → ℝ) (B : ℝ) (hf : ∀ g, 0 ≤ f g) (hcap : RightCosetCap f H B) :
    (Module.finrank ℂ V : ℝ) *
      hsNormSq (complexFourier (ρ.comp H.subtype) k * complexFourier ρ (fun g => f g)) ≤
      B * mass f * ((Fintype.card H : ℝ) * ∑ h, ‖k h‖^2) := by
  have hc : (H.index : ℝ) * (Fintype.card H : ℝ) = (Fintype.card G : ℝ) := by
    exact_mod_cast (by simpa only [Nat.card_eq_fintype_card] using H.index_mul_card)
  have hi : (H.index : ℝ) ≠ 0 := by exact_mod_cast H.index_ne_zero_of_finite
  calc
    _ ≤ (Fintype.card G : ℝ) * ∑ g, ‖leftKernel H k f g‖^2 := by
      rw [← complexFourier_leftKernel]
      exact fourier_bessel ρ hρ _
    _ ≤ (Fintype.card G : ℝ) * (B / H.index * mass f * ∑ h, ‖k h‖^2) :=
      mul_le_mul_of_nonneg_left (leftKernel_l2 H k f B hf hcap) (by positivity)
    _ = _ := by rw [← hc]; field_simp

lemma small_type_hs_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    [Representation.IsIrreducible ρ] (H : Subgroup G) (R : ℝ)
    (f : G → ℝ) (B : ℝ) (hf : ∀ g, 0 ≤ f g) (hcap : LeftCosetCap f H B) :
    (Module.finrank ℂ V : ℝ) *
      hsNormSq (complexFourier ρ (fun g => f g) *
        complexFourier (ρ.comp H.subtype) (smallTypeKernel H R)) ≤
      B * mass f * smallDegreeSum H R := by
  have hi := kernel_hs_energy ρ hρ H (smallTypeKernel H R) (fun g => f g⁻¹) B
    (fun g => hf _) (inverse_rightCap H f B hcap)
  rw [mass_inverse, smallTypeKernel_energy] at hi
  have hP := complexFourier_selfAdjoint (G := H) (ρ.comp H.subtype)
    (fun (g : H) => hρ g) (smallTypeKernel H R) (smallTypeKernel_inv R)
  have hA : LinearMap.adjoint (complexFourier ρ (fun g => (f g⁻¹ : ℂ))) =
      complexFourier ρ (fun g => (f g : ℂ)) := by
    rw [complexFourier_adjoint ρ hρ]
    simp
  rw [← hsNormSq_adjoint (_ * _), adjoint_mul_eq, hA, hP] at hi
  exact hi

section Cover
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    {ι : Type*} [Fintype ι] (P : ι → Module.End ℂ V)
    (hP : ∀ i, LinearMap.adjoint (P i) = P i)
    (hcover : ∀ c : isotypicComponents ℂ[G] ρ.asModule,
      ∃ i, ∀ x ∈ componentSpace ρ c, P i x = x)

include ρ hρ hP hcover

lemma component_projection_cover_norm (v : V) : ‖v‖^2 ≤ ∑ i, ‖P i v‖^2 := by
  let : Fintype (isotypicComponents ℂ[G] ρ.asModule) := Fintype.ofFinite _
  calc
    _ = ∑ c, ‖(componentSpace ρ c).starProjection v‖^2 :=
      (sum_component_norm_sq ρ hρ v).symm
    _ ≤ ∑ c, ∑ i, ‖(componentSpace ρ c).starProjection (P i v)‖^2 := by
      apply Finset.sum_le_sum
      intro c _
      obtain ⟨i, hi⟩ := hcover c
      have he := congrArg (fun A : Module.End ℂ V => A v)
        (projection_kernel_mul (componentSpace ρ c) (P i) (hP i) hi)
      change (componentSpace ρ c).starProjection (P i v) =
        (componentSpace ρ c).starProjection v at he
      rw [← he]
      exact Finset.single_le_sum (fun j _ =>
        sq_nonneg (‖(componentSpace ρ c).starProjection (P j v)‖)) (Finset.mem_univ i)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      exact sum_component_norm_sq ρ hρ (P i v)

lemma component_projection_cover_hs (A : Module.End ℂ V) :
    hsNormSq A ≤ ∑ i, hsNormSq (A * P i) := by
  let e := stdOrthonormalBasis ℂ V
  calc
    _ = ∑ j, ‖LinearMap.adjoint A (e j)‖^2 := by
      rw [← hsNormSq_adjoint A, hsNormSq_eq_sum e]
    _ ≤ ∑ j, ∑ i, ‖P i (LinearMap.adjoint A (e j))‖^2 :=
      Finset.sum_le_sum (fun j _ => component_projection_cover_norm ρ hρ P hP hcover _)
    _ = ∑ i, hsNormSq (P i * LinearMap.adjoint A) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [hsNormSq_eq_sum e]
      rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← hsNormSq_adjoint (A * P i), adjoint_mul_eq, hP]

end Cover
end
end PartialPermutation

end

end OAI

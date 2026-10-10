import Mathlib
import OAI.RepresentationTheory.PartialPermutation.Plancherel
import OAI.RepresentationTheory.PartialPermutation.ConvolutionKernels
import OAI.RepresentationTheory.PartialPermutation.IsotypicProjections

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

lemma centralCharacterKernel_norm_sq {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (τ : Representation ℂ G W) [Representation.IsIrreducible τ] (hτ : IsUnitary τ) :
    ∑ g, ‖centralCharacterKernel τ g‖^2 =
      (Module.finrank ℂ W : ℝ)^2 / Fintype.card G := by
  have hN : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [centralCharacterKernel, unitary_character_inv τ hτ, norm_mul,
    norm_div, Complex.norm_natCast, Complex.norm_conj, mul_pow,
    ← Finset.mul_sum, character_norm_sq_sum τ hτ]
  field_simp

lemma centralCharacterKernel_inv {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (τ : Representation ℂ G W) (hτ : IsUnitary τ) (g : G) :
    centralCharacterKernel τ g⁻¹ = conj (centralCharacterKernel τ g) := by
  simp [centralCharacterKernel, unitary_character_inv τ hτ]

lemma kernel_hs_global (H : Subgroup G) (k : H → ℂ)
    (d : ℕ) (hk : ∑ h : H, ‖k h‖^2 = (d : ℝ)^2 / Fintype.card H)
    (f : G → ℝ) (B : ℝ) (hf : ∀ g, 0 ≤ f g) (hcap : RightCosetCap f H B) :
    ∑ c : IrreducibleIndex G, (irreducibleDegree c : ℝ) *
      hsNormSq (V := irreducibleSpace c)
        (complexFourier ((irreducibleRep c).comp H.subtype) k *
          complexFourier (irreducibleRep c) (fun g => (f g : ℂ))) ≤
        B * mass f * (d : ℝ)^2 := by
  have hc : (H.index : ℝ) * (Fintype.card H : ℝ) = (Fintype.card G : ℝ) := by
    exact_mod_cast (by simpa only [Nat.card_eq_fintype_card] using H.index_mul_card)
  have hi : (H.index : ℝ) ≠ 0 := by
    exact_mod_cast H.index_ne_zero_of_finite
  have hh : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ = (Fintype.card G : ℝ) * ∑ g, ‖leftKernel H k f g‖^2 := by
      rw [finite_group_plancherel]
      apply Finset.sum_congr rfl
      intro c _
      rw [complexFourier_leftKernel]
    _ ≤ (Fintype.card G : ℝ) * (B / H.index * mass f * ∑ h : H, ‖k h‖^2) :=
      mul_le_mul_of_nonneg_left (leftKernel_l2 H k f B hf hcap) (by positivity)
    _ = _ := by rw [hk, ← hc]; field_simp

lemma kernel_hs_global_right (H : Subgroup G) (k : H → ℂ)
    (d : ℕ) (hk : ∑ h : H, ‖k h‖^2 = (d : ℝ)^2 / Fintype.card H)
    (hki : ∀ h, k h⁻¹ = conj (k h))
    (f : G → ℝ) (B : ℝ) (hf : ∀ g, 0 ≤ f g) (hcap : LeftCosetCap f H B) :
    ∑ c : IrreducibleIndex G, (irreducibleDegree c : ℝ) *
      hsNormSq (V := irreducibleSpace c)
        (complexFourier (irreducibleRep c) (fun g => (f g : ℂ)) *
          complexFourier ((irreducibleRep c).comp H.subtype) k) ≤
        B * mass f * (d : ℝ)^2 := by
  have hl := kernel_hs_global H k d hk (fun g => f g⁻¹) B
    (fun g => hf _) (inverse_rightCap H f B hcap)
  rw [mass_inverse] at hl
  convert hl using 1
  apply Finset.sum_congr rfl
  intro c _
  have hP := complexFourier_selfAdjoint (G := H) (V := irreducibleSpace c)
    ((irreducibleRep c).comp H.subtype) (fun (g : H) => irreducibleRep_unitary c g) k hki
  have hA : LinearMap.adjoint (E := irreducibleSpace c) (F := irreducibleSpace c)
      (complexFourier (irreducibleRep c) (fun g => (f g⁻¹ : ℂ))) =
        complexFourier (irreducibleRep c) (fun g => (f g : ℂ)) := by
    rw [complexFourier_adjoint _ (irreducibleRep_unitary c)]
    simp
  rw [← hsNormSq_adjoint (V := irreducibleSpace c)
    (complexFourier ((irreducibleRep c).comp H.subtype) k *
      complexFourier (irreducibleRep c) (fun g => (f g⁻¹ : ℂ))), adjoint_mul_eq, hP, hA]

def fullIsotypicProjection {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (H : Subgroup G) (τ : Representation ℂ H W) :
    Module.End ℂ V := complexFourier (ρ.comp H.subtype) (centralCharacterKernel τ)

lemma centralCharacterKernel_equiv {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : Representation.Equiv ρ σ) : centralCharacterKernel ρ = centralCharacterKernel σ := by
  funext g
  simp only [centralCharacterKernel, Representation.char_iso e, e.toLinearEquiv.finrank_eq]

lemma fullIsotypicProjection_eq_component {V W : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (H : Subgroup G)
    (τ : Representation ℂ H W)
    (c : isotypicComponents ℂ[H] (Representation.asModule (ρ.comp H.subtype)))
    (e : Representation.Equiv τ (componentRep (ρ.comp H.subtype) c)) :
    fullIsotypicProjection ρ H τ =
      (componentSpace (ρ.comp H.subtype) c).starProjection.toLinearMap := by
  rw [fullIsotypicProjection, centralCharacterKernel_equiv e]
  exact component_kernel_eq_projection (G := H) (ρ.comp H.subtype)
    (fun (g : H) => hρ g) c

theorem central_isotypic_global (H : Subgroup G) {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (τ : Representation ℂ H W) [Representation.IsIrreducible τ] (hτ : IsUnitary τ)
    (f : G → ℝ) (B : ℝ) (hf : ∀ g, 0 ≤ f g) (hcap : LeftCosetCap f H B) :
    ∑ c : IrreducibleIndex G, (irreducibleDegree c : ℝ) *
      hsNormSq (V := irreducibleSpace c)
        (complexFourier (irreducibleRep c) (fun g => (f g : ℂ)) *
          fullIsotypicProjection (irreducibleRep c) H τ) ≤
      B * mass f * (Module.finrank ℂ W : ℝ)^2 :=
  kernel_hs_global_right H (centralCharacterKernel τ) _
    (centralCharacterKernel_norm_sq τ hτ) (centralCharacterKernel_inv τ hτ) f B hf hcap

end
end PartialPermutation

end

end OAI

import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteInvariantOrbit
import OAI.GroupTheory.PolycyclicRecognition.Algebra.HyperplaneReflection
import Mathlib.Analysis.InnerProductSpace.Dual

namespace OAI

/-! # A reflected direction for two distinct finite labels agreeing on a facet

The invariant Euclidean norm is pulled back from the finite orbit embedding,
only inside the proof. The height space keeps its original norm and topology.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped RealInnerProductSpace

variable {W E : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Distinct finite labels fixing the same affine facet have an outward
direction on which their images are opposite. The hypothesis here is just
agreement of their linear parts along the facet kernel. -/
theorem exists_reflected_direction_of_finite_labels_of_embedding
    (Γ : Subgroup (W ≃ₗ[ℝ] W)) [Fintype Γ]
    (e : W →ₗ[ℝ] E) (he : Function.Injective e)
    (A C : Γ) (hne : A ≠ C) (ℓ : W →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hfix : ∀ w, ℓ w = 0 → A.val w = C.val w) :
    ∃ v : W, 0 < ℓ v ∧ C.val v = -A.val v := by
  let L := finiteOrbitEmbedding Γ e
  let : NormedAddCommGroup W := NormedAddCommGroup.induced W _ L
    (finiteOrbitEmbedding_injective Γ e he)
  let : NormedSpace ℝ W := NormedSpace.induced ℝ W _ L
  let : InnerProductSpace ℝ W := InnerProductSpace.induced L
  let R : W ≃ₗᵢ[ℝ] W :=
    { (A⁻¹ * C).val with
      norm_map' := finiteOrbitEmbedding_norm Γ e (A⁻¹ * C) }
  let v := (InnerProductSpace.toDual ℝ W).symm ℓ.toContinuousLinearMap
  have hvℓ (w : W) : ⟪v, w⟫ = ℓ w :=
    InnerProductSpace.toDual_symm_apply
  have hv : v ≠ 0 := by
    intro h
    apply hℓ
    ext w
    rw [← hvℓ, h]
    simp
  have hvpos : 0 < ℓ v := by
    rw [← hvℓ]
    exact real_inner_self_pos.mpr hv
  have hrfix (w : W) (hw : ⟪w, v⟫ = 0) : R w = w := by
    have hwℓ : ℓ w = 0 := by rw [← hvℓ, real_inner_comm]; exact hw
    change A.val.symm (C.val w) = w
    rw [← hfix w hwℓ, LinearEquiv.symm_apply_apply]
  have hrne : R ≠ LinearIsometryEquiv.refl ℝ W := by
    intro h
    apply hne
    apply Subtype.ext
    ext w
    have hw := LinearIsometryEquiv.congr_fun h w
    change A.val.symm (C.val w) = w at hw
    exact (congrArg A.val hw).symm.trans (by simp)
  have hvR := orthogonal_map_fixing_hyperplane_negates_normal R v hv hrfix hrne
  refine ⟨v, hvpos, ?_⟩
  have hh := congrArg A.val hvR
  change A.val (A.val.symm (C.val v)) = A.val (-v) at hh
  simpa using hh

/-- No Euclidean structure on the height space is required: its finite
dimension supplies the auxiliary injective map used in the proof. -/
theorem exists_reflected_direction_of_finite_labels
    (Γ : Subgroup (W ≃ₗ[ℝ] W)) [Finite Γ]
    (A C : Γ) (hne : A ≠ C) (ℓ : W →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hfix : ∀ w, ℓ w = 0 → A.val w = C.val w) :
    ∃ v : W, 0 < ℓ v ∧ C.val v = -A.val v := by
  let := Fintype.ofFinite Γ
  let e : W ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ W)) :=
    (Module.finBasis ℝ W).equivFun.trans (WithLp.linearEquiv 2 ℝ _).symm
  exact exists_reflected_direction_of_finite_labels_of_embedding Γ e.toLinearMap
    e.injective A C hne ℓ hℓ hfix

end PolycyclicRecognition

end

end OAI

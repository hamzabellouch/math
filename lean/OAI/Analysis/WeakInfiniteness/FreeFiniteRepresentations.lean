import Mathlib
import OAI.Analysis.WeakInfiniteness.FreeFiniteQuotients

namespace OAI

universe u

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

open FreeGroup

variable {α : Type*} [Fintype α] [DecidableEq α]

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def freeOrbitSpace (π : FreeGroup α →* H ≃ₗᵢ[ℂ] H) (m : ℕ) (ξ : H) : Submodule ℂ H :=
  Submodule.span ℂ ((fun g => π g ξ) '' (↑(freeWordBall (α := α) m) : Set (FreeGroup α)))

instance freeOrbitSpace_finite (π : FreeGroup α →* H ≃ₗᵢ[ℂ] H) (m : ℕ) (ξ : H) :
    FiniteDimensional ℂ (freeOrbitSpace π m ξ) := by
  unfold freeOrbitSpace
  exact FiniteDimensional.span_of_finite ℂ ((freeWordBall (α := α) m).finite_toSet.image _)

lemma freeOrbitSpace_mem (π : FreeGroup α →* H ≃ₗᵢ[ℂ] H) (m : ℕ) (ξ : H)
    (g : FreeGroup α) (hg : g ∈ freeWordBall m) : π g ξ ∈ freeOrbitSpace π m ξ :=
  Submodule.subset_span ⟨g,hg,rfl⟩

lemma freeOrbitSpace_base (π : FreeGroup α →* H ≃ₗᵢ[ℂ] H) (m : ℕ) (ξ : H) :
    ξ ∈ freeOrbitSpace π m ξ := by
  simpa using freeOrbitSpace_mem π m ξ 1 (one_mem_freeWordBall m)

def extendUnitaryOn (K : Submodule ℂ H) [FiniteDimensional ℂ K] (U : H ≃ₗᵢ[ℂ] H) :
    K ≃ₗᵢ[ℂ] K := by
  let S := K.comap (U.toLinearMap.comp K.subtype)
  let L : S →ₗᵢ[ℂ] K :=
    { toLinearMap :=
        { toFun := fun x => ⟨U x.val.val, x.property⟩
          map_add' := by intro x y; apply Subtype.ext; exact U.map_add _ _
          map_smul' := by intro c x; apply Subtype.ext; exact U.map_smul _ _ }
      norm_map' := fun x => U.norm_map x.val.val }
  exact L.extend.toLinearIsometryEquiv rfl

lemma extendUnitaryOn_apply (K : Submodule ℂ H) [FiniteDimensional ℂ K]
    (U : H ≃ₗᵢ[ℂ] H) (x : K) (hx : U x.val ∈ K) :
    (extendUnitaryOn K U x).val = U x.val := by
  unfold extendUnitaryOn
  exact congrArg Subtype.val (LinearIsometry.extend_apply _ ⟨x,hx⟩)

lemma extendUnitaryOn_symm_apply (K : Submodule ℂ H) [FiniteDimensional ℂ K]
    (U : H ≃ₗᵢ[ℂ] H) (x : K) (hx : U.symm x.val ∈ K) :
    ((extendUnitaryOn K U).symm x).val = U.symm x.val := by
  let y : K := ⟨U.symm x.val, hx⟩
  have hy : extendUnitaryOn K U y = x := by
    apply Subtype.ext
    rw [extendUnitaryOn_apply, LinearIsometryEquiv.apply_symm_apply]
    simpa only [y, LinearIsometryEquiv.apply_symm_apply] using x.property
  have he := congrArg (extendUnitaryOn K U).symm hy
  simp only [LinearIsometryEquiv.symm_apply_apply] at he
  exact congrArg Subtype.val he.symm

def freeFiniteRepresentation (π : FreeGroup α →* H ≃ₗᵢ[ℂ] H) (m : ℕ) (ξ : H) :
    FreeGroup α →* freeOrbitSpace π m ξ ≃ₗᵢ[ℂ] freeOrbitSpace π m ξ :=
  FreeGroup.lift (fun a => extendUnitaryOn (freeOrbitSpace π m ξ) (π (FreeGroup.of a)))

lemma freeFiniteRepresentation_of (π : FreeGroup α →* H ≃ₗᵢ[ℂ] H) (m : ℕ) (ξ : H) (a : α) :
    freeFiniteRepresentation π m ξ (FreeGroup.of a) =
    extendUnitaryOn (freeOrbitSpace π m ξ) (π (FreeGroup.of a)) := by
  simp [freeFiniteRepresentation]

lemma freeFiniteRepresentation_word (π : FreeGroup α →* H ≃ₗᵢ[ℂ] H) (m : ℕ) (ξ : H)
    (w : List (α × Bool)) (hw : w.length ≤ m) :
    (freeFiniteRepresentation π m ξ (FreeGroup.mk w) ⟨ξ, freeOrbitSpace_base π m ξ⟩).val =
      π (FreeGroup.mk w) ξ := by
  induction w with
  | nil => simp [← FreeGroup.one_eq_mk]
  | cons x w ih =>
    have hw' : w.length ≤ m := (Nat.le_succ w.length).trans hw
    have ih' := ih hw'
    have hmem : π (FreeGroup.mk (x :: w)) ξ ∈ freeOrbitSpace π m ξ :=
      freeOrbitSpace_mem π m ξ _ ((mem_freeWordBall _ _).mpr (FreeGroup.norm_mk_le.trans hw))
    rcases x with ⟨a,b⟩
    cases b
    · rw [free_mk_cons_neg] at hmem ⊢
      simp only [_root_.map_mul, _root_.map_inv, freeFiniteRepresentation_of,
        LinearIsometryEquiv.coe_mul, Function.comp_apply, LinearIsometryEquiv.coe_inv] at hmem ⊢
      rw [extendUnitaryOn_symm_apply, ih']
      simpa only [ih'] using hmem
    · rw [free_mk_cons_pos] at hmem ⊢
      simp only [_root_.map_mul, freeFiniteRepresentation_of,
        LinearIsometryEquiv.coe_mul, Function.comp_apply] at hmem ⊢
      rw [extendUnitaryOn_apply, ih']
      simpa only [ih'] using hmem

lemma freeFiniteRepresentation_ball (π : FreeGroup α →* H ≃ₗᵢ[ℂ] H) (m : ℕ) (ξ : H)
    (g : FreeGroup α) (hg : g ∈ freeWordBall m) :
    (freeFiniteRepresentation π m ξ g ⟨ξ, freeOrbitSpace_base π m ξ⟩).val = π g ξ := by
  simpa only [FreeGroup.mk_toWord] using
    freeFiniteRepresentation_word π m ξ g.toWord ((mem_freeWordBall g m).mp hg)

lemma norm_freePolynomial_le_of_finite_tests (c : FreeGroup α →₀ ℂ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      [FiniteDimensional ℂ V] (ρ : FreeGroup α →* V ≃ₗᵢ[ℂ] V),
      ‖c.sum (fun g a => a • (ρ g : V →L[ℂ] V))‖ ≤ C)
    (π : FreeGroup α →* H ≃ₗᵢ[ℂ] H) :
    ‖c.sum (fun g a => a • (π g : H →L[ℂ] H))‖ ≤ C := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro ξ
  let m := c.support.sup FreeGroup.norm
  let K := freeOrbitSpace π m ξ
  let η : K := ⟨ξ, freeOrbitSpace_base π m ξ⟩
  let ρ := freeFiniteRepresentation π m ξ
  have he : (c.sum (fun g a => a • (ρ g : K →L[ℂ] K)) η).val =
      c.sum (fun g a => a • (π g : H →L[ℂ] H)) ξ := by
    simp only [Finsupp.sum, sum_apply, smul_apply,
      Submodule.coe_sum, Submodule.coe_smul_of_tower]
    apply Finset.sum_congr rfl
    intro g hg
    exact congrArg (fun x : H => c g • x)
      (freeFiniteRepresentation_ball π m ξ g ((mem_freeWordBall _ _).mpr (Finset.le_sup hg)))
  rw [← he]
  exact (ContinuousLinearMap.le_opNorm _ η).trans
    (mul_le_mul_of_nonneg_right (h K ρ) (norm_nonneg η))

end WeakPureInfiniteness
end

end OAI

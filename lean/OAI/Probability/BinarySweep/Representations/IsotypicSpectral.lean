import Mathlib
import OAI.Probability.BinarySweep.Representations.MultiplicityBound
import OAI.Probability.BinarySweep.MatrixBounds.PositiveTraceRestriction

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W)

omit [Fintype G] [FiniteDimensional ℂ W] in
lemma commuting_eigenspace_map (T : Module.End ℂ W)
    (hT : ∀ g w, T (σ g w) = σ g (T w)) (μ : ℂ) (g : G) :
    (T.eigenspace μ).map (σ g) = T.eigenspace μ := by
  apply le_antisymm
  · rintro w ⟨v,hv,rfl⟩
    apply Module.End.mem_eigenspace_iff.mpr
    rw [hT,Module.End.mem_eigenspace_iff.mp hv,map_smul]
  · intro w hw
    refine ⟨σ g⁻¹ w, ?_, ?_⟩
    · apply Module.End.mem_eigenspace_iff.mpr
      rw [hT,Module.End.mem_eigenspace_iff.mp hw,map_smul]
    · rw [← Module.End.mul_apply,← map_mul,mul_inv_cancel,map_one,Module.End.one_apply]

def eigenspaceProjectionIntertwiner (T : Module.End ℂ W)
    (hT : ∀ g w, T (σ g w) = σ g (T w))
    (hσ : ∀ g w, ‖σ g w‖ = ‖w‖) (μ : ℂ) : IntertwiningMap σ σ where
  toLinearMap := (T.eigenspace μ).starProjection.toLinearMap
  isIntertwining' g := by
    ext w
    change (T.eigenspace μ).starProjection (σ g w) = σ g ((T.eigenspace μ).starProjection w)
    let U : W →ₗᵢ[ℂ] W := {toLinearMap := σ g, norm_map' := hσ g}
    have he := U.map_starProjection (T.eigenspace μ) w
    change σ g ((T.eigenspace μ).starProjection w) =
      ((T.eigenspace μ).map (σ g)).starProjection (σ g w) at he
    simpa only [commuting_eigenspace_map σ T hT μ g] using he.symm

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma eigenvalue_multiplicity_ge [ρ.IsIrreducible] (T : Module.End ℂ W)
    (hT : ∀ g w, T (σ g w) = σ g (T w))
    (hσ : ∀ g w, ‖σ g w‖ = ‖w‖) (μ : ℂ)
    {w : W} (hw : w ∈ isotypicSpan ρ σ) (he : T w = μ • w) (hn : w ≠ 0) :
    Module.finrank ℂ V ≤ Module.finrank ℂ (T.eigenspace μ) := by
  let P := eigenspaceProjectionIntertwiner σ T hT hσ μ
  have hP : ∃ f : IntertwiningMap ρ σ, P.comp f ≠ 0 := by
    by_contra! hall
    have hz : P w = 0 := by
      change w ∈ ⨆ f : IntertwiningMap ρ σ, LinearMap.range f.toLinearMap at hw
      refine Submodule.iSup_induction _ (motive := fun x => P x = 0) hw ?_ (map_zero P) ?_
      · intro f x hx
        obtain ⟨v,rfl⟩ := hx
        exact DFunLike.congr_fun (hall f) v
      · intro x y hx hy
        rw [map_add,hx,hy,zero_add]
    have hpw : P w = w := Submodule.starProjection_eq_self_iff.mpr
      (Module.End.mem_eigenspace_iff.mpr he)
    exact hn (hpw.symm.trans hz)
  obtain ⟨f,hf⟩ := hP
  have hi := (IsIrreducible.injective_or_eq_zero (P.comp f)).resolve_right hf
  let Q : V →ₗ[ℂ] T.eigenspace μ := (P.comp f).toLinearMap.codRestrict _
    (fun v => (T.eigenspace μ).starProjection_apply_mem (f v))
  apply LinearMap.finrank_le_finrank_of_injective (f:=Q)
  intro v v' hv
  exact hi (congrArg Subtype.val hv)

omit [Fintype G] [FiniteDimensional ℂ V] in
theorem isotypic_eigenvalue_trace_le [ρ.IsIrreducible] (T : Module.End ℂ W)
    (hpos : T.IsPositive) (hT : ∀ g w, T (σ g w) = σ g (T w))
    (hσ : ∀ g w, ‖σ g w‖ = ‖w‖) {μ : ℝ} (hμ : 0 ≤ μ)
    {w : W} (hw : w ∈ isotypicSpan ρ σ) (he : T w = (μ:ℂ) • w) (hn : w ≠ 0) :
    (Module.finrank ℂ V : ℝ) * μ ≤ (LinearMap.trace ℂ W T).re := by
  let E := T.eigenspace (μ:ℂ)
  have hE : ∀ x ∈ E, T x ∈ E := by
    intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [hx,map_smul,hx]
  have hr : T.restrict hE = (μ:ℂ) • (LinearMap.id : E →ₗ[ℂ] E) := by
    ext x
    exact Module.End.mem_eigenspace_iff.mp x.property
  have ht := positive_trace_restrict_le E T hpos hE
  rw [hr,map_smul,LinearMap.trace_id] at ht
  have hd := eigenvalue_multiplicity_ge ρ σ T hT hσ (μ:ℂ) hw he hn
  have hd' : (Module.finrank ℂ V : ℝ) ≤ (Module.finrank ℂ E : ℝ) := by exact_mod_cast hd
  have ht' : μ * (Module.finrank ℂ E : ℝ) ≤ (LinearMap.trace ℂ W T).re := by
    simpa using ht
  nlinarith

end BinaryCoordinateSweeps.Irrep

end

open scoped BigOperators Classical ComplexOrder

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W)

def commutingIntertwiner (T : Module.End ℂ W)
    (hT : ∀ g w, T (σ g w) = σ g (T w)) : IntertwiningMap σ σ where
  toLinearMap := T
  isIntertwining' g := by ext w; exact hT g w

omit [Fintype G] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
lemma commuting_isotypic_invariant (T : Module.End ℂ W)
    (hT : ∀ g w, T (σ g w) = σ g (T w)) :
    ∀ w ∈ isotypicSpan ρ σ, T w ∈ isotypicSpan ρ σ := by
  intro w hw
  apply Submodule.iSup_induction (fun f : IntertwiningMap ρ σ => LinearMap.range f.toLinearMap)
    (motive := fun w => T w ∈ isotypicSpan ρ σ) hw
  · intro f w hw
    obtain ⟨v,rfl⟩ := hw
    let F := (commutingIntertwiner σ T hT).comp f
    exact (le_iSup (fun f : IntertwiningMap ρ σ => LinearMap.range f.toLinearMap) F) ⟨v,rfl⟩
  · simp
  · intro x y hx hy
    simpa only [map_add] using Submodule.add_mem _ hx hy

omit [Fintype G] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
lemma isotypic_restrict_positive (T : Module.End ℂ W) (hpos : T.IsPositive)
    (hT : ∀ g w, T (σ g w) = σ g (T w)) :
    (T.restrict (commuting_isotypic_invariant ρ σ T hT)).IsPositive :=
  ⟨hpos.isSymmetric.restrict_invariant _, fun x => hpos.2 x.val⟩

omit [Fintype G] [FiniteDimensional ℂ V] in
theorem isotypic_restriction_cap [ρ.IsIrreducible] (T : Module.End ℂ W)
    (hpos : T.IsPositive) (hT : ∀ g w, T (σ g w) = σ g (T w))
    (hσ : ∀ g w, ‖σ g w‖ = ‖w‖) :
    (((LinearMap.trace ℂ W T).re : ℂ) • (LinearMap.id : isotypicSpan ρ σ →ₗ[ℂ] isotypicSpan ρ σ) -
      (Module.finrank ℂ V : ℂ) • T.restrict (commuting_isotypic_invariant ρ σ T hT)).IsPositive := by
  let S := isotypicSpan ρ σ
  let R := T.restrict (commuting_isotypic_invariant ρ σ T hT)
  have hR : R.IsPositive := isotypic_restrict_positive ρ σ T hpos hT
  let b := hR.isSymmetric.eigenvectorBasis rfl
  apply (LinearMap.posSemidef_toMatrix_iff b).mp
  rw [map_sub,map_smul,map_smul,LinearMap.toMatrix_id]
  rw [show LinearMap.toMatrix b.toBasis b.toBasis R =
    Matrix.diagonal (fun i => (hR.isSymmetric.eigenvalues rfl i : ℂ)) from
      hR.isSymmetric.toMatrix_eigenvectorBasis rfl]
  rw [← Matrix.diagonal_one,← Matrix.diagonal_smul,← Matrix.diagonal_smul,Matrix.diagonal_sub]
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  have hi := isotypic_eigenvalue_trace_le ρ σ T hpos hT hσ
    (hR.nonneg_eigenvalues rfl i) (b i).property
    (congrArg Subtype.val (hR.isSymmetric.apply_eigenvectorBasis rfl i))
    (fun hz => (hR.isSymmetric.hasEigenvector_eigenvectorBasis rfl i).2 (Subtype.ext hz))
  change 0 ≤ ((LinearMap.trace ℂ W T).re : ℂ)*1 - _
  have he : (0:ℂ) ≤ (((LinearMap.trace ℂ W T).re -
      (Module.finrank ℂ V : ℝ)*hR.isSymmetric.eigenvalues rfl i : ℝ):ℂ) := by
    exact_mod_cast sub_nonneg.mpr hi
  simpa using he

end BinaryCoordinateSweeps.Irrep

end

end OAI

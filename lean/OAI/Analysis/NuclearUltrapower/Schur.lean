import OAI.Analysis.NuclearUltrapower.FiniteRepresentations
import OAI.Analysis.NuclearUltrapower.HilbertSchmidt

namespace OAI

section
universe u v w
noncomputable section
open scoped TensorProduct InnerProductSpace
open Module.End
noncomputable section
open scoped CStarAlgebra
noncomputable section
open Filter
open scoped Topology ENNReal
noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower
namespace FiniteUnitaryRep
open Module.End
variable {Γ : Type u} [Group Γ]

/-- Schur's scalar lemma, proved from an actual eigenvalue over C. -/
theorem scalar_of_commuting {π : FiniteUnitaryRep.{u,v} Γ} (hπ : π.Irreducible)
    (T : π →ₗ[ℂ] π) (hT : ∀ g x, T (π.action g x) = π.action g (T x)) :
    ∃ c : ℂ, T = c • LinearMap.id := by
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  have hi : ∀ g x, x ∈ eigenspace T c → π.action g x ∈ eigenspace T c := by
    intro g x hx
    rw [mem_eigenspace_iff] at hx ⊢
    rw [hT, hx, map_smul]
  rcases hπ _ hi with hz | ht
  · exact False.elim ((Module.End.hasEigenvalue_iff.mp hc) hz)
  · refine ⟨c, ?_⟩
    ext x
    exact (mem_eigenspace_iff.mp (show x ∈ eigenspace T c by rw [ht]; trivial))

/-- Every nonzero intertwiner out of an irreducible finite-dimensional unitary
representation is a positive scalar multiple of an isometry. The target can
be any Hilbert space, not necessarily separable or finite-dimensional. -/
theorem isometry_of_intertwiner {π : FiniteUnitaryRep.{u,v} Γ} (hπ : π.Irreducible)
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (σ : Γ →* (K ≃ₗᵢ[ℂ] K)) (T : π →L[ℂ] K) (hT0 : T ≠ 0)
    (hT : ∀ g x, T (π.action g x) = σ g (T x)) :
    ∃ U : π →ₗᵢ[ℂ] K, ∀ g x, U (π.action g x) = σ g (U x) := by
  have hcomm (g : Γ) (y : π) :
      T.adjoint (T (π.action g y)) = π.action g (T.adjoint (T y)) := by
    apply ext_inner_left ℂ
    intro z
    obtain ⟨x, rfl⟩ := (π.action g).surjective z
    rw [ContinuousLinearMap.adjoint_inner_right, hT, hT,
      (σ g).inner_map_map, (π.action g).inner_map_map,
      ContinuousLinearMap.adjoint_inner_right]
  obtain ⟨c, hc⟩ := scalar_of_commuting hπ (T.adjoint.comp T).toLinearMap hcomm
  have hn (x : π) : ‖T x‖ ^ 2 = RCLike.re c * ‖x‖ ^ 2 := by
    have he := congrArg (fun L : π →ₗ[ℂ] π => RCLike.re (Inner.inner ℂ x (L x))) hc
    change RCLike.re (Inner.inner ℂ x (T.adjoint (T x))) =
      RCLike.re (Inner.inner ℂ x (c • x)) at he
    simpa only [ContinuousLinearMap.adjoint_inner_right, inner_smul_right,
      RCLike.mul_re, inner_self_eq_norm_sq, inner_self_im, mul_zero, sub_zero] using he
  have hex : ∃ x : π, T x ≠ 0 := by
    by_contra! h
    exact hT0 (ContinuousLinearMap.ext fun x => h x)
  obtain ⟨x, hx⟩ := hex
  have hcpos : 0 < RCLike.re c := by
    have hh := hn x
    have hhpos : 0 < ‖T x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
    nlinarith [sq_nonneg ‖x‖]
  let r : ℝ := Real.sqrt (RCLike.re c)
  have hr : 0 < r := Real.sqrt_pos.mpr hcpos
  have hnorm (x : π) : ‖T x‖ = r * ‖x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hr.le (norm_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt hcpos.le]
    exact hn x
  let U : π →ₗᵢ[ℂ] K := {
    toLinearMap := (↑r⁻¹ : ℂ) • T.toLinearMap
    norm_map' x := by
      change ‖(↑r⁻¹ : ℂ) • T x‖ = ‖x‖
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), hnorm]
      rw [← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul] }
  refine ⟨U, fun g x => ?_⟩
  change (↑r⁻¹ : ℂ) • T (π.action g x) = σ g ((↑r⁻¹ : ℂ) • T x)
  rw [hT, map_smul]

/-- The unitary form of Schur's lemma used by the coordinate-quotient argument. -/
theorem equivalent_of_nonzero_intertwiner {π τ : FiniteUnitaryRep.{u,v} Γ}
    (hπ : π.Irreducible) (hτ : τ.Irreducible) (T : π →L[ℂ] τ) (hT0 : T ≠ 0)
    (hT : ∀ g x, T (π.action g x) = τ.action g (T x)) : π.Equivalent τ :=
  Embeds.equivalent_of_irreducible (isometry_of_intertwiner hπ τ.action T hT0 hT) hτ

end FiniteUnitaryRep

open scoped TensorProduct
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable {Γ : Type u} [Group Γ]

section MixedTensor
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The finite-rank operator represented by a rectangular Hilbert tensor. -/
def mixedTensorOperator : E ⊗[ℂ] StrongDual ℂ F →ₗ[ℂ] (F →L[ℂ] E) :=
  TensorProduct.lift
    { toFun := fun x =>
        { toFun := fun f => f.smulRight x
          map_add' := by intro f g; ext v; simp [add_smul]
          map_smul' := by intro c f; ext v; simp [mul_smul] }
      map_add' := by intro x y; ext f v; simp [smul_add]
      map_smul' := by intro c x; ext f v; simp [smul_smul, mul_comm] }

omit [CompleteSpace F] in
@[simp] theorem mixedTensorOperator_tmul (x : E) (f : StrongDual ℂ F) (v : F) :
    mixedTensorOperator (x ⊗ₜ[ℂ] f) v = f v • x := rfl

/-- All matrix coefficients, using Lean's second-variable-linear inner product. -/
theorem mixedTensorOperator_inner (z : E ⊗[ℂ] StrongDual ℂ F) (v : F) (y : E) :
    ⟪y, mixedTensorOperator z v⟫_ℂ = ⟪y ⊗ₜ[ℂ] InnerProductSpace.toDual ℂ F v, z⟫_ℂ := by
  induction z using TensorProduct.inductionOn with
  | tmul x f => simp [mul_comm]
  | add z w hz hw =>
      simp only [map_add, add_apply, inner_add_right, hz, hw]
      simp [TensorProduct.inner_def]

theorem mixedTensorOperator_injective : Function.Injective (mixedTensorOperator (E := E) (F := F)) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  change mixedTensorOperator z = 0 at hz
  have hp (x : E) (f : StrongDual ℂ F) : ⟪x ⊗ₜ[ℂ] f, z⟫_ℂ = 0 := by
    obtain ⟨v, rfl⟩ := (InnerProductSpace.toDual ℂ F).surjective f
    rw [← mixedTensorOperator_inner, hz, zero_apply, inner_zero_right]
  have ha (w : E ⊗[ℂ] StrongDual ℂ F) : ⟪w, z⟫_ℂ = 0 := by
    induction w using TensorProduct.inductionOn with
    | tmul x f => exact hp x f
    | add x y hx hy => rw [inner_add_left (𝕜 := ℂ) (E := E ⊗[ℂ] StrongDual ℂ F), hx, hy, add_zero]
  exact (inner_self_eq_zero (𝕜 := ℂ) (E := E ⊗[ℂ] StrongDual ℂ F)).mp (ha z)

/-- Tensor invariance is the genuine intertwining equation. -/
theorem mixedTensorOperator_action (u : E ≃ₗᵢ[ℂ] E) (v : F ≃ₗᵢ[ℂ] F)
    (z : E ⊗[ℂ] StrongDual ℂ F) :
    mixedTensorOperator (TensorProduct.congrIsometry u (dualUnitary v) z) =
      (u : E →L[ℂ] E).comp ((mixedTensorOperator z).comp (v.symm : F →L[ℂ] F)) := by
  induction z using TensorProduct.inductionOn with
  | tmul x f => ext y; simp
  | add x y hx hy => simp only [map_add, hx, hy, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]

def tensorContragredientRep (ρ : Γ →* (E ≃ₗᵢ[ℂ] E)) (π : Γ →* (F ≃ₗᵢ[ℂ] F)) :
    Γ →* (E ⊗[ℂ] StrongDual ℂ F ≃ₗᵢ[ℂ] E ⊗[ℂ] StrongDual ℂ F) where
  toFun g := TensorProduct.congrIsometry (ρ g) (dualUnitary (π g))
  map_one' := by
    ext z
    induction z using TensorProduct.inductionOn with
    | tmul x f =>
      apply mixedTensorOperator_injective
      ext y
      simp
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  map_mul' g h := by
    ext z
    induction z using TensorProduct.inductionOn with
    | tmul x f =>
      apply mixedTensorOperator_injective
      ext y
      simp
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]

/-- The invariant tensor defines an actual bounded intertwiner. -/
theorem invariant_tensor_intertwines
    (ρ : Γ →* (E ≃ₗᵢ[ℂ] E)) (π : Γ →* (F ≃ₗᵢ[ℂ] F))
    (z : E ⊗[ℂ] StrongDual ℂ F)
    (hz : ∀ g, tensorContragredientRep ρ π g z = z) (g : Γ) (x : F) :
    mixedTensorOperator z (π g x) = ρ g (mixedTensorOperator z x) := by
  have he := congrArg (fun w => mixedTensorOperator w (π g x)) (hz g)
  change mixedTensorOperator (TensorProduct.congrIsometry (ρ g) (dualUnitary (π g)) z) (π g x) = _ at he
  rw [mixedTensorOperator_action] at he
  simpa using he.symm

end MixedTensor

/-- Schur exclusion at each nonexceptional coordinate. -/
theorem tensor_no_invariants_of_inequivalent
    {π τ : FiniteUnitaryRep.{u,v} Γ} (hπ : π.Irreducible) (hτ : τ.Irreducible)
    (hne : ¬ τ.Equivalent π) (z : π ⊗[ℂ] StrongDual ℂ τ)
    (hz : ∀ g, tensorContragredientRep π.action τ.action g z = z) : z = 0 := by
  by_contra h0
  have hT : mixedTensorOperator z ≠ 0 := by
    intro h
    apply h0
    exact mixedTensorOperator_injective (by simpa using h)
  exact hne (FiniteUnitaryRep.equivalent_of_nonzero_intertwiner hτ hπ
    (mixedTensorOperator z) hT (invariant_tensor_intertwines π.action τ.action z hz))

end NuclearUltrapower

namespace NuclearUltrapower
open scoped TensorProduct
section TensorSurjective
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [CompleteSpace F]

/-- Every operator with finite-dimensional domain is represented by an actual
algebraic tensor; no completed-tensor compactness argument is hidden here. -/
theorem mixedTensorOperator_surjective :
    Function.Surjective (mixedTensorOperator (E := E) (F := F)) := by
  intro T
  let b := stdOrthonormalBasis ℂ F
  refine ⟨∑ i, T (b i) ⊗ₜ[ℂ] InnerProductSpace.toDual ℂ F (b i), ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  simp only [map_sum, sum_apply, mixedTensorOperator_tmul]
  change (∑ i, inner ℂ (b i) x • T (b i)) = T x
  calc
    _ = T (∑ i, inner ℂ (b i) x • b i) := by simp only [map_sum, map_smul]
    _ = T x := congrArg T (b.sum_repr' x)

/-- A nonzero finite-dimensional intertwiner gives a nonzero invariant tensor. -/
theorem exists_invariant_tensor_of_intertwiner {Γ : Type*} [Group Γ]
    (ρ : Γ →* (E ≃ₗᵢ[ℂ] E)) (π : Γ →* (F ≃ₗᵢ[ℂ] F))
    (T : F →L[ℂ] E) (hT : T ≠ 0)
    (hcomm : ∀ g x, T (π g x) = ρ g (T x)) :
    ∃ z : E ⊗[ℂ] StrongDual ℂ F, z ≠ 0 ∧
      ∀ g, tensorContragredientRep ρ π g z = z := by
  obtain ⟨z, hz⟩ := mixedTensorOperator_surjective (E := E) T
  refine ⟨z, ?_, ?_⟩
  · intro h0
    apply hT
    simpa only [h0, map_zero] using hz.symm
  · intro g
    apply mixedTensorOperator_injective
    change mixedTensorOperator (TensorProduct.congrIsometry (ρ g) (dualUnitary (π g)) z) = _
    rw [mixedTensorOperator_action, hz]
    apply ContinuousLinearMap.ext
    intro x
    change ρ g (T ((π g).symm x)) = T x
    rw [← hcomm, (π g).apply_symm_apply]
end TensorSurjective

section FiniteSubspace
variable {Γ : Type u} [Group Γ]
  {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (σ : Γ →* (K ≃ₗᵢ[ℂ] K))
  (W : Submodule ℂ K) [Nontrivial W] [FiniteDimensional ℂ W]
  (hW : ∀ g x, x ∈ W → σ g x ∈ W)

/-- The honest finite-dimensional subrepresentation on an invariant subspace. -/
def finiteSubspaceRep : FiniteUnitaryRep.{u,v} Γ where
  carrier := W
  action := {
    toFun g := {
      toFun x := ⟨σ g x, hW g x x.property⟩
      invFun x := ⟨σ g⁻¹ x, hW g⁻¹ x x.property⟩
      left_inv x := by ext; change (σ g⁻¹ * σ g) x.val = x.val; rw [← map_mul]; simp
      right_inv x := by ext; change (σ g * σ g⁻¹) x.val = x.val; rw [← map_mul]; simp
      map_add' x y := by ext; simp
      map_smul' c x := by ext; simp
      norm_map' x := (σ g).norm_map x }
    map_one' := by ext; simp
    map_mul' g h := by ext; simp [map_mul] }

include W hW in
/-- Every nonzero finite subrepresentation contains an irreducible one, with
an explicit isometric intertwiner into the original ambient Hilbert space. -/
theorem finiteSubspace_exists_irreducible :
    ∃ τ : FiniteUnitaryRep.{u,v} Γ, τ.Irreducible ∧
      ∃ T : τ →ₗᵢ[ℂ] K, ∀ g x, T (τ.action g x) = σ g (T x) := by
  obtain ⟨τ, hτ, T, hT⟩ := (finiteSubspaceRep σ W hW).exists_irreducible
  refine ⟨τ, hτ, W.subtypeₗᵢ.comp T, ?_⟩
  intro g x
  exact congrArg (fun y : W => (y : K)) (hT g x)
end FiniteSubspace
end NuclearUltrapower

end
end
end
end
end

end OAI

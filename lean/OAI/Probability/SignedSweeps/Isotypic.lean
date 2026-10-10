import OAI.Probability.SignedSweeps.TensorCommutant

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {G E F : Type*} [Monoid G] [AddCommGroup E] [Module ℂ E]
  [AddCommGroup F] [Module ℂ F]

def isotypicSubrepresentation (ρ : Representation ℂ G E) (σ : Representation ℂ G F) :
    Subrepresentation σ where
  toSubmodule := ⨆ f : Representation.IntertwiningMap ρ σ, f.toLinearMap.range
  apply_mem_toSubmodule g x hx := by
    refine Submodule.iSup_induction (motive := fun x => σ g x ∈
      ⨆ f : Representation.IntertwiningMap ρ σ, f.toLinearMap.range)
      (fun f : Representation.IntertwiningMap ρ σ => f.toLinearMap.range) hx ?_ ?_ ?_
    · intro f y hy
      obtain ⟨v, rfl⟩ := hy
      exact (le_iSup (fun f : Representation.IntertwiningMap ρ σ => f.toLinearMap.range) f)
        ⟨ρ g v, Representation.IntertwiningMap.isIntertwining ρ σ f g v⟩
    · simp
    · intro x y hx hy
      simpa only [map_add] using Submodule.add_mem _ hx hy

lemma intertwiner_mem_isotypic (ρ : Representation ℂ G E) (σ : Representation ℂ G F)
    (f : Representation.IntertwiningMap ρ σ) (x : E) :
    f x ∈ (isotypicSubrepresentation ρ σ).toSubmodule :=
  (le_iSup (fun f : Representation.IntertwiningMap ρ σ => f.toLinearMap.range) f) ⟨x, rfl⟩

lemma isotypic_end_stable (ρ : Representation ℂ G E) (σ : Representation ℂ G F)
    (T : Representation.IntertwiningMap σ σ) {x : F}
    (hx : x ∈ (isotypicSubrepresentation ρ σ).toSubmodule) :
    T x ∈ (isotypicSubrepresentation ρ σ).toSubmodule := by
  refine Submodule.iSup_induction (motive := fun x =>
    T x ∈ (isotypicSubrepresentation ρ σ).toSubmodule)
    (fun f : Representation.IntertwiningMap ρ σ => f.toLinearMap.range) hx ?_ ?_ ?_
  · intro f y hy
    obtain ⟨v, rfl⟩ := hy
    exact intertwiner_mem_isotypic ρ σ (T.comp f) v
  · simp
  · intro x y hx hy
    simpa only [map_add] using Submodule.add_mem _ hx hy

def isotypicEvaluation (ρ : Representation ℂ G E) (σ : Representation ℂ G F) :
    E ⊗[ℂ] Representation.IntertwiningMap ρ σ →ₗ[ℂ] F :=
  TensorProduct.lift {
    toFun x := {
      toFun f := f x
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    map_add' := by intro x y; ext f; exact f.map_add x y
    map_smul' := by intro c x; ext f; exact f.map_smul c x }

@[simp] lemma isotypicEvaluation_tmul (ρ : Representation ℂ G E) (σ : Representation ℂ G F)
    (x : E) (f : Representation.IntertwiningMap ρ σ) :
    isotypicEvaluation ρ σ (x ⊗ₜ[ℂ] f) = f x := rfl

lemma isotypicEvaluation_range (ρ : Representation ℂ G E) (σ : Representation ℂ G F) :
    (isotypicEvaluation ρ σ).range = (isotypicSubrepresentation ρ σ).toSubmodule := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.inductionOn with
    | tmul x f => exact intertwiner_mem_isotypic ρ σ f x
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  · apply iSup_le
    intro f y hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x ⊗ₜ[ℂ] f, rfl⟩

lemma isotypic_finrank_le (ρ : Representation ℂ G E) (σ : Representation ℂ G F)
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] :
    finrank ℂ (isotypicSubrepresentation ρ σ).toSubmodule ≤
      finrank ℂ E * finrank ℂ (Representation.IntertwiningMap ρ σ) := by
  rw [← isotypicEvaluation_range, ← Module.finrank_tensorProduct]
  exact LinearMap.finrank_range_le _

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {G E F : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]
variable (ρ : Representation ℂ G E) (σ : Representation ℂ G F)
  (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (hσ : ∀ g x, ‖σ g x‖ = ‖x‖)

def adjointIntertwiner (f : Representation.IntertwiningMap ρ σ) :
    Representation.IntertwiningMap σ ρ :=
  f.toLinearMap.adjoint.intertwiningMap_of_isIntertwiningMap σ ρ (by
    intro g x
    have he : f.toLinearMap ∘ₗ ρ g⁻¹ = σ g⁻¹ ∘ₗ f.toLinearMap := by
      ext y; exact Representation.IntertwiningMap.isIntertwining ρ σ f g⁻¹ y
    have ha := congrArg LinearMap.adjoint he
    simp only [LinearMap.adjoint_comp, unitary_representation_adjoint ρ hρ,
      unitary_representation_adjoint σ hσ, inv_inv] at ha
    exact congrArg (fun T : F →ₗ[ℂ] E => T x) ha.symm)

@[simp] lemma adjointIntertwiner_linearMap (f : Representation.IntertwiningMap ρ σ) :
    (adjointIntertwiner ρ σ hρ hσ f).toLinearMap = f.toLinearMap.adjoint := rfl

lemma submodule_projection_commute (S : Submodule ℂ F) (T : F →ₗ[ℂ] F)
    (hT : ∀ x ∈ S, T x ∈ S) (hT' : ∀ x ∈ S, T.adjoint x ∈ S) :
    S.starProjection.toLinearMap * T = T * S.starProjection.toLinearMap := by
  apply LinearMap.ext
  intro x
  change S.starProjection (T x) = T (S.starProjection x)
  apply S.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hT _ (S.starProjection_apply_mem x)
  · intro w hw
    change inner ℂ (T x - T (S.starProjection x)) w = 0
    rw [← map_sub, ← LinearMap.adjoint_inner_right]
    exact S.starProjection_inner_eq_zero x _ (hT' w hw)

include hσ in
omit [FiniteDimensional ℂ E] in

lemma isotypic_projection_commute [FiniteDimensional ℂ E]
    (T : Representation.IntertwiningMap σ σ) :
    (isotypicSubrepresentation ρ σ).toSubmodule.starProjection.toLinearMap * T.toLinearMap =
      T.toLinearMap * (isotypicSubrepresentation ρ σ).toSubmodule.starProjection.toLinearMap := by
  apply submodule_projection_commute
  · exact fun x hx => isotypic_end_stable ρ σ T hx
  · exact fun x hx => isotypic_end_stable ρ σ (adjointIntertwiner σ σ hσ hσ T) hx

include hρ hσ in

theorem intertwiner_isometric_scaling [ρ.IsIrreducible] [Nontrivial E]
    (f : Representation.IntertwiningMap ρ σ) (hf : f ≠ 0) :
    ∃ j : Representation.IntertwiningMap ρ σ, (∃ c : ℂ, j = c • f) ∧
      ∀ x, ‖j x‖ = ‖x‖ := by
  let A := (adjointIntertwiner ρ σ hρ hσ f).comp f
  obtain ⟨z, hz⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective A
  have he (x : E) : f.toLinearMap.adjoint (f x) = z • x :=
    congrArg (fun T : Representation.IntertwiningMap ρ ρ => T x) hz.symm
  have hnorm (x : E) : ‖f x‖ ^ 2 = z.re * ‖x‖ ^ 2 := by
    have hi := congrArg Complex.re (LinearMap.adjoint_inner_right f.toLinearMap x (f x))
    rw [he] at hi
    change (inner ℂ x (z • x)).re = (inner ℂ (f x) (f x)).re at hi
    simpa only [inner_smul_right, inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
      ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero] using hi.symm
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : E)
  have hinj := (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  have hfx : f x₀ ≠ 0 := fun h => hx₀ (hinj (h.trans f.map_zero.symm))
  have hzpos : 0 < z.re := by
    have hp : 0 < ‖f x₀‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hfx)
    rw [hnorm] at hp
    exact (mul_pos_iff.mp hp).resolve_right (fun h => (not_lt_of_ge (sq_nonneg ‖x₀‖)) h.2) |>.1
  refine ⟨(Real.sqrt z.re : ℂ)⁻¹ • f, ⟨_, rfl⟩, fun x => ?_⟩
  change ‖(Real.sqrt z.re : ℂ)⁻¹ • f x‖ = ‖x‖
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have hs : 0 < Real.sqrt z.re := Real.sqrt_pos.mpr hzpos
  have hx := hnorm x
  have hsq := Real.sq_sqrt hzpos.le
  apply (sq_eq_sq₀ (mul_nonneg (inv_nonneg.mpr hs.le) (norm_nonneg _)) (norm_nonneg _)).mp
  rw [mul_pow, inv_pow, hsq, hx, ← mul_assoc, inv_mul_cancel₀ hzpos.ne', one_mul]

include hρ hσ in

theorem intertwiner_isometric_normalization [ρ.IsIrreducible] [Nontrivial E]
    (f : Representation.IntertwiningMap ρ σ) (hf : f ≠ 0) :
    ∃ j : Representation.IntertwiningMap ρ σ, ∀ x, ‖j x‖ = ‖x‖ := by
  obtain ⟨j, _, hj⟩ := intertwiner_isometric_scaling ρ σ hρ hσ f hf
  exact ⟨j, hj⟩

lemma adjoint_isometric_intertwiner (j : Representation.IntertwiningMap ρ σ)
    (hj : ∀ x, ‖j x‖ = ‖x‖) (x : E) : j.toLinearMap.adjoint (j x) = x := by
  let J : E →ₗᵢ[ℂ] F := ⟨j.toLinearMap, hj⟩
  apply ext_inner_left ℂ
  intro y
  rw [LinearMap.adjoint_inner_right]
  exact J.inner_map_map y x

include hρ hσ in

lemma multiplicity_le_commutant (j : Representation.IntertwiningMap ρ σ)
    (hj : ∀ x, ‖j x‖ = ‖x‖) :
    finrank ℂ (Representation.IntertwiningMap ρ σ) ≤
      finrank ℂ (Representation.IntertwiningMap σ σ) := by
  let r := adjointIntertwiner ρ σ hρ hσ j
  let L : Representation.IntertwiningMap ρ σ →ₗ[ℂ]
      Representation.IntertwiningMap σ σ := {
    toFun f := f.comp r
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  apply LinearMap.finrank_le_finrank_of_injective (f := L)
  intro f g hfg
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  have hc := congrArg (fun T : Representation.IntertwiningMap σ σ => T (j x)) hfg
  change f (j.toLinearMap.adjoint (j x)) = g (j.toLinearMap.adjoint (j x)) at hc
  rw [adjoint_isometric_intertwiner ρ σ j hj] at hc
  exact hc

include hρ hσ in

theorem central_scalar_on_isotypic [ρ.IsIrreducible]
    (j : Representation.IntertwiningMap ρ σ) (hj : ∀ x, ‖j x‖ = ‖x‖)
    (A : Representation.IntertwiningMap σ σ)
    (hA : ∀ T : Representation.IntertwiningMap σ σ, A.comp T = T.comp A) :
    ∃ z : ℂ, ∀ x ∈ (isotypicSubrepresentation ρ σ).toSubmodule, A x = z • x := by
  let r := adjointIntertwiner ρ σ hρ hσ j
  have hr (x : E) : r (j x) = x := adjoint_isometric_intertwiner ρ σ j hj x
  obtain ⟨z, hz⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective (r.comp (A.comp j))
  have hscalar (x : E) : r (A (j x)) = z • x :=
    congrArg (fun T : Representation.IntertwiningMap ρ ρ => T x) hz.symm
  have hcopy (f : Representation.IntertwiningMap ρ σ) (x : E) : A (f x) = z • f x := by
    have hc := congrArg (fun T : Representation.IntertwiningMap σ σ => T (j x))
      (hA (f.comp r))
    change A (f (r (j x))) = f (r (A (j x))) at hc
    simpa only [hr, hscalar, map_smul] using hc
  refine ⟨z, fun x hx => ?_⟩
  refine Submodule.iSup_induction (motive := fun x => A x = z • x)
    (fun f : Representation.IntertwiningMap ρ σ => f.toLinearMap.range) hx ?_ ?_ ?_
  · intro f y hy
    obtain ⟨v, rfl⟩ := hy
    exact hcopy f v
  · simp
  · intro x y hx hy
    simp only [map_add, hx, hy, smul_add]

include hρ hσ in

lemma isotypic_finrank_le_commutant (j : Representation.IntertwiningMap ρ σ)
    (hj : ∀ x, ‖j x‖ = ‖x‖) :
    finrank ℂ (isotypicSubrepresentation ρ σ).toSubmodule ≤
      finrank ℂ E * finrank ℂ (Representation.IntertwiningMap σ σ) :=
  (isotypic_finrank_le ρ σ).trans
    (Nat.mul_le_mul_left _ (multiplicity_le_commutant ρ σ hρ hσ j hj))

end SignedSweeps
end

end OAI

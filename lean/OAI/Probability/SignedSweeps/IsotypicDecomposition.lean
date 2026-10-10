import OAI.Probability.SignedSweeps.WordUpper
import OAI.Probability.SignedSweeps.PairWordTypes
import OAI.Probability.SignedSweeps.TensorMultiplicity

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]

def orthogonalSubrepresentation {G : Type*} [Group G]
    (ρ : Representation ℂ G E) (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (S : Subrepresentation ρ) : Subrepresentation ρ where
  toSubmodule := S.toSubmoduleᗮ
  apply_mem_toSubmodule g x hx := by
    rw [Submodule.mem_orthogonal'] at hx ⊢
    intro y hy
    rw [representation_inner_inverse ρ hρ]
    exact hx _ (S.apply_mem_toSubmodule g⁻¹ hy)

lemma specht_isotypic_orthogonal (ρ : Representation ℂ (SymmetricGroup n) E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (lam mu : Partition n) (hne : lam ≠ mu) :
    (isotypicSubrepresentation (spechtRepresentation mu) ρ).toSubmodule ≤
      (isotypicSubrepresentation (spechtRepresentation lam) ρ).toSubmoduleᗮ := by
  apply iSup_le
  intro f x hx
  obtain ⟨x, rfl⟩ := hx
  rw [Submodule.mem_orthogonal]
  intro y hy
  refine Submodule.iSup_induction (motive := fun y => inner ℂ y (f x) = 0)
    (fun k : Representation.IntertwiningMap (spechtRepresentation lam) ρ => k.toLinearMap.range)
    hy ?_ ?_ ?_
  · intro k y hy
    obtain ⟨y,rfl⟩ := hy
    have hz := specht_hom_eq_zero_of_ne mu lam hne.symm
      ((adjointIntertwiner (spechtRepresentation lam) ρ (spechtRepresentation_norm lam) hρ k).comp f)
    have he := congrArg (fun k : Representation.IntertwiningMap (spechtRepresentation mu)
      (spechtRepresentation lam) => k x) hz
    change k.toLinearMap.adjoint (f x) = 0 at he
    rw [← LinearMap.adjoint_inner_right, he, inner_zero_right]
  · simp
  · intro y z hy hz
    simp only [inner_add_left, hy, hz, add_zero]

theorem specht_isotypic_iSup_eq_top (ρ : Representation ℂ (SymmetricGroup n) E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) :
    (⨆ lam : Partition n, (isotypicSubrepresentation (spechtRepresentation lam) ρ).toSubmodule) = ⊤ := by
  let S : Subrepresentation ρ := {
    toSubmodule := ⨆ lam : Partition n, (isotypicSubrepresentation (spechtRepresentation lam) ρ).toSubmodule
    apply_mem_toSubmodule g x hx := by
      refine Submodule.iSup_induction
        (motive := fun x => ρ g x ∈ ⨆ lam : Partition n,
          (isotypicSubrepresentation (spechtRepresentation lam) ρ).toSubmodule)
        (fun lam => (isotypicSubrepresentation (spechtRepresentation lam) ρ).toSubmodule)
        hx ?_ ?_ ?_
      · intro lam y hy
        exact (le_iSup (fun lam => (isotypicSubrepresentation (spechtRepresentation lam) ρ).toSubmodule) lam) ((isotypicSubrepresentation (spechtRepresentation lam) ρ).apply_mem_toSubmodule g hy)
      · simp
      · intro x y hx hy
        simpa only [map_add] using Submodule.add_mem _ hx hy }
  change S.toSubmodule = ⊤
  apply Submodule.orthogonal_eq_bot_iff.mp
  by_contra hn
  let T := orthogonalSubrepresentation ρ hρ S
  have ht : T.toSubmodule ≠ ⊥ := hn
  let : Nontrivial T.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr ht
  obtain ⟨lam, f, hf⟩ := exists_specht_intertwiner T.toRepresentation
  let j : Representation.IntertwiningMap T.toRepresentation ρ :=
    T.toSubmodule.subtype.intertwiningMap_of_isIntertwiningMap _ _ (by intros; rfl)
  have hm (x : Specht lam) : (j.comp f) x ∈ S.toSubmodule :=
    (le_iSup (fun lam => (isotypicSubrepresentation (spechtRepresentation lam) ρ).toSubmodule) lam) (intertwiner_mem_isotypic (spechtRepresentation lam) ρ (j.comp f) x)
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (f x : E) = 0
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  exact ((Submodule.mem_orthogonal S.toSubmodule _).mp (f x).2) _ (hm x)

lemma specht_isotypic_projection_on (ρ : Representation ℂ (SymmetricGroup n) E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (lam mu : Partition n)
    (x : E) (hx : x ∈ (isotypicSubrepresentation (spechtRepresentation mu) ρ).toSubmodule) :
    (isotypicSubrepresentation (spechtRepresentation lam) ρ).toSubmodule.starProjection x =
      if lam = mu then x else 0 := by
  split_ifs with h
  · subst mu
    exact Submodule.starProjection_eq_self_iff.mpr hx
  · apply (isotypicSubrepresentation (spechtRepresentation lam) ρ).toSubmodule.eq_starProjection_of_mem_of_inner_eq_zero
    · simp
    · intro y hy
      simp only [sub_zero]
      exact ((Submodule.mem_orthogonal' _ _).mp (specht_isotypic_orthogonal ρ hρ lam mu h hx)) _ hy

theorem specht_isotypic_projection_sum (ρ : Representation ℂ (SymmetricGroup n) E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) :
    (∑ lam : Partition n,
      (isotypicSubrepresentation (spechtRepresentation lam) ρ).toSubmodule.starProjection.toLinearMap) = 1 := by
  apply LinearMap.ext
  intro x
  have hx : x ∈ ⨆ lam : Partition n,
      (isotypicSubrepresentation (spechtRepresentation lam) ρ).toSubmodule := by
    rw [specht_isotypic_iSup_eq_top ρ hρ]
    trivial
  refine Submodule.iSup_induction (motive := fun x =>
      (∑ lam : Partition n, (isotypicSubrepresentation (spechtRepresentation lam) ρ).toSubmodule.starProjection.toLinearMap) x = x)
    (fun lam => (isotypicSubrepresentation (spechtRepresentation lam) ρ).toSubmodule)
    hx ?_ ?_ ?_
  · intro mu y hy
    simp only [LinearMap.sum_apply, ContinuousLinearMap.coe_coe,
      specht_isotypic_projection_on ρ hρ _ mu y hy]
    simp
  · simp
  · intro y z hy hz
    simp only [map_add, hy, hz]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma wordTypeProjection_sum (p : ℕ) (C : Type*) [Fintype C] :
    (∑ mu : Partition p, wordTypeProjection mu C) = 1 :=
  specht_isotypic_projection_sum (wordRepresentation p C) wordRepresentation_norm

lemma wordTypeProjection_orthogonal {p : ℕ} (C : Type*) [Fintype C]
    (lam mu : Partition p) (hne : lam ≠ mu) :
    wordTypeProjection lam C * wordTypeProjection mu C = 0 := by
  apply LinearMap.ext
  intro x
  exact (specht_isotypic_projection_on (wordRepresentation p C) wordRepresentation_norm lam mu _
    ((isotypicSubrepresentation (spechtRepresentation mu) (wordRepresentation p C)).toSubmodule.starProjection_apply_mem x)).trans
    (ite_eq_right hne)

lemma word_first_column_collision {p : ℕ} {C : Type*} [Fintype C]
    (mu : Partition p) (hmu : Fintype.card C < mu.1.colLen 0) (w : Fin p → C) :
    ∃ i j : Fin p, i ≠ j ∧ mu.colOf i = mu.colOf j ∧ w i = w j := by
  have hc : 0 < mu.1.colLen 0 := lt_of_le_of_lt (Nat.zero_le _) hmu
  have hr : 0 < mu.1.rowLen 0 := by
    exact YoungDiagram.mem_iff_lt_rowLen.mp (YoungDiagram.mem_iff_lt_colLen.mpr hc)
  let j₀ : Fin (mu.1.rowLen 0) := ⟨0,hr⟩
  let e : Fin (mu.1.colLen 0) → Fin p := fun i => mu.colEquiv ⟨j₀,i⟩
  have he : Function.Injective e := by
    intro x y h
    exact eq_of_heq (Sigma.mk.inj_iff.mp (mu.colEquiv.injective h)).2
  have hn : ¬ Function.Injective (w ∘ e) := by
    intro hi
    have h := Fintype.card_le_of_injective _ hi
    simp only [Fintype.card_fin] at h
    omega
  obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp hn
  exact ⟨e i,e j,fun h => hne (he h), by simp [e], hij⟩

lemma word_intertwiner_zero_of_height {p : ℕ} {C : Type*} [Fintype C]
    (mu : Partition p) (hmu : Fintype.card C < mu.1.colLen 0)
    (f : Representation.IntertwiningMap (spechtRepresentation mu) (wordRepresentation p C)) :
    f = 0 := by
  apply specht_hom_ext mu (wordRepresentation p C) f 0
  apply PiLp.ext
  intro w
  obtain ⟨i,j,hij,hc,hw⟩ := word_first_column_collision mu hmu w
  exact word_polytabloid_collision mu f w hij hc hw

lemma wordTypeProjection_zero_of_height {p : ℕ} {C : Type*} [Fintype C]
    (mu : Partition p) (hmu : Fintype.card C < mu.1.colLen 0) :
    wordTypeProjection mu C = 0 := by
  have he : (isotypicSubrepresentation (spechtRepresentation mu)
      (wordRepresentation p C)).toSubmodule = ⊥ := by
    apply le_antisymm _ bot_le
    apply iSup_le
    intro f
    have hf := word_intertwiner_zero_of_height mu hmu f
    rw [hf]
    simp
  simp [wordTypeProjection, he]

lemma word_isotypic_finrank_le {p : ℕ} (mu : Partition p) (C : Type*) [Fintype C] :
    finrank ℂ (isotypicSubrepresentation (spechtRepresentation mu) (wordRepresentation p C)).toSubmodule ≤
      spechtDimension mu * (p+1)^(Fintype.card C * Fintype.card C) := by
  let := specht_irreducible mu
  by_cases hf : ∃ f : Representation.IntertwiningMap (spechtRepresentation mu) (wordRepresentation p C), f ≠ 0
  · obtain ⟨f,hf⟩ := hf
    obtain ⟨j,hj⟩ := intertwiner_isometric_normalization (spechtRepresentation mu) (wordRepresentation p C)
      (spechtRepresentation_norm mu) wordRepresentation_norm f hf
    exact (isotypic_finrank_le _ _).trans (Nat.mul_le_mul_left _
      (word_multiplicity_le _ (spechtRepresentation_norm mu) j hj))
  · push Not at hf
    have hh : finrank ℂ (Representation.IntertwiningMap (spechtRepresentation mu) (wordRepresentation p C)) = 0 :=
      finrank_zero_iff_forall_zero.mpr hf
    have ht := isotypic_finrank_le (spechtRepresentation mu) (wordRepresentation p C)
    rw [hh, mul_zero] at ht
    exact ht.trans (Nat.zero_le _)

end SignedSweeps
end

end OAI

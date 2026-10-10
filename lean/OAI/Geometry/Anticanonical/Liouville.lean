import Mathlib

namespace OAI

/-! Constancy of equivariant analytic families from compact factors and lattice bounds. -/

noncomputable section
open Bundle Set Filter
open scoped Manifold Bundle Topology BoundedContinuousFunction

namespace DeckLiouville

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

 

theorem exists_finite_injective_evaluations [FiniteDimensional ℂ V] {ι : Type*}
    (ev : ι → (V →ₗ[ℂ] ℂ))
    (hsep : ∀ v : V, (∀ i, ev i v = 0) → v = 0) :
    ∃ n : ℕ, ∃ t : Fin n → ι,
      Function.Injective (LinearMap.pi (fun i => ev (t i))) := by
  classical
  obtain ⟨f, hf, hspan, _⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℂ (Set.range ev)
  choose t ht using hf
  refine ⟨_, t, ?_⟩
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  apply hsep v
  intro i
  have hm : ev i ∈ Submodule.span ℂ (Set.range f) := by
    rw [hspan]
    exact Submodule.subset_span (Set.mem_range_self i)
  refine Submodule.span_induction (p := fun g _ => g v = 0) ?_ ?_ ?_ ?_ hm
  · intro g hg
    obtain ⟨j, rfl⟩ := hg
    rw [← ht j]
    exact congrFun hv j
  · simp
  · intro x y hx hy hxv hyv
    simp only [LinearMap.add_apply, hxv, hyv, add_zero]
  · intro a x hx hxv
    simp only [LinearMap.smul_apply, hxv, smul_zero]

 
theorem differentiable_of_evaluations {a : ℕ} {ι : Type*} [Fintype ι]
    (ev : V →ₗ[ℂ] (ι → ℂ)) (hev : Function.Injective ev)
    (v : (Fin a → ℂ) → V)
    (hv : ∀ i, Differentiable ℂ (fun z => ev (v z) i)) :
    Differentiable ℂ v := by
  obtain ⟨back, hback⟩ := ev.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hev)
  have hc : Differentiable ℂ (fun z => back (ev (v z))) :=
    (LinearMap.toContinuousLinearMap back).differentiable.comp (differentiable_pi.mpr hv)
  have heq : (fun z => back (ev (v z))) = v := by
    funext z
    exact LinearMap.congr_fun hback (v z)
  rwa [heq] at hc

 

theorem equivariant_analytic_family_constant {a : ℕ} {Γ : Type*}
    (Λ : Submodule ℤ (Fin a → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (τ : Γ → (Fin a → ℂ)) (hτ : Set.range τ = (Λ : Set (Fin a → ℂ)))
    (ρ : Γ → (V ≃ₗᵢ[ℂ] V))
    (v : (Fin a → ℂ) → V) (hv : Differentiable ℂ v)
    (heq : ∀ g z, v (z + τ g) = ρ g (v z))
    (hne : ∃ z, v z ≠ 0) :
    ∃ s : V, s ≠ 0 ∧ (∀ z, v z = s) ∧ ∀ g, ρ g s = s := by
  have hcompact : IsCompact (Set.range (fun z => ‖v z‖)) :=
    IsZLattice.isCompact_range_of_periodic Λ _ hv.continuous.norm (by
      intro z w hw
      change w ∈ (Λ : Set (Fin a → ℂ)) at hw
      rw [← hτ] at hw
      obtain ⟨g, rfl⟩ := hw
      rw [heq]
      exact (ρ g).norm_map _)
  obtain ⟨C, hC⟩ := hcompact.isBounded.exists_norm_le
  have hbounded : Bornology.IsBounded (Set.range v) := by
    refine isBounded_iff_forall_norm_le.mpr ⟨C, ?_⟩
    rintro _ ⟨z, rfl⟩
    simpa only [norm_norm] using hC ‖v z‖ (Set.mem_range_self z)
  obtain ⟨s, hs⟩ := hv.exists_const_forall_eq_of_bounded hbounded
  refine ⟨s, ?_, hs, ?_⟩
  · intro hs0
    obtain ⟨z, hz⟩ := hne
    exact hz ((hs z).trans hs0)
  · intro g
    calc
      ρ g s = ρ g (v 0) := congrArg (ρ g) (hs 0).symm
      _ = v (0 + τ g) := (heq g 0).symm
      _ = s := hs _

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℂ E H) [I.Boundaryless]
variable {W : Type*} [TopologicalSpace W] [ChartedSpace H W] [IsManifold I 1 W]
  [CompactSpace W] [ConnectedSpace W]

 

theorem compact_factor_equivariant_family_constant {a : ℕ} {Γ ι : Type*} [Fintype ι]
    (Λ : Submodule ℤ (Fin a → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (τ : Γ → (Fin a → ℂ)) (hτ : Set.range τ = (Λ : Set (Fin a → ℂ)))
    (σ : Γ → W → W) (ρ : Γ → (V ≃ₗᵢ[ℂ] V))
    (ev : V →ₗ[ℂ] (ι → ℂ)) (hev : Function.Injective ev)
    (v : (Fin a → ℂ) → W → V)
    (hz : ∀ w i, Differentiable ℂ (fun z => ev (v z w) i))
    (hw : ∀ z i, MDifferentiable I 𝓘(ℂ, ℂ) (fun w => ev (v z w) i))
    (heq : ∀ g z w, v (z + τ g) (σ g w) = ρ g (v z w))
    (hne : ∃ z w, v z w ≠ 0) :
    ∃ s : V, s ≠ 0 ∧ (∀ z w, v z w = s) ∧ ∀ g, ρ g s = s := by
  have windependent (z : Fin a → ℂ) (w w' : W) : v z w = v z w' := by
    apply hev
    funext i
    exact (hw z i).apply_eq_of_compactSpace w w'
  let w₀ : W := Classical.arbitrary W
  have heq' (g : Γ) (z : Fin a → ℂ) : v (z + τ g) w₀ = ρ g (v z w₀) :=
    (windependent _ _ _).trans (heq g z w₀)
  have hne' : ∃ z, v z w₀ ≠ 0 := by
    obtain ⟨z, w, hzw⟩ := hne
    refine ⟨z, ?_⟩
    intro hz0
    exact hzw ((windependent z w w₀).trans hz0)
  obtain ⟨s, hs, hconst, hinv⟩ := equivariant_analytic_family_constant Λ τ hτ ρ
    (fun z => v z w₀) (differentiable_of_evaluations ev hev _ (hz w₀)) heq' hne'
  exact ⟨s, hs, fun z w => (windependent z w w₀).trans (hconst z), hinv⟩

end DeckLiouville

end

end OAI

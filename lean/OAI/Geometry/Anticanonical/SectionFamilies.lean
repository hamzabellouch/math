import OAI.Geometry.Anticanonical.CompactSections
import OAI.Geometry.Anticanonical.Liouville

namespace OAI

/-! Recovery of invariant sections from holomorphic families of compact-bundle sections. -/

noncomputable section
open Bundle Set Filter
open scoped Manifold Bundle Topology BoundedContinuousFunction

namespace NativeLiouville

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
  {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) (⊤ : WithTop ℕ∞) M]
  (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]
  [ContMDiffVectorBundle (⊤ : WithTop ℕ∞) F V 𝓘(ℂ, E)]

abbrev H0 := ContMDiffSection 𝓘(ℂ, E) F (⊤ : WithTop ℕ∞) V

 
def sectionEval (x : M) (ℓ : F →ₗ[ℂ] ℂ) : H0 (E := E) (F := F) V →ₗ[ℂ] ℂ where
  toFun s := ℓ ((trivializationAt F V x ⟨x, s x⟩).2)
  map_add' s t := by
    rw [show (trivializationAt F V x ⟨x, (s + t) x⟩).2 =
      (trivializationAt F V x ⟨x, s x⟩).2 + (trivializationAt F V x ⟨x, t x⟩).2 from
        ((trivializationAt F V x).linearEquivAt ℂ x (mem_baseSet_trivializationAt F V x)).map_add _ _]
    exact ℓ.map_add _ _
  map_smul' c s := by
    rw [show (trivializationAt F V x ⟨x, (c • s) x⟩).2 =
      c • (trivializationAt F V x ⟨x, s x⟩).2 from
        ((trivializationAt F V x).linearEquivAt ℂ x (mem_baseSet_trivializationAt F V x)).map_smul _ _]
    exact ℓ.map_smul _ _

variable {EW : Type*} [NormedAddCommGroup EW] [NormedSpace ℂ EW]
  [FiniteDimensional ℂ EW] {W : Type*} [TopologicalSpace W] [ChartedSpace EW W]
  [IsManifold 𝓘(ℂ, EW) (⊤ : WithTop ℕ∞) W] [CompactSpace W] [ConnectedSpace W]

 

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ EW] in
theorem native_family_recovery {a : ℕ} {Γ : Type*}
    (Λ : Submodule ℤ (Fin a → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (τ : Γ → (Fin a → ℂ)) (hτ : Set.range τ = (Λ : Set (Fin a → ℂ)))
    (σ : Γ → W → W)
    (h : InnerProductSpace.Core ℂ (H0 (E := E) (F := F) V))
    (ρ : Γ → (H0 (E := E) (F := F) V ≃ₗ[ℂ] H0 (E := E) (F := F) V))
    (hρ : ∀ g s t, h.inner (ρ g s) (ρ g t) = h.inner s t)
    (v : (Fin a → ℂ) → W → H0 (E := E) (F := F) V)
    (hv : ContMDiff ((𝓘(ℂ, Fin a → ℂ)).prod ((𝓘(ℂ, EW)).prod 𝓘(ℂ, E)))
      ((𝓘(ℂ, E)).prod 𝓘(ℂ, F)) (⊤ : WithTop ℕ∞)
      (fun p : (Fin a → ℂ) × W × M => (⟨p.2.2, v p.1 p.2.1 p.2.2⟩ : TotalSpace F V)))
    (heq : ∀ g z w, v (z + τ g) (σ g w) = ρ g (v z w))
    (hne : ∃ z w, v z w ≠ 0) :
    ∃ s : H0 (E := E) (F := F) V, s ≠ 0 ∧
      (∀ z w, v z w = s) ∧ ∀ g, ρ g s = s := by
  classical
  let C := H0 (E := E) (F := F) V
  let : FiniteDimensional ℂ C := CompactSections.finiteDimensional_holomorphic_sections V
  let : InnerProductSpace.Core ℂ C := h
  let : NormedAddCommGroup C := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := C)
  let : NormedSpace ℂ C := NormedSpace.ofCore (InnerProductSpace.Core.toNormedSpaceCore h)
  let ρ' : Γ → (C ≃ₗᵢ[ℂ] C) := fun g =>
    { toLinearEquiv := ρ g
      norm_map' := fun s => congrArg (fun z : ℂ => Real.sqrt z.re) (hρ g s s) }
  let ev : (M × (F →ₗ[ℂ] ℂ)) → (C →ₗ[ℂ] ℂ) := fun p => sectionEval V p.1 p.2
  have hsep (s : C) (hs : ∀ p, ev p s = 0) : s = 0 := by
    ext x
    let e := trivializationAt F V x
    apply (e.linearEquivAt ℂ x (mem_baseSet_trivializationAt F V x)).injective
    change (e.linearEquivAt ℂ x _) (s x) = (e.linearEquivAt ℂ x _) (0 : V x)
    rw [map_zero]
    apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
    intro ℓ
    exact hs (x, ℓ)
  obtain ⟨n, t, ht⟩ := DeckLiouville.exists_finite_injective_evaluations ev hsep
  let evals : C →ₗ[ℂ] (Fin n → ℂ) := LinearMap.pi (fun i => ev (t i))
  have hz (w : W) (i : Fin n) : Differentiable ℂ (fun z => evals (v z w) i) := by
    let x := (t i).1
    let ℓ := (t i).2
    let e := trivializationAt F V x
    have hslice : ContMDiff 𝓘(ℂ, Fin a → ℂ) ((𝓘(ℂ, E)).prod 𝓘(ℂ, F))
        (⊤ : WithTop ℕ∞) (fun z => (⟨x, v z w x⟩ : TotalSpace F V)) :=
      hv.comp (contMDiff_id.prodMk (contMDiff_const.prodMk contMDiff_const))
    have hc : ContMDiff 𝓘(ℂ, Fin a → ℂ) 𝓘(ℂ, F) (⊤ : WithTop ℕ∞)
        (fun z => (e ⟨x, v z w x⟩).2) :=
      (e.contMDiff_iff (fun _ => e.mem_source.mpr (mem_baseSet_trivializationAt F V x))).mp hslice |>.2
    exact mdifferentiable_iff_differentiable.mp
      ((ℓ.toContinuousLinearMap.contMDiff.comp hc).mdifferentiable (by simp))
  have hw (z : Fin a → ℂ) (i : Fin n) :
      MDifferentiable 𝓘(ℂ, EW) 𝓘(ℂ, ℂ) (fun w => evals (v z w) i) := by
    let x := (t i).1
    let ℓ := (t i).2
    let e := trivializationAt F V x
    have hslice : ContMDiff 𝓘(ℂ, EW) ((𝓘(ℂ, E)).prod 𝓘(ℂ, F))
        (⊤ : WithTop ℕ∞) (fun w => (⟨x, v z w x⟩ : TotalSpace F V)) :=
      hv.comp (contMDiff_const.prodMk (contMDiff_id.prodMk contMDiff_const))
    have hc : ContMDiff 𝓘(ℂ, EW) 𝓘(ℂ, F) (⊤ : WithTop ℕ∞)
        (fun w => (e ⟨x, v z w x⟩).2) :=
      (e.contMDiff_iff (fun _ => e.mem_source.mpr (mem_baseSet_trivializationAt F V x))).mp hslice |>.2
    exact (ℓ.toContinuousLinearMap.contMDiff.comp hc).mdifferentiable (by simp)
  exact DeckLiouville.compact_factor_equivariant_family_constant 𝓘(ℂ, EW)
    Λ τ hτ σ ρ' evals ht v hz hw heq hne

end NativeLiouville

end

end OAI

import OAI.Geometry.SurfaceImmersion.Primitive.LoopDensityCompact

namespace OAI

/-! Extend prescribed positive densities while fixing a closed collar. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.LoopDensity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]

theorem positive_density_compact_preserving
    {p : B → ℝ → Plane} {c : B → Plane}
    (hp : ContDiff ℝ ∞ (fun z : B × ℝ => p z.1 z.2))
    {U C K : Set B} (hU : IsOpen U) (hC : IsClosed C) (hCU : C ⊆ U)
    (hK : IsCompact K) (ρ₀ : B × ℝ → ℝ)
    (hρ₀ : ContDiffOn ℝ ∞ ρ₀ (U ×ˢ univ))
    (hpos₀ : ∀ b ∈ U, ∀ t, 0 < ρ₀ (b, t))
    (hper₀ : ∀ b, Function.Periodic (fun t => ρ₀ (b, t)) 1)
    (hmom₀ : ∀ b ∈ U, (∫ t in 0..1, ρ₀ (b, t) • augment (p b t)) = augment (c b))
    (hlocal : ∀ b ∈ K \ U, ∃ W : Set B, IsOpen W ∧ b ∈ W ∧ ∃ ρ : B × ℝ → ℝ,
      ContDiffOn ℝ ∞ ρ (W ×ˢ univ) ∧
      (∀ x ∈ W, ∀ t, 0 < ρ (x, t)) ∧
      (∀ x, Function.Periodic (fun t => ρ (x, t)) 1) ∧
      ∀ x ∈ W, (∫ t in 0..1, ρ (x, t) • augment (p x t)) = augment (c x)) :
    ∃ V : Set B, IsOpen V ∧ K ⊆ V ∧ ∃ σ : B × ℝ → ℝ,
      ContDiffOn ℝ ∞ σ (V ×ˢ univ) ∧
      (∀ b ∈ V, ∀ t, 0 < σ (b, t)) ∧
      (∀ b, Function.Periodic (fun t => σ (b, t)) 1) ∧
      (∀ b ∈ V, (∫ t in 0..1, σ (b, t) • augment (p b t)) = augment (c b)) ∧
      ∀ b ∈ V ∩ C, ∀ t, σ (b, t) = ρ₀ (b, t) := by
  classical
  let I := {b : B // b ∈ K \ U}
  choose W hW hbW ρ hρ hpos hper hmom using fun b : I => hlocal b b.property
  let O : Option I → Set B := fun i =>
    match i with
    | none => U
    | some b => W b \ C
  let r : Option I → B × ℝ → ℝ := fun i =>
    match i with
    | none => ρ₀
    | some b => ρ b
  have hO (i : Option I) : IsOpen (O i) := by
    cases i with
    | none => exact hU
    | some b => exact (hW b).sdiff hC
  have hr (i : Option I) : ContDiffOn ℝ ∞ (r i) (O i ×ˢ univ) := by
    cases i with
    | none => exact hρ₀
    | some b => exact (hρ b).mono (fun _ hx => ⟨hx.1.1, hx.2⟩)
  have hrpos (i : Option I) (x : B) (hx : x ∈ O i) (t : ℝ) : 0 < r i (x, t) := by
    cases i with
    | none => exact hpos₀ x hx t
    | some b => exact hpos b x hx.1 t
  have hrper (i : Option I) (x : B) : Function.Periodic (fun t => r i (x, t)) 1 := by
    cases i with
    | none => exact hper₀ x
    | some b => exact hper b x
  have hrmom (i : Option I) (x : B) (hx : x ∈ O i) :
      (∫ t in 0..1, r i (x, t) • augment (p x t)) = augment (c x) := by
    cases i with
    | none => exact hmom₀ x hx
    | some b => exact hmom b x hx.1
  have hcover : K ⊆ ⋃ i, O i := by
    intro b hbK
    by_cases hbU : b ∈ U
    · exact mem_iUnion.mpr ⟨none, hbU⟩
    · have hbC : b ∉ C := fun h => hbU (hCU h)
      exact mem_iUnion.mpr ⟨some ⟨b, hbK, hbU⟩, hbW ⟨b, hbK, hbU⟩, hbC⟩
  obtain ⟨V, hV, hKV, σ, hσ, hσpos, hσper, hσmom, heq⟩ :=
    compact_patch_densities hp O hO r hr hrpos hrper hrmom hK hcover
  refine ⟨V, hV, hKV, σ, hσ, hσpos, hσper, hσmom, ?_⟩
  intro b hb t
  apply heq b hb.1 t (ρ₀ (b, t))
  intro i hi
  cases i with
  | none => rfl
  | some x => exact False.elim (hi.2 hb.2)

end ClosedSurfaceR4.LoopDensity

end

end OAI

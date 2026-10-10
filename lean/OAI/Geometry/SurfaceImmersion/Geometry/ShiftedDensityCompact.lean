import OAI.Geometry.SurfaceImmersion.Geometry.BlendedDensityCompact

namespace OAI

/-! Uniform positive densities for small translations of the blended angle.
The allowable translation size follows from compactness after constructing
smooth solutions near zero translation. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]

theorem shifted_density_compact {a A s : B → ℝ} {c : B → LoopDensity.Plane}
    (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A)
    (hs : ContDiff ℝ ∞ s) (hc : ContDiff ℝ ∞ c)
    {K : Set B} (hK : IsCompact K)
    (hshape : ∀ b ∈ K,
      (0 < a b ∧ 2 * Real.arctan (a b) ≤ A b ∧ s b ∈ Icc (0 : ℝ) 1 ∧
        c b = ![(1 - a b ^ 2 / 2) / (1 + a b ^ 2 / 2), 0]) ∨
      (s b = 1 ∧ Real.pi < A b ∧ c b 0 ^ 2 + c b 1 ^ 2 < 1)) :
    ∃ W : Set B, IsOpen W ∧ K ⊆ W ∧ ∃ ε : ℝ, 0 < ε ∧
      ∃ ρ : (B × ℝ) × ℝ → ℝ,
        ContDiffOn ℝ ∞ ρ ((W ×ˢ Metric.ball (0 : ℝ) ε) ×ˢ univ) ∧
        (∀ b ∈ W, ∀ h, |h| < ε → ∀ t, 0 < ρ ((b, h), t)) ∧
        (∀ b h, Function.Periodic (fun t => ρ ((b, h), t)) 1) ∧
        ∀ b ∈ W, ∀ h, |h| < ε →
          (∫ t in 0..1, ρ ((b, h), t) •
            LoopDensity.augment (blendedPath (a b) (A b) (s b) h t)) =
              LoopDensity.augment (c b) := by
  classical
  let a' : B × ℝ → ℝ := fun p => a p.1
  let A' : B × ℝ → ℝ := fun p => A p.1
  let s' : B × ℝ → ℝ := fun p => s p.1
  let c' : B × ℝ → LoopDensity.Plane := fun p => c p.1
  have ha' : ContDiff ℝ ∞ a' := ha.comp contDiff_fst
  have hA' : ContDiff ℝ ∞ A' := hA.comp contDiff_fst
  have hs' : ContDiff ℝ ∞ s' := hs.comp contDiff_fst
  have hc' : ContDiff ℝ ∞ c' := hc.comp contDiff_fst
  let J := {p : B × ℝ // p ∈ K ×ˢ ({0} : Set ℝ)}
  have hlocal (p : J) : ∃ V : Set (B × ℝ), IsOpen V ∧ p.val ∈ V ∧
      ∃ ρ : (B × ℝ) × ℝ → ℝ, ContDiffOn ℝ ∞ ρ (V ×ˢ univ) ∧
        (∀ b ∈ V, ∀ t, 0 < ρ (b, t)) ∧
        (∀ b, Function.Periodic (fun t => ρ (b, t)) 1) ∧
        ∀ b ∈ V, (∫ t in 0..1, ρ (b, t) • LoopDensity.augment
          (blendedPath (a' b) (A' b) (s' b) b.2 t)) = LoopDensity.augment (c' b) := by
    have hp0 : p.val.2 = 0 := p.property.2
    rcases hshape p.val.1 p.property.1 with ht | hi
    · exact blended_positive_density_near ha' hA' hs' contDiff_snd hc'
        ht.1 ht.2.1 ht.2.2.1 hp0 ht.2.2.2
    · apply blended_density_near_interior ha' hA' hs' contDiff_snd hc' hi.1 _ hi.2.2
      simpa only [hp0, abs_zero, add_zero] using hi.2.1
  choose V hV hpV ρ hρ hpos hper hmom using hlocal
  have hcover : K ×ˢ ({0} : Set ℝ) ⊆ ⋃ p : J, V p := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, hpV ⟨p, hp⟩⟩
  obtain ⟨U, hU, hKU, σ, hσ, hσpos, hσper, hσmom, _⟩ :=
    LoopDensity.compact_patch_densities
      (blendedPath_smooth ha' hA' hs' contDiff_snd) V hV ρ hρ hpos hper hmom
      (hK.prod isCompact_singleton) hcover
  obtain ⟨W, Z, hW, hZ, hKW, h0Z, hWZ⟩ :=
    generalized_tube_lemma hK isCompact_singleton hU hKU
  obtain ⟨ε, hε, hεZ⟩ := Metric.isOpen_iff.mp hZ 0 (h0Z (mem_singleton 0))
  have htube : W ×ˢ Metric.ball (0 : ℝ) ε ⊆ U :=
    (prod_mono Subset.rfl hεZ).trans hWZ
  refine ⟨W, hW, hKW, ε, hε, σ, hσ.mono (prod_mono htube Subset.rfl), ?_, ?_, ?_⟩
  · intro b hb h hh t
    exact hσpos (b, h) (htube ⟨hb, by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hh⟩) t
  · intro b h
    exact hσper (b, h)
  · intro b hb h hh
    exact hσmom (b, h) (htube ⟨hb, by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hh⟩)

end ClosedSurfaceR4.CollarVelocity

end

end OAI

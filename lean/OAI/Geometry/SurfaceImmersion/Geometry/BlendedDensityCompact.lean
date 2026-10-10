import OAI.Geometry.SurfaceImmersion.Whitney.CollarDensityMoments
import OAI.Geometry.SurfaceImmersion.Primitive.LoopDensityRelative

namespace OAI

/-! Positive densities through the collar, transition, and circle-covering interior. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]

theorem blended_density_near_interior
    {a A s h : B → ℝ} {c : B → LoopDensity.Plane}
    (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A)
    (hs : ContDiff ℝ ∞ s) (hh : ContDiff ℝ ∞ h) (hc : ContDiff ℝ ∞ c)
    {b₀ : B} (hs₀ : s b₀ = 1) (hA₀ : Real.pi + |h b₀| < A b₀)
    (hc₀ : c b₀ 0 ^ 2 + c b₀ 1 ^ 2 < 1) :
    ∃ U : Set B, IsOpen U ∧ b₀ ∈ U ∧ ∃ ρ : B × ℝ → ℝ,
      ContDiffOn ℝ ∞ ρ (U ×ˢ univ) ∧
      (∀ b ∈ U, ∀ t, 0 < ρ (b, t)) ∧
      (∀ b, Function.Periodic (fun t => ρ (b, t)) 1) ∧
      ∀ b ∈ U, (∫ t in 0..1, ρ (b, t) •
        LoopDensity.augment (blendedPath (a b) (A b) (s b) (h b) t)) = LoopDensity.augment (c b) := by
  apply LoopDensity.positive_density_near_of_circle_coverage
    (blendedPath_smooth ha hA hs hh) hc hc₀
  intro e he
  obtain ⟨t, ht, hpt⟩ := LoopDensity.interiorPath_covers hA₀ he
  exact ⟨t, ht, by simpa [blendedPath, blendedAngle, hs₀, LoopDensity.interiorPath] using hpt⟩

/-- The density is constructed on a neighborhood of the whole compact parameter set,
and agrees exactly with the prescribed rational density on the closed collar. -/
theorem blended_density_compact
    {a A s h : B → ℝ} {c : B → LoopDensity.Plane}
    (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A)
    (hs : ContDiff ℝ ∞ s) (hh : ContDiff ℝ ∞ h) (hc : ContDiff ℝ ∞ c)
    {U C K : Set B} (hU : IsOpen U) (hC : IsClosed C) (hCU : C ⊆ U) (hK : IsCompact K)
    (hcollar : ∀ b ∈ U, s b = 0 ∧ h b = 0 ∧
      c b = ![(1 - a b ^ 2 / 2) / (1 + a b ^ 2 / 2), 0])
    (hrest : ∀ b ∈ K \ U,
      (0 < a b ∧ 2 * Real.arctan (a b) ≤ A b ∧ s b ∈ Icc (0 : ℝ) 1 ∧ h b = 0 ∧
        c b = ![(1 - a b ^ 2 / 2) / (1 + a b ^ 2 / 2), 0]) ∨
      (s b = 1 ∧ Real.pi + |h b| < A b ∧ c b 0 ^ 2 + c b 1 ^ 2 < 1)) :
    ∃ V : Set B, IsOpen V ∧ K ⊆ V ∧ ∃ ρ : B × ℝ → ℝ,
      ContDiffOn ℝ ∞ ρ (V ×ˢ univ) ∧
      (∀ b ∈ V, ∀ t, 0 < ρ (b, t)) ∧
      (∀ b, Function.Periodic (fun t => ρ (b, t)) 1) ∧
      (∀ b ∈ V, (∫ t in 0..1, ρ (b, t) •
        LoopDensity.augment (blendedPath (a b) (A b) (s b) (h b) t)) = LoopDensity.augment (c b)) ∧
      ∀ b ∈ V ∩ C, ∀ t, ρ (b, t) = unitDensity (a b) t := by
  apply LoopDensity.positive_density_compact_preserving (blendedPath_smooth ha hA hs hh)
    hU hC hCU hK (fun z => unitDensity (a z.1) z.2)
  · exact (unitDensity_smooth.comp ((ha.comp contDiff_fst).prodMk contDiff_snd)).contDiffOn
  · intro b _ t
    exact unitDensity_pos _ _
  · intro b
    exact unitDensity_periodic (a b)
  · intro b hb
    obtain ⟨hsb, hhb, hcb⟩ := hcollar b hb
    simp only [hsb, hhb, hcb]
    exact collar_density_moments _ _
  · intro b hb
    rcases hrest b hb with ht | hi
    · exact blended_positive_density_near ha hA hs hh hc ht.1 ht.2.1 ht.2.2.1 ht.2.2.2.1 ht.2.2.2.2
    · exact blended_density_near_interior ha hA hs hh hc hi.1 hi.2.1 hi.2.2

end ClosedSurfaceR4.CollarVelocity

end

end OAI

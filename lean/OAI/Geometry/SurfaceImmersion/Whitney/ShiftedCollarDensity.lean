import OAI.Geometry.SurfaceImmersion.Geometry.ShiftedDensityPullback
import OAI.Geometry.SurfaceImmersion.Primitive.LoopDensityMomentConverse

namespace OAI

/-! Construct the mean-adjusting density for the whole collar/interior family,
allowing any sufficiently small smooth translation supported off the collar. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

private lemma path_continuous (a A s h : ℝ) : Continuous (blendedPath a A s h) := by
  have hb : Continuous (fun t : ℝ => baseAngle a (2 * Real.pi * t)) := by
    unfold baseAngle
    fun_prop
  have hg : Continuous (fun t : ℝ => blendedAngle a A s h (2 * Real.pi * t)) := by
    unfold blendedAngle
    fun_prop
  apply continuous_pi
  intro i
  fin_cases i
  · exact Real.continuous_cos.comp hg
  · exact Real.continuous_sin.comp hg

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]

theorem small_shift_collar_density {a A s : B → ℝ} {c : B → LoopDensity.Plane}
    (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A)
    (hs : ContDiff ℝ ∞ s) (hc : ContDiff ℝ ∞ c)
    {U C K : Set B} (hU : IsOpen U) (hC : IsClosed C) (hCU : C ⊆ U) (hK : IsCompact K)
    (hcollar : ∀ b ∈ U, s b = 0 ∧ c b = ![(1 - a b ^ 2 / 2) / (1 + a b ^ 2 / 2), 0])
    (hrest : ∀ b ∈ K \ U,
      (0 < a b ∧ 2 * Real.arctan (a b) ≤ A b ∧ s b ∈ Icc (0 : ℝ) 1 ∧
        c b = ![(1 - a b ^ 2 / 2) / (1 + a b ^ 2 / 2), 0]) ∨
      (s b = 1 ∧ Real.pi < A b ∧ c b 0 ^ 2 + c b 1 ^ 2 < 1)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : B → ℝ, ContDiff ℝ ∞ h →
      (∀ b, |h b| < ε) → (∀ b ∈ U, h b = 0) →
      ∃ V : Set B, IsOpen V ∧ K ⊆ V ∧ ∃ ρ : B × ℝ → ℝ,
        ContDiffOn ℝ ∞ ρ (V ×ˢ univ) ∧
        (∀ b ∈ V, ∀ t, 0 < ρ (b, t)) ∧
        (∀ b, Function.Periodic (fun t => ρ (b, t)) 1) ∧
        (∀ b ∈ V, (∫ t in 0..1, ρ (b, t) •
          LoopDensity.augment (blendedPath (a b) (A b) (s b) (h b) t)) =
            LoopDensity.augment (c b)) ∧
        ∀ b ∈ V ∩ C, ∀ t, ρ (b, t) = unitDensity (a b) t := by
  obtain ⟨W, hW, hKW, ε, hε, hsol⟩ := small_shift_density ha hA hs hc (hK.diff hU) hrest
  refine ⟨ε, hε, ?_⟩
  intro h hh hsmall hzero
  obtain ⟨σ, hσ, hσpos, hσper, hσmass, hσmean⟩ := hsol h hh hsmall
  apply LoopDensity.positive_density_compact_preserving
    (blendedPath_smooth ha hA hs hh) hU hC hCU hK (fun z => unitDensity (a z.1) z.2)
  · exact (unitDensity_smooth.comp ((ha.comp contDiff_fst).prodMk contDiff_snd)).contDiffOn
  · intro b _ t
    exact unitDensity_pos _ _
  · intro b
    exact unitDensity_periodic (a b)
  · intro b hb
    obtain ⟨hsb, hcb⟩ := hcollar b hb
    simp only [hsb, hzero b hb, hcb]
    exact collar_density_moments _ _
  · intro b hb
    refine ⟨W, hW, hKW hb, σ, hσ, hσpos, hσper, ?_⟩
    intro x hx
    exact LoopDensity.augmented_moments (ρ := fun t => σ (x, t))
      (p := fun t => blendedPath (a x) (A x) (s x) (h x) t) (c := c x)
      (LocalPeriodicCalculus.smooth_slice hW hσ hx).continuous (path_continuous (a x) (A x) (s x) (h x))
      (hσmass x hx) (hσmean x hx)

end ClosedSurfaceR4.CollarVelocity

end

end OAI

import OAI.Geometry.SurfaceImmersion.Geometry.ShiftedDensityCompact
import OAI.Geometry.SurfaceImmersion.Primitive.LoopDensityMoments

namespace OAI

/-! Pull back the universal translation-dependent density along any small smooth
translation. Its derivatives may be arbitrarily large. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]

theorem small_shift_density {a A s : B → ℝ} {c : B → LoopDensity.Plane}
    (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A)
    (hs : ContDiff ℝ ∞ s) (hc : ContDiff ℝ ∞ c)
    {K : Set B} (hK : IsCompact K)
    (hshape : ∀ b ∈ K,
      (0 < a b ∧ 2 * Real.arctan (a b) ≤ A b ∧ s b ∈ Icc (0 : ℝ) 1 ∧
        c b = ![(1 - a b ^ 2 / 2) / (1 + a b ^ 2 / 2), 0]) ∨
      (s b = 1 ∧ Real.pi < A b ∧ c b 0 ^ 2 + c b 1 ^ 2 < 1)) :
    ∃ W : Set B, IsOpen W ∧ K ⊆ W ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ h : B → ℝ, ContDiff ℝ ∞ h → (∀ b, |h b| < ε) →
        ∃ σ : B × ℝ → ℝ, ContDiffOn ℝ ∞ σ (W ×ˢ univ) ∧
          (∀ b ∈ W, ∀ t, 0 < σ (b, t)) ∧
          (∀ b, Function.Periodic (fun t => σ (b, t)) 1) ∧
          (∀ b ∈ W, (∫ t in 0..1, σ (b, t)) = 1) ∧
          ∀ b ∈ W, (∫ t in 0..1, σ (b, t) •
            blendedPath (a b) (A b) (s b) (h b) t) = c b := by
  obtain ⟨W, hW, hKW, ε, hε, ρ, hρ, hpos, hper, hmom⟩ :=
    shifted_density_compact ha hA hs hc hK hshape
  refine ⟨W, hW, hKW, ε, hε, ?_⟩
  intro h hh hsmall
  let σ : B × ℝ → ℝ := fun z => ρ ((z.1, h z.1), z.2)
  have hσ : ContDiffOn ℝ ∞ σ (W ×ˢ univ) := by
    apply hρ.comp
      (((contDiff_fst.prodMk (hh.comp contDiff_fst)).prodMk contDiff_snd).contDiffOn)
    intro z hz
    exact ⟨⟨hz.1, by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, Function.comp_apply] using hsmall z.1⟩, hz.2⟩
  have hσpos (b : B) (hb : b ∈ W) (t : ℝ) : 0 < σ (b, t) :=
    hpos b hb (h b) (hsmall b) t
  have hσmom (b : B) (hb : b ∈ W) :
      (∫ t in 0..1, σ (b, t) •
        LoopDensity.augment (blendedPath (a b) (A b) (s b) (h b) t)) =
          LoopDensity.augment (c b) := hmom b hb (h b) (hsmall b)
  have hσboth (b : B) (hb : b ∈ W) := LoopDensity.mass_and_mean
    (LocalPeriodicCalculus.smooth_slice hW hσ hb).continuous
    ((blendedPath_smooth ha hA hs hh).continuous.comp
      (continuous_const.prodMk continuous_id)) (hσmom b hb)
  exact ⟨σ, hσ, hσpos, (fun b => hper b (h b)),
    (fun b hb => (hσboth b hb).1), (fun b hb => (hσboth b hb).2)⟩

end ClosedSurfaceR4.CollarVelocity

end

end OAI

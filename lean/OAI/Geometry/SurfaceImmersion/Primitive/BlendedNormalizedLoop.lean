import OAI.Geometry.SurfaceImmersion.Geometry.BlendedDensityCompact
import OAI.Geometry.SurfaceImmersion.Geometry.DensityNormalizedPath

namespace OAI

/-! Construct the normalized leading loop across all three parameter regions. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]

theorem blended_normalized_loop
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
    ∃ V : Set B, IsOpen V ∧ K ⊆ V ∧ ∃ q : B × ℝ → LoopDensity.Plane,
      ContDiffOn ℝ ∞ q (V ×ˢ univ) ∧
      (∀ b ∈ V, Function.Periodic (fun t => q (b, t)) 1) ∧
      (∀ b ∈ V, (∫ t in 0..1, q (b, t)) = c b) ∧
      (∀ b ∈ V, ∀ t, q (b, t) 0 ^ 2 + q (b, t) 1 ^ 2 = 1) ∧
      ∀ b ∈ V ∩ C, a b = 0 → ∀ t, q (b, t) = ![1, 0] := by
  obtain ⟨V, hV, hKV, ρ, hρ, hpos, hper, hmom, _hfixed⟩ :=
    blended_density_compact ha hA hs hh hc hU hC hCU hK hcollar hrest
  let p : B → ℝ → LoopDensity.Plane := fun b t => blendedPath (a b) (A b) (s b) (h b) t
  have hp : ContDiff ℝ ∞ (fun z : B × ℝ => p z.1 z.2) := blendedPath_smooth ha hA hs hh
  have hunit (b : B) (_hb : b ∈ V) (t : ℝ) : p b t 0 ^ 2 + p b t 1 ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq _
  have hq := LoopDensity.normalizedPath_properties hV hρ hp.contDiffOn hpos
    (fun b _ => hper b) (fun b _ => blendedPath_periodic _ _ _ _) hmom hunit
  refine ⟨V, hV, hKV, LoopDensity.normalizedPath ρ p,
    hq.1, hq.2.1, hq.2.2.1, hq.2.2.2, ?_⟩
  intro b hb haz t
  obtain ⟨hsb, hhb, _⟩ := hcollar b (hCU hb.2)
  simp [LoopDensity.normalizedPath, PositiveDensity.reparametrize,
    p, blendedPath, blendedAngle, baseAngle, haz, hsb, hhb]

end ClosedSurfaceR4.CollarVelocity

end

end OAI

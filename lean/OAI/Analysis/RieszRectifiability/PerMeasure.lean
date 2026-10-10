import OAI.Analysis.RieszRectifiability.Restart.OriginalADUniformRestartSurfacePieces
import OAI.Analysis.RieszRectifiability.Kernel.GlobalGrowth

namespace OAI

/-!
# Per-measure Riesz rectifiability

This endpoint retains the original per-measure statement. For nontrivial support,
AD regularity supplies global upper growth; uniform restart surface pieces and
the hard-truncated Riesz bound then yield Lipschitz ball maps. Subsingleton
support is handled separately, so the theorem does not require a positive or
finite support diameter. Uniform choices before the measure belong to the
separate quantitative endpoint.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

/-- The hard-truncated Riesz bound gives Lipschitz ball maps for each measure. -/
theorem exact_higher_codimension_riesz_rectifiability : FullStatement := by
  intro d n _hd hn hnd μ hreg hAD hRiesz
  let : μ.Regular := hreg
  cases n with
  | zero => omega
  | succ p =>
    by_cases hsupport : μ.support.Nontrivial
    · obtain ⟨G₀, hg₀⟩ := globalGrowth_of_ADRegular_nontrivial (p + 1) μ hAD hsupport
      have hG : 0 < G₀ + 1 := by linarith [hg₀.1]
      have hg : GlobalUpperGrowth (p + 1) (G₀ + 1) μ := hg₀.mono_constant (by linarith)
      obtain ⟨ε, hε, hεfine, hsmall, hpieces⟩ := exists_original_AD_uniform_restart_surface_pieces
        (Nat.succ_pos p) (by omega) μ hAD (G₀ + 1) hG hg
      exact uniformlyRectifiable_of_Riesz_and_uniform_restart_surface_pieces
        (by omega) μ hAD hRiesz (G₀ + 1) hG hg ε hε hεfine hsmall hpieces
    · exact uniformlyRectifiable_of_subsingleton_support (p + 1) μ (Set.not_nontrivial_iff.mp hsupport)

end

end RieszRectifiability

end OAI

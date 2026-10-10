import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBSlopeError

namespace OAI

/-! At a remote endpoint the normalized slope mismatch is of order E⁻²,
uniformly under the radial frequency and derivative bounds. -/

namespace DefocusingNLS

theorem spectralWKB_remote_mismatch (h F gamma g E : ℝ)
    (hh : h^2 = 1) (hE : 0 < E) (hF : E^2/32 ≤ F) (hg : |g| ≤ 4*F/E) :
    ‖((h : ℂ)*Complex.I)*(Real.sqrt F : ℂ) -
      homogeneousSpectralWKBLog ((h : ℂ)*Complex.I)
        (Complex.sqrt ((F : ℂ)+Complex.I*(gamma : ℂ)))
        ((g : ℂ)/(2*Complex.sqrt ((F : ℂ)+Complex.I*(gamma : ℂ))))‖ / Real.sqrt F ≤
      (32*|gamma|+8)/E^2 := by
  have hFp : 0 < F := (by positivity : 0 < E^2/32).trans_le hF
  have hS : 0 < Real.sqrt F := Real.sqrt_pos.mpr hFp
  have hSq := Real.sq_sqrt hFp.le
  have hSlo : E/8 ≤ Real.sqrt F := by
    apply (sq_le_sq₀ (by positivity : 0 ≤ E/8) hS.le).mp
    nlinarith [sq_nonneg E]
  have hγ : |gamma|/Real.sqrt F/Real.sqrt F ≤ 32*|gamma|/E^2 := by
    calc
      _ = |gamma|/F := by rw [div_div,← sq,hSq]
      _ ≤ |gamma|/(E^2/32) := div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hF
      _ = _ := by ring
  have hg' : |g|/(4*F) ≤ 1/E := by
    apply (div_le_iff₀ (by positivity : 0 < 4*F)).mpr
    exact hg.trans_eq (by ring)
  have hrem : (1/E)/Real.sqrt F ≤ 8/E^2 := by
    calc
      _ ≤ (1/E)/(E/8) := div_le_div_of_nonneg_left (by positivity) (by positivity) hSlo
      _ = _ := by ring
  calc
    _ ≤ (|gamma|/Real.sqrt F+|g|/(4*F))/Real.sqrt F :=
      div_le_div_of_nonneg_right (spectralWKB_oscillatory_slope_error h F gamma g hh hFp) hS.le
    _ = |gamma|/Real.sqrt F/Real.sqrt F + (|g|/(4*F))/Real.sqrt F := add_div _ _ _
    _ ≤ 32*|gamma|/E^2 + (1/E)/Real.sqrt F :=
      add_le_add hγ (div_le_div_of_nonneg_right hg' hS.le)
    _ ≤ 32*|gamma|/E^2 + 8/E^2 := add_le_add le_rfl hrem
    _ = _ := by ring

end DefocusingNLS

end OAI

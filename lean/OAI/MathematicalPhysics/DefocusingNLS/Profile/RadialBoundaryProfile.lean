import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialBoundaryGap
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialBoundaryGeometry

namespace OAI

/-! Existence of the actual free boundary data with the manuscript's strict modulus gap. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem exists_radial_boundary_profile (b Z : ℝ)
    (hb : b ∈ Icc (334/1000 : ℝ) (335/1000))
    (hZ : |Z-(ProfileCertificate.centerZ : ℝ)| ≤ (1/100000000 : ℝ)) :
    ∃ F G : ℝ → ℂ, Continuous F ∧ Continuous G ∧
      (∀ r ∈ Icc (2*Real.sqrt Z) innerBoundaryRadius,
        F r=1+∫ t in (2*Real.sqrt Z)..r, G t) ∧
      (∀ r ∈ Icc (2*Real.sqrt Z) innerBoundaryRadius,
        G r=∫ t in (2*Real.sqrt Z)..r, -radialFreeCoefficient t*G t-(b : ℂ)*F t) ∧
      1-(1/5 : ℝ)*(1/10000)^2 < ‖F innerBoundaryRadius‖ ∧
      ‖F innerBoundaryRadius‖ < 1-(3/20 : ℝ)*(1/10000)^2 := by
  obtain ⟨hl,hu,hshell⟩ := radial_boundary_shell_geometry Z hZ
  have hlu : 2*Real.sqrt Z ≤ innerBoundaryRadius := by linarith [hshell.1]
  have hwidth : innerBoundaryRadius-2*Real.sqrt Z ≤ (1/1000 : ℝ) := by
    linarith [hshell.2]
  obtain ⟨F,G,hF,hG,heF,heG,hB⟩ := exists_radial_free_components b (2*Real.sqrt Z)
    innerBoundaryRadius hb hl hu hlu hwidth
  have ht := radial_free_taylor b (2*Real.sqrt Z) innerBoundaryRadius hb hl hu hlu hwidth
    F G hF hG heF heG (fun r _ => hB r) innerBoundaryRadius ⟨hlu,le_rfl⟩
  exact ⟨F,G,hF,hG,heF,heG,radial_free_boundary_gap b _ _ hb hshell ht.2⟩

end DefocusingNLS

end OAI

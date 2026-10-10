import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.TranslatedFarTestIntegral
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalTruncatedTests

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Set

theorem inverseDistancePow_exterior_mass_translation {d : ℕ} (m : ℕ)
    (x : Ambient d) (ε : ℝ) :
    (∫ y in closedExterior x ε, inverseDistancePow (m + 1) x y) =
      ∫ h in closedExterior (0 : Ambient d) ε, inverseDistancePow (m + 1) 0 h := by
  have hp := measurePreserving_add_left (volume : Measure (Ambient d)) x
  have he := (MeasurableEquiv.addLeft x).measurableEmbedding
  have hs : (fun h => x + h) ⁻¹' closedExterior x ε = closedExterior 0 ε := by
    ext h
    simp [closedExterior, dist_eq_norm]
  have hk : ∀ h : Ambient d, inverseDistancePow (m + 1) x (x + h) = inverseDistancePow (m + 1) 0 h := by
    intro h
    simp [inverseDistancePow, dist_eq_norm]
  simpa only [hs, hk] using! (hp.setIntegral_preimage_emb he
    (inverseDistancePow (m + 1) x) (closedExterior x ε)).symm

theorem fractionalSchwartz_single_increment_integrable (p : ℕ) (ε : ℝ) (hε : 0 < ε)
    (g : 𝓢(Ambient (p + 1), ℂ)) (x : Ambient (p + 1)) :
    IntegrableOn (fun y => inverseDistancePow (p + 1 + 1) x y • (g x - g y))
      (closedExterior x ε) volume := by
  have hk := (inverseDistancePow_closedExterior_integrable_and_bound (p + 1) _ volume
    (volume_global_upper_growth (p + 1)) x ε hε).1
  have hraw := raw_far_test_kernel_integrable volume g g.integrable (p + 1) x ε hε
  have hsub := (hk.smul_const (g x)).sub hraw
  have heq : (fun y => inverseDistancePow (p + 1 + 1) x y • (g x - g y)) =
      fun y => inverseDistancePow (p + 1 + 1) x y • g x - inverseDistancePow (p + 1 + 1) x y • g y := by
    funext y
    exact smul_sub (inverseDistancePow (p + 1 + 1) x y) (g x) (g y)
  rw [heq]
  exact hsub

theorem fractionalSchwartzTruncatedTest_eq_single_increment (p : ℕ) (ε : ℝ) (hε : 0 < ε)
    (g : 𝓢(Ambient (p + 1), ℂ)) (x : Ambient (p + 1)) :
    fractionalSchwartzTruncatedTest p ε g x =
      ∫ y in closedExterior x ε, inverseDistancePow (p + 1 + 1) x y • (g x - g y) := by
  have hk := (inverseDistancePow_closedExterior_integrable_and_bound (p + 1) _ volume
    (volume_global_upper_growth (p + 1)) x ε hε).1
  have hraw := raw_far_test_kernel_integrable volume g g.integrable (p + 1) x ε hε
  have hc : IntegrableOn (fun y => inverseDistancePow (p + 1 + 1) x y • g x)
      (closedExterior x ε) := hk.smul_const (g x)
  have heq : (fun y => inverseDistancePow (p + 1 + 1) x y • (g x - g y)) =
      fun y => inverseDistancePow (p + 1 + 1) x y • g x - inverseDistancePow (p + 1 + 1) x y • g y := by
    funext y
    exact smul_sub (inverseDistancePow (p + 1 + 1) x y) (g x) (g y)
  rw [heq, integral_sub hc hraw]
  have hconst : (∫ y in closedExterior x ε, inverseDistancePow (p + 1 + 1) x y • g x) =
      (∫ h in closedExterior (0 : Ambient (p + 1)) ε, inverseDistancePow (p + 1 + 1) 0 h) • g x := by
    calc
      _ = (∫ y in closedExterior x ε, inverseDistancePow (p + 1 + 1) x y) • g x :=
        integral_smul_const _ (g x)
      _ = _ := congrArg (fun z : ℝ => z • g x)
        (inverseDistancePow_exterior_mass_translation (p + 1) x ε)
  rw [hconst]
  exact fractionalSchwartz_far_integral_identity p g x ε hε

end

end RieszRectifiability

end OAI

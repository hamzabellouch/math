import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.OpenPlaneBoxes
import OAI.Analysis.RieszRectifiability.Limits.WeakRieszInterior
import OAI.Analysis.RieszRectifiability.Limits.CorrectedLocalLimits

namespace OAI

/-!
# Interior Riesz pairings under compact-test convergence

Restricting to a ball with zero boundary mass converts compact-test convergence into
weak convergence of finite measures. Common upper growth bounds then give convergence
of the interior Riesz pairing against bounded Lipschitz tests. For compactly supported
mean-zero limit tests, a bump with nonzero integral also controls the mean correction,
so the corrected pairings converge to the original limit pairing.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem compactTestConvergence_rieszInterior_ball {d : ℕ} (p : ℕ) (C D : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    (hg : ∀ j, GlobalUpperGrowth (p + 1) C (μ j)) (hgν : GlobalUpperGrowth (p + 1) D ν)
    (hweak : CompactTestConvergence μ ν) (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (hboundary : ν (frontier (ball a R)) = 0) (hmass : ν (ball a R) ≠ 0)
    (e : Ambient d) (φ : Ambient d → ℝ) (L B : ℝ≥0)
    (hφ : LipschitzWith L φ) (hB : ∀ x, |φ x| ≤ (B : ℝ)) :
    Tendsto (fun j => ∫ q, rieszInteriorIntegrand (p + 1) e φ q
      ∂((μ j).restrict (ball a R)).prod ((μ j).restrict (ball a R))) atTop
      (𝓝 (∫ q, rieszInteriorIntegrand (p + 1) e φ q
        ∂(ν.restrict (ball a R)).prod (ν.restrict (ball a R)))) := by
  let (j : ℕ) := (hg j).finite_on_compacts
  let := hgν.finite_on_compacts
  have hcompact : IsCompact (closure (ball a R)) :=
    (isCompact_closedBall a R).of_isClosed_subset isClosed_closure
      (closure_minimal ball_subset_closedBall isClosed_closedBall)
  let μ' := fun j => relativelyCompactFiniteMeasure (μ j) (ball a R) hcompact
  let ν' := relativelyCompactFiniteMeasure ν (ball a R) hcompact
  have hweak' : Tendsto μ' atTop (𝓝 ν') :=
    compactTestConvergence_restrict_tendsto μ ν hweak (ball a R) measurableSet_ball hcompact hboundary
  have hν' : ν' ≠ 0 := by
    intro hz
    have heq := congrArg (fun ρ : FiniteMeasure (Ambient d) => (ρ : Measure (Ambient d)) univ) hz
    apply hmass
    change (ν.restrict (ball a R)) univ = (0 : Measure (Ambient d)) univ at heq
    simpa only [Measure.restrict_apply_univ, Measure.coe_zero, Pi.zero_apply] using! heq
  apply rieszInterior_integral_tendsto_of_weak p (max C D) μ' ν' hweak' hν'
    (fun j => (globalGrowth_restrict (p + 1) C (μ j) (hg j) (ball a R)).mono_constant (le_max_left _ _))
    ((globalGrowth_restrict (p + 1) D ν hgν (ball a R)).mono_constant (le_max_right _ _))
    (C * R ^ (p + 1)) (fun j => ball_restriction_mass_bound (p + 1) C (μ j) (hg j) a R hR)
    e φ L B hφ hB

theorem compactTestConvergence_corrected_rieszInterior_ball {d : ℕ} (p : ℕ) (C D : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    (hg : ∀ j, GlobalUpperGrowth (p + 1) C (μ j)) (hgν : GlobalUpperGrowth (p + 1) D ν)
    (hweak : CompactTestConvergence μ ν) (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (hboundary : ν (frontier (ball a R)) = 0) (hmass : ν (ball a R) ≠ 0)
    (e : Ambient d) (φ η : Ambient d → ℝ) (Lφ Lη Bφ Bη : ℝ≥0)
    (hφ : LipschitzWith Lφ φ) (hη : LipschitzWith Lη η)
    (hcφ : HasCompactSupport φ) (hcη : HasCompactSupport η)
    (hBφ : ∀ x, |φ x| ≤ (Bφ : ℝ)) (hBη : ∀ x, |η x| ≤ (Bη : ℝ))
    (hmean : (∫ x, φ x ∂ν) = 0) (hbump : (∫ x, η x ∂ν) ≠ 0) :
    Tendsto (fun j => ∫ q, rieszInteriorIntegrand (p + 1) e (meanCorrection (μ j) φ η) q
      ∂((μ j).restrict (ball a R)).prod ((μ j).restrict (ball a R))) atTop
      (𝓝 (∫ q, rieszInteriorIntegrand (p + 1) e φ q
        ∂(ν.restrict (ball a R)).prod (ν.restrict (ball a R)))) := by
  let (j : ℕ) := (hg j).finite_on_compacts
  let (j : ℕ) : IsFiniteMeasure ((μ j).restrict (ball a R)) :=
    finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C (μ j) (hg j) a R hR
  have hcoef := (compact_meanCorrection_admissible μ ν hweak φ η Lφ Lη Bφ Bη
    hφ hη hcφ hcη hBφ hBη hmean hbump).1
  have hlimφ := compactTestConvergence_rieszInterior_ball p C D μ ν hg hgν hweak a R hR
    hboundary hmass e φ Lφ Bφ hφ hBφ
  have hlimη := compactTestConvergence_rieszInterior_ball p C D μ ν hg hgν hweak a R hR
    hboundary hmass e η Lη Bη hη hBη
  let w := affineNormalHeight e 0 0
  have heq (ψ : Ambient d → ℝ) (q : Ambient d × Ambient d) :
      rieszInteriorIntegrand (p + 1) e ψ q = fractionalBilinear (p + 1) w ψ q.1 q.2 :=
    rieszInteriorIntegrand_eq_fractionalBilinear (p + 1) e w ψ
      (affineNormalHeight_difference e 0 0) q
  simp only [heq] at hlimφ hlimη ⊢
  apply globally_corrected_local_singular_limit (p + 1) μ (ball a R) (fun _ => w) φ η hcoef
    _ _ _ _ hlimφ hlimη
  · intro j
    have hi := (rieszInterior_integrable_and_cap_error p C ((μ j).restrict (ball a R))
      (globalGrowth_restrict (p + 1) C (μ j) (hg j) (ball a R)) e φ Lφ Bφ hφ hBφ 1 zero_lt_one).1
    change Integrable (fun q => rieszInteriorIntegrand (p + 1) e φ q) _ at hi
    simpa only [heq] using! hi
  · intro j
    have hi := (rieszInterior_integrable_and_cap_error p C ((μ j).restrict (ball a R))
      (globalGrowth_restrict (p + 1) C (μ j) (hg j) (ball a R)) e η Lη Bη hη hBη 1 zero_lt_one).1
    change Integrable (fun q => rieszInteriorIntegrand (p + 1) e η q) _ at hi
    simpa only [heq] using! hi

end

end RieszRectifiability

end OAI

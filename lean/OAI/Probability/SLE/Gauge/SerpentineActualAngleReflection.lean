import OAI.Probability.SLE.Gauge.SerpentineActualAngle
import OAI.Probability.SLE.Geometry.MarkedWitnessReflection

namespace OAI

/-! Reflection removes the sign restriction on the marked point, with
exactly the same uniform angle constant as the right-hand experiment. -/

noncomputable section
open Set Filter Metric ComplexConjugate
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Serpentine
open RibbonCoordinates FirstFrontPassage Target

theorem uniform_serpentine_actual_angle
    (hopen : PublishedPlanarDiskOpenness)
    (hstraight : PublishedHalfPlaneCrosscutStraightening)
    (hexit : PublishedHalfPlaneConformalExitLaw)
    (hsupport : PublishedPlanarWienerUnitSupport) (W : WienerLaw) (hW : IsWiener W)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ)
      (G F : ℝ≥0 → ℂ → ℂ), IsCapacityTwoWitness U γ G F → Continuous U →
      ∀ w : ℂ, ‖w‖ ≤ 1 → s ≤ w.im →
      ∀ m : ℕ, 0 < m → ∀ g : C(ℂ, ℝ),
      (∀ z ∈ closedRibbon, g (physicalExperimentChart s w m z) = z.re) →
      ∀ ε : ℝ, ε ≤ 1 / 8 →
      () ∈ GoodRibbonPrefix (fun _ : Unit => γ)
        (fun _ => firstFrontTime (fun t => g (γ t)) (fitCompletion s w m))
        (physicalExperimentChart s w m) ε →
      let T := (firstFrontTime (fun t => g (γ t)) (fitCompletion s w m)).untopD 0
      s₀ ≤ (G T w - (U T : ℂ)).im / ‖G T w - (U T : ℂ)‖ := by
  obtain ⟨s₀, hs₀, hangle⟩ :=
    uniform_serpentine_actual_angle_nonneg hopen hstraight hexit hsupport W hW hs hs1
  refine ⟨s₀, hs₀, ?_⟩
  intro U γ G F hw hU w hwn hwy m hm g hg ε hε hpref
  by_cases hwr : 0 ≤ w.re
  · have hchart : physicalExperimentChart s w m = physicalFitChart s w m := by
      funext z
      simp only [physicalExperimentChart, ite_eq_left hwr]
    exact hangle U γ G F hw hU w hwn hwy hwr m hm g
      (by simpa only [hchart] using hg) ε hε (by simpa only [hchart] using hpref)
  · have hwneg : w.re < 0 := lt_of_not_ge hwr
    let γ' : ℝ≥0 → ℂ := loewnerMirror ∘ γ
    let U' : ℝ≥0 → ℝ := fun t => -U t
    let G' : ℝ≥0 → ℂ → ℂ := fun t z => loewnerMirror (G t (loewnerMirror z))
    let F' : ℝ≥0 → ℂ → ℂ := fun t z => loewnerMirror (F t (loewnerMirror z))
    let g' := mirroredProgress g
    have hg' : ∀ z ∈ closedRibbon,
        g' (physicalFitChart s (loewnerMirror w) m z) = z.re := by
      intro z hz
      have hh := hg (conj z) (conj_mem_closedRibbon hz)
      rw [physicalExperimentChart_negative hwneg m] at hh
      simpa only [g', mirroredProgress, ContinuousMap.coe_mk, reflectedChart,
        Complex.conj_conj, Complex.conj_re] using hh
    have hclock : firstFrontTime (fun t => g' (γ' t))
        (fitCompletion s (loewnerMirror w) m) =
        firstFrontTime (fun t => g (γ t)) (fitCompletion s w m) := by
      rw [fitCompletion_mirror]
      exact mirroredProgress_firstFrontTime g γ _
    have hpref' : () ∈ GoodRibbonPrefix (fun _ : Unit => γ')
        (fun _ => firstFrontTime (fun t => g' (γ' t))
          (fitCompletion s (loewnerMirror w) m))
        (physicalFitChart s (loewnerMirror w) m) ε := by
      rw [hclock]
      rw [goodRibbonPrefix_physical_negative _ _ hwneg m ε] at hpref
      simpa only [γ', Function.comp_def] using hpref
    have hh := hangle U' γ' G' F' hw.mirror hU.neg (loewnerMirror w)
      (by simpa only [loewnerMirror_norm] using hwn)
      (by simpa only [loewnerMirror_im] using hwy)
      (by simp only [loewnerMirror_re]; linarith)
      m hm g' hg' ε hε hpref'
    dsimp only at hh ⊢
    rw [hclock] at hh
    simpa only [U', G', loewnerMirror_twice, mirrored_centered_sine] using hh

end SLEExactGauge.Serpentine

end

end OAI

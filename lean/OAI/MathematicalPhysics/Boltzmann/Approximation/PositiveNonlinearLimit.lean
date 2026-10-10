import OAI.MathematicalPhysics.Boltzmann.Approximation.CapWeightedNonlinearLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.WindowLocalizedSource
import OAI.MathematicalPhysics.Boltzmann.Compactness.PairRepresentative

namespace OAI

section

/-! # A compact kinetic cutoff inside the positive-time horizon lies in a slab -/

noncomputable section

open Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.TransportCutoff

theorem exists_positive_cutoff_window {U : ℝ≥0∞} (hU : 1 ≤ U)
    {χ : Published.KineticPhase → ℝ} (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ {z | 0 < z.1.1 ∧ ENNReal.ofReal z.1.1 < U}) :
    ∃ a A R : ℝ, 0 < a ∧ a ≤ A ∧ ENNReal.ofReal A < U ∧
      tsupport χ ⊆ kineticWindow a A R := by
  rcases (tsupport χ).eq_empty_or_nonempty with he | he
  · refine ⟨1/2,1/2,1,by norm_num,le_rfl,?_,?_⟩
    · exact lt_of_lt_of_le (by norm_num : ENNReal.ofReal (1/2:ℝ) < 1) hU
    · rw [he]
      exact empty_subset _
  · obtain ⟨x,hx,hmax⟩ := hc.exists_isMaxOn he continuous_fst.fst.continuousOn
    obtain ⟨a,ha,haall⟩ := hc.exists_forall_le' continuous_fst.fst.continuousOn
      (fun z hz => (hs hz).1)
    obtain ⟨R,_hR,hball⟩ := (hc.image continuous_fst.snd).isBounded.subset_ball_lt 0
      (0 : Velocity)
    refine ⟨a,x.1.1,R,ha,haall x hx,(hs hx).2,?_⟩
    intro z hz
    refine ⟨⟨⟨haall z hz,hmax hz⟩,?_⟩,mem_univ _⟩
    exact Metric.ball_subset_closedBall (hball (mem_image_of_mem (fun z : Published.KineticPhase => z.1.2) hz))

end BoltzmannNonuniqueness.TransportCutoff

end

end

section

/-! # A nonnegative representative of the actual weighted nonlinear weak limit -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem TightCapFamily.exists_positive_nonlinear_limit
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightCapFamily s₀ η K α γ d₀ q)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ), StrictMono φ ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.pairDensity
          (torusPhysical q (F.approximation (φ n)).solution.value))
        (CollisionCompactness.pairDensity g) ∧ (∀ z, 0 ≤ g z) := by
  obtain ⟨φ,g,hφ,hg,hpair,hgn⟩ := F.exists_weighted_nonlinear_weak_limit hcarleman hGLPS hDP hq₁ hq₂
  let g' : (ℝ × Position) × Velocity → ℝ := fun z => max (g z) 0
  have hm : Measurable g' := hg.1.max measurable_const
  have he : g =ᵐ[(AnnularEnvelope.timePositionVolume F.time).prod volume] g' := by
    filter_upwards [hgn] with z hz
    exact (max_eq_left hz).symm
  have hpe := CollisionCompactness.pairDensity_congr hg.1 hm he
  exact ⟨φ,g',hφ,hg.congr_limit hm he,
    hpair.congr_limit (CollisionCompactness.pairDensity_measurable hm) hpe,
    fun z => le_max_right _ _⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI

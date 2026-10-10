import OAI.Probability.StrongRayleigh.GroupBrownianPosterior
import OAI.Probability.StrongRayleigh.ObservationNoiseReal

namespace OAI

universe u_1 u_2

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336AdditiveD139.ReferenceObservation

variable {Γ : Type u_1} {W : Type u_2} [Group Γ] [Countable Γ] [DecidableEq Γ] [MeasurableSpace W]

theorem groupDrift_condExp_history
    (μ : ProbabilityMeasure (Γ → Bool)) (ν : ProbabilityMeasure W)
    (B : ℝ≥0 → W → ℝ) (hB : IsPreBrownianReal B (ν : Measure W))
    (hBm : ∀ t, Measurable (B t)) (t : ℝ≥0) (i : Γ) :
    (fun ω : Space Γ W => groupDrift μ (t : ℝ)
      (fun j => observation B j t ω) i) =ᵐ[law μ ν]
      (law μ ν)[(fun ω => boolReal (ω.1 i)) | ObservationNoise.historySigma B t] := by
  have hs : IndepFun (Prod.fst : Space Γ W → Γ → Bool)
      (fun ω (p : Γ × ℝ≥0) => noise B p.1 p.2 ω) (law μ ν) := by
    exact (signal_indep_noiseField μ ν).comp measurable_id
      (show Measurable (fun w : Γ → W => fun p : Γ × ℝ≥0 => B p.2 (w p.1)) by
        fun_prop)
  have hp := GroupBrownianPosterior.groupDrift_ae_eq_condExp (law μ ν) μ
    (noise_isPreBrownian μ ν B hB) (iid_noise_paths μ ν B hBm)
    (measurable_noise B hBm) Prod.fst measurable_fst (signal_hasLaw μ ν) hs t i
  have hspace : PosteriorLimit.observationSpace
      (fun j (s : Set.Iic t) (ω : Space Γ W) =>
        (s.1 : ℝ) * boolReal (ω.1 j) + noise B j s.1 ω) Set.univ =
      ObservationNoise.historySigma B t := by
    unfold PosteriorLimit.observationSpace ObservationNoise.historySigma ObservationNoise.history
    simp only [Set.mem_univ, iSup_true, MeasurableSpace.comap_process_pi, noise]
  rw [hspace] at hp
  exact hp

theorem groupDrift_condExp_filtration
    (μ : ProbabilityMeasure (Γ → Bool)) (ν : ProbabilityMeasure W)
    (B : ℝ≥0 → W → ℝ) (hB : IsPreBrownianReal B (ν : Measure W))
    (hBm : ∀ t, Measurable (B t)) (t : ℝ≥0) (i : Γ) :
    (fun ω : Space Γ W => groupDrift μ (t : ℝ)
      (fun j => observation B j t ω) i) =ᵐ[law μ ν]
      (law μ ν)[(fun ω => boolReal (ω.1 i)) | ObservationNoise.filtration hBm t] :=
  groupDrift_condExp_history μ ν B hB hBm t i

theorem groupDrift_condExp_realFiltration
    (μ : ProbabilityMeasure (Γ → Bool)) (ν : ProbabilityMeasure W)
    (B : ℝ≥0 → W → ℝ) (hB : IsPreBrownianReal B (ν : Measure W))
    (hBm : ∀ t, Measurable (B t)) (t : ℝ) (ht : 0 ≤ t) (i : Γ) :
    (fun ω : Space Γ W => groupDrift μ t
      (fun j => observation B j t.toNNReal ω) i) =ᵐ[law μ ν]
      (law μ ν)[(fun ω => boolReal (ω.1 i)) | ObservationNoise.realFiltration hBm t] := by
  simpa only [Real.coe_toNNReal _ ht, ObservationNoise.realFiltration_apply] using
    groupDrift_condExp_history μ ν B hB hBm t.toNNReal i

end Problem336AdditiveD139.ReferenceObservation

end

end OAI

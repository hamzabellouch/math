import OAI.Probability.SpanningForest.BorelFUSFKernel
import OAI.Probability.SpanningForest.FUSFRelabelMeasure
import OAI.Probability.SpanningForest.GraphDomain
import OAI.Probability.SpanningForest.Relabeling

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem336.BorelFUSFKernel

theorem exists_measurable_equivariant_fusf_kernel_on
    (D : Set GraphCode) (hD : MeasurableSet D)
    (hconn : ∀ G : D, GraphConnected G.1)
    (hinv : ∀ (σ : Equiv ℕ ℕ) (G : GraphCode), relabelGraph σ G ∈ D ↔ G ∈ D)
    (hex : ∀ G : D, ∃ μ : ProbabilityMeasure EdgeConfiguration,
      HasFUSFLaw G.1 (μ : Measure EdgeConfiguration) id) :
    ∃ μ : GraphCode → ProbabilityMeasure EdgeConfiguration,
      Measurable μ ∧
      (∀ G ∈ D, HasFUSFLaw G (μ G : Measure EdgeConfiguration) id) ∧
      (∀ (σ : Equiv ℕ ℕ) (G : GraphCode),
        (μ G : Measure EdgeConfiguration).map (configurationRelabel σ) =
          (μ (relabelGraph σ G) : Measure EdgeConfiguration)) := by
  classical
  obtain ⟨μ, hμm, hμ⟩ := exists_measurable_fusf_kernel_of_exists D hconn hex
  let μ₀ : ProbabilityMeasure EdgeConfiguration :=
    ⟨Measure.dirac (fun _ => false), inferInstance⟩
  let ν (G : GraphCode) := if h : G ∈ D then μ ⟨G, h⟩ else μ₀
  refine ⟨ν, Measurable.dite hμm measurable_const hD, ?_, ?_⟩
  · intro G hG
    simpa only [ν, dite_eq_left hG] using hμ ⟨G, hG⟩
  · intro σ G
    by_cases hG : G ∈ D
    · have hσG := (hinv σ G).mpr hG
      simp only [ν, dite_eq_left hG, dite_eq_left hσG]
      exact (hμ ⟨G, hG⟩).map_configurationRelabel σ (hμ ⟨_, hσG⟩)
        (BorelExhaustion.candidate_isConnectedExhaustion_of_connected (hconn ⟨G, hG⟩))
    · have hσG : relabelGraph σ G ∉ D := fun h => hG ((hinv σ G).mp h)
      simp only [ν, dite_eq_right hG, dite_eq_right hσG]
      change (Measure.dirac (fun _ : EdgeCode => false)).map
        (configurationRelabel σ) = Measure.dirac (fun _ : EdgeCode => false)
      rw [Measure.map_dirac' (configurationRelabel σ).measurable]
      rfl

theorem exists_measurable_equivariant_fusf_kernel
    (hex : ∀ G : GraphCode, GraphConnected G → GraphLocallyFinite G →
      ∃ μ : ProbabilityMeasure EdgeConfiguration,
        HasFUSFLaw G (μ : Measure EdgeConfiguration) id) :
    ∃ μ : GraphCode → ProbabilityMeasure EdgeConfiguration,
      Measurable μ ∧
      (∀ G : GraphCode, GraphConnected G → GraphLocallyFinite G →
        HasFUSFLaw G (μ G : Measure EdgeConfiguration) id) ∧
      (∀ (σ : Equiv ℕ ℕ) (G : GraphCode),
        (μ G : Measure EdgeConfiguration).map (configurationRelabel σ) =
          (μ (relabelGraph σ G) : Measure EdgeConfiguration)) := by
  obtain ⟨μ, hμm, hμ, hμeq⟩ := exists_measurable_equivariant_fusf_kernel_on
    {G : GraphCode | GraphConnected G ∧ GraphLocallyFinite G}
    measurableSet_validGraph (fun G => G.2.1)
    (fun σ G => by simp only [Set.mem_ofPred_eq, graphConnected_relabelGraph_iff,
      graphLocallyFinite_relabelGraph_iff])
    (fun G => hex G.1 G.2.1 G.2.2)
  exact ⟨μ, hμm, fun G hc hf => hμ G ⟨hc, hf⟩, hμeq⟩

end Problem336.BorelFUSFKernel

end

end OAI

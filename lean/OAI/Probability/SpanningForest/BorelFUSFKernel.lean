import OAI.Probability.SpanningForest.BorelExhaustion
import OAI.Probability.SpanningForest.CylinderKernel
import OAI.Probability.SpanningForest.GraphEncoding
import OAI.Probability.SpanningForest.FiniteUSTMeasure

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Problem336.BorelFUSFKernel

def CommonCylinderLimits (G : GraphCode)
    (p : Finset EdgeCode → Finset EdgeCode → ℝ≥0∞) : Prop :=
  ∀ H, IsConnectedExhaustion G H → ∀ A B,
    Tendsto (fun n => ustCylinder (H n) A B) atTop (𝓝 (p A B))

lemma measurable_common_cylinder_limits
    (D : Set GraphCode) (hconn : ∀ G : D, GraphConnected G.1)
    (p : D → Finset EdgeCode → Finset EdgeCode → ℝ≥0∞)
    (hp : ∀ G : D, CommonCylinderLimits G.1 (p G)) (A B : Finset EdgeCode) :
    Measurable (fun G => p G A B) := by
  apply measurable_of_tendsto_metrizable
    (f := fun n (G : D) => ustCylinder (BorelExhaustion.candidate G.1 n) A B)
  · intro n
    exact (measurable_of_countable (fun K : FiniteSubgraphCode => ustCylinder K A B)).comp
      ((BorelExhaustion.measurable_candidate n).comp measurable_subtype_coe)
  · apply tendsto_pi_nhds.mpr
    intro G
    exact hp G (BorelExhaustion.candidate G.1)
      (BorelExhaustion.candidate_isConnectedExhaustion_of_connected (hconn G)) A B

theorem exists_measurable_fusf_kernel_of_common_limits
    (D : Set GraphCode) (hconn : ∀ G : D, GraphConnected G.1)
    (p : D → Finset EdgeCode → Finset EdgeCode → ℝ≥0∞)
    (hp : ∀ G : D, CommonCylinderLimits G.1 (p G)) :
    ∃ μ : D → ProbabilityMeasure EdgeConfiguration, Measurable μ ∧
      ∀ G : D, HasFUSFLaw G.1 (μ G : Measure EdgeConfiguration) id := by
  let μn (n : ℕ) (G : D) : ProbabilityMeasure EdgeConfiguration :=
    ⟨finiteUSTMeasure (BorelExhaustion.candidate G.1 n),
      finiteUSTMeasure_isProbabilityMeasure _
        (FiniteEncoding.spanningTrees_nonempty
          ((BorelExhaustion.candidate_isConnectedExhaustion_of_connected (hconn G)).1 n))⟩
  obtain ⟨μ, hμm, hμ⟩ :=
    CylinderKernel.exists_measurable_probabilityMeasure_of_cylinder_limits μn p
      (measurable_common_cylinder_limits D hconn p hp) (by
        intro G A B
        have h := hp G (BorelExhaustion.candidate G.1)
          (BorelExhaustion.candidate_isConnectedExhaustion_of_connected (hconn G)) A B
        change Tendsto
          (fun n => finiteUSTMeasure (BorelExhaustion.candidate G.1 n) (edgeCylinder A B))
          atTop (𝓝 (p G A B))
        simpa only [finiteUSTMeasure_edgeCylinder] using h)
  refine ⟨μ, hμm, fun G => ?_⟩
  constructor
  · intro e
    exact measurable_pi_apply e
  · intro H hH A B
    change Tendsto (fun n => ustCylinder (H n) A B) atTop
      (𝓝 ((μ G : Measure EdgeConfiguration) (CylinderKernel.cylinder A B)))
    rw [hμ G A B]
    exact hp G H hH A B

theorem exists_measurable_fusf_kernel
    (D : Set GraphCode) (hconn : ∀ G : D, GraphConnected G.1)
    (hlimits : ∀ G : D, ∃ p, CommonCylinderLimits G.1 p) :
    ∃ μ : D → ProbabilityMeasure EdgeConfiguration, Measurable μ ∧
      ∀ G : D, HasFUSFLaw G.1 (μ G : Measure EdgeConfiguration) id := by
  choose p hp using hlimits
  exact exists_measurable_fusf_kernel_of_common_limits D hconn p hp

theorem exists_measurable_fusf_kernel_of_exists
    (D : Set GraphCode) (hconn : ∀ G : D, GraphConnected G.1)
    (hex : ∀ G : D, ∃ μ : ProbabilityMeasure EdgeConfiguration,
      HasFUSFLaw G.1 (μ : Measure EdgeConfiguration) id) :
    ∃ μ : D → ProbabilityMeasure EdgeConfiguration, Measurable μ ∧
      ∀ G : D, HasFUSFLaw G.1 (μ G : Measure EdgeConfiguration) id := by
  apply exists_measurable_fusf_kernel D hconn
  intro G
  obtain ⟨μ, hμ⟩ := hex G
  refine ⟨fun A B => (μ : Measure EdgeConfiguration) (edgeCylinder A B), ?_⟩
  exact hμ.2

theorem exists_measurable_fusf_kernel_global
    (D : Set GraphCode) (hD : MeasurableSet D)
    (hconn : ∀ G : D, GraphConnected G.1)
    (hlimits : ∀ G : D, ∃ p, CommonCylinderLimits G.1 p) :
    ∃ μ : GraphCode → ProbabilityMeasure EdgeConfiguration, Measurable μ ∧
      ∀ G ∈ D, HasFUSFLaw G (μ G : Measure EdgeConfiguration) id := by
  classical
  obtain ⟨μ, hμm, hμ⟩ := exists_measurable_fusf_kernel D hconn hlimits
  let μ₀ : ProbabilityMeasure EdgeConfiguration :=
    ⟨Measure.dirac (fun _ => false), inferInstance⟩
  let μ' (G : GraphCode) := if h : G ∈ D then μ ⟨G, h⟩ else μ₀
  refine ⟨μ', ?_, ?_⟩
  · exact Measurable.dite hμm measurable_const hD
  · intro G hG
    simpa only [μ', dite_eq_left hG] using hμ ⟨G, hG⟩

end Problem336.BorelFUSFKernel

end

end OAI

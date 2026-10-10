import OAI.Probability.SpanningForest.USTDeterminant
import OAI.Probability.SpanningForest.FUSFExistenceReduction
import OAI.Probability.SpanningForest.ExhaustionExistence
import OAI.Probability.SpanningForest.EquivariantFUSFKernel

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Problem336.GraphLaw

theorem positive_cylinders_tendsto {G : GraphCode}
    {H : ℕ → FiniteSubgraphCode} (hH : IsConnectedExhaustion G H)
    (A : Finset EdgeCode) :
    Tendsto (fun n => ustCylinder (H n) A ∅) atTop
      (𝓝 (ENNReal.ofReal (Matrix.det
        (fun e f : A => FreeKernel.kernelEntry G e.val f.val)))) := by
  classical
  simp_rw [FreeKernel.ustCylinder_positive_eq_finiteKernel_det (hH.1 _)]
  exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (FreeKernel.finiteKernel_edge_minor_tendsto hH (fun e : A => e.val))

theorem exists_fusf_probability (G : GraphCode) (hG : GraphConnected G) :
    ∃ μ : ProbabilityMeasure EdgeConfiguration,
      HasFUSFLaw G (μ : Measure EdgeConfiguration) id := by
  classical
  obtain ⟨H, hH⟩ := hG.exists_connected_exhaustion
  exact exists_hasFUSFLaw_of_inclusion_limits G H hH
    (fun A => ENNReal.ofReal (Matrix.det
      (fun e f : A => FreeKernel.kernelEntry G e.val f.val)))
    (fun _ hH' A => positive_cylinders_tendsto hH' A)

theorem exists_equivariant_fusf_kernel :
    ∃ μ : GraphCode → ProbabilityMeasure EdgeConfiguration,
      Measurable μ ∧
      (∀ G, GraphConnected G → GraphLocallyFinite G →
        HasFUSFLaw G (μ G : Measure EdgeConfiguration) id) ∧
      (∀ (σ : Equiv ℕ ℕ) (G : GraphCode),
        (μ G : Measure EdgeConfiguration).map (configurationRelabel σ) =
          (μ (relabelGraph σ G) : Measure EdgeConfiguration)) :=
  BorelFUSFKernel.exists_measurable_equivariant_fusf_kernel
    (fun G hG _ => exists_fusf_probability G hG)

end Problem336.GraphLaw

end

end OAI

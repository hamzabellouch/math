import OAI.Analysis.LipschitzHilbert.Phase.FiniteDiagonalBandL1
import OAI.Analysis.LipschitzHilbert.Fourier.AnnularBandL1
import OAI.Analysis.LipschitzHilbert.Estimates.L1MultiplierDominatedLimit
import OAI.Analysis.LipschitzHilbert.Estimates.AmplitudeApproximationL1

namespace OAI

/-! Finite diagonal forms converge under the actual amplitude
exhaustion. This removes all amplitude cutoffs without an L2 continuity
assumption on the operator being estimated. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketRepresentation

variable {κ : Type} [Fintype κ]

theorem vector_coordinate_integrable (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hfm : Measurable f) (hf1 : Integrable f planeMeasure) (k : κ) :
    Integrable (fun z => f z k) planeMeasure := by
  apply hf1.norm.mono'
    (((measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hfm)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun z => PiLp.norm_apply_le (f z) k)

theorem finiteDiagonalBand_amplitude_limit {N : ℕ}
    (psi beta : SchwartzMap ℝ ℂ) (topLength width M B U : ℝ)
    (htop : 0<topLength) (hwidth : 0<width)
    (hpsi : ∀ s, psi s≠0 → |s|≤M) (hbeta : ∀ s, beta s≠0 → |s|≤B)
    (center : κ → ℝ) (u : ℝ×ℝ → ℝ) (hum : Measurable u) (hu : ∀ z, |u z|≤U)
    (f g : ℝ×ℝ → EuclideanSpace ℂ κ) (hfm : Measurable f) (hgm : Measurable g)
    (hf1 : Integrable f planeMeasure) (hg1 : Integrable g planeMeasure)
    (hf2 : MemLp f 2 planeMeasure) (hg2 : MemLp g 2 planeMeasure) :
    Tendsto (fun n : ℕ => finiteDiagonalBandL1 (N:=N) psi beta topLength width center u
      (fun k z => amplitudeApprox f
        ((Finset.Icc (-(n:ℤ)) n).filter (fun i => 0<planeMeasure.real (amplitudeLevel f i))) z k)
      (amplitudeApprox g ((Finset.Icc (-(n:ℤ)) n).filter (fun j => 0<planeMeasure.real (amplitudeLevel g j)))))
      atTop (𝓝 (finiteDiagonalBandL1 (N:=N) psi beta topLength width center u (fun k z => f z k) g)) := by
  classical
  have hU : 0≤U := (abs_nonneg (u 0)).trans (hu 0)
  unfold finiteDiagonalBandL1
  apply tendsto_finsetSum
  intro s _
  apply tendsto_finsetSum
  intro k _
  obtain ⟨q,hq,hbound⟩ := exists_annularBandSymbol_envelope psi beta
    (topLength/(2:ℝ)^s.val) width (center k) M B U
    (div_pos htop (pow_pos (by norm_num) _)) hwidth hU hpsi hbeta u hu
  apply variableFrequencyMultiplier_pairing_tendsto_dominated _
    (annularBandSymbol_measurable psi beta _ width (center k) u hum) q hq hbound
  · exact vector_coordinate_integrable f hfm hf1 k
  · exact vector_coordinate_integrable g hgm hg1 k
  · intro n
    exact vector_coordinate_integrable _ (amplitudeApprox_measurable hfm _)
      (amplitudeApprox_integrable planeMeasure f hfm hf1 _) k
  · intro n
    exact vector_coordinate_integrable _ (amplitudeApprox_measurable hgm _)
      (amplitudeApprox_integrable planeMeasure g hgm hg1 _) k
  · intro n
    exact Filter.Eventually.of_forall (fun z => amplitudeApprox_coordinate_norm_le f _ z k)
  · intro n
    exact Filter.Eventually.of_forall (fun z => amplitudeApprox_coordinate_norm_le g _ z k)
  · filter_upwards [amplitudeApprox_positive_tendsto_ae planeMeasure f hf2] with z hz
    exact (PiLp.continuous_apply 2 (fun _ : κ => ℂ) k).continuousAt.tendsto.comp hz
  · filter_upwards [amplitudeApprox_positive_tendsto_ae planeMeasure g hg2] with z hz
    exact (PiLp.continuous_apply 2 (fun _ : κ => ℂ) k).continuousAt.tendsto.comp hz

end LipschitzHilbert.PacketRepresentation

end

end OAI

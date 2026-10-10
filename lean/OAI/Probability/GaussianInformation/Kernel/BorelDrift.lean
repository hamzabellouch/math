import Mathlib
import OAI.Probability.GaussianInformation.Kernel.ContinuousDrift

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.NoisyDrift
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open Projection Projection.Support GaussianTools ReferenceGaussian Noise Bayes DriftTools.FiniteReference EntropySupport Coercivity

lemma positive_borel_bound {d N : ℕ} (hd : 16 ≤ d) (hN : 0 < N)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] {H : ℝ} (hH : 1 ≤ H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d) (rule : PositiveRule (d/16) d N) :
    (∑ w,mass ν (rule.exactResponse w)*Phi (post ν (rule.exactResponse w))) ≤
      Phi ν+95*(d:ℝ)+6*Real.log H/(d:ℝ)+2*Real.log (N:ℝ)/(d:ℝ)+Real.log (N:ℝ)/(d/16:ℕ) := by
  have : IsProbabilityMeasure (gaussianRows (d/16) d) := by unfold gaussianRows; infer_instance
  let T : Ambient d × Mat (d/16) d → Mat (d/16) d × (Fin (d/16) → ℝ) := fun z => (z.2,projectVector z.2 z.1)
  have hT : Measurable T := measurable_snd.prodMk ((continuous_projectVector.comp (continuous_snd.prodMk continuous_fst)).measurable)
  let μ := (ν.prod (gaussianRows (d/16) d)).map T
  have : IsProbabilityMeasure μ := by infer_instance
  obtain ⟨R,hR,hRl,hconv⟩ := rule.exists_continuous_approx hN μ
  have hæ := Measure.ae_ae_of_ae_prod (ae_of_ae_map hT.aemeasurable hconv)
  have he (w : Fin N) : ∀ᵐ s ∂ν,Tendsto (fun n => (R n).exactResponse w s) atTop (𝓝 (rule.exactResponse w s)) := by
    filter_upwards [hæ] with s hs
    apply tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ))
    · intro n
      exact ((R n).measurable w |>.comp (measurable_id.prodMk ((continuous_projectVector.comp (continuous_id.prodMk continuous_const)).measurable))).aestronglyMeasurable
    · exact integrable_const 1
    · intro n
      filter_upwards [] with X
      rw [Real.norm_eq_abs,abs_of_nonneg ((R n).nonneg _ _)]
      exact (R n).le_one _ _
    · filter_upwards [hs] with X hX
      exact hX w
  have heps : 0 < rule.lower/(N:ℝ) := div_pos rule.lower_pos (by exact_mod_cast hN)
  have hconvPhi (w : Fin N) := tendsto_weighted_Phi_positive hd ν (lt_of_lt_of_le zero_lt_one hH) hν
    (fun n => (R n).exactResponse w) (rule.exactResponse w)
    (fun n => (R n).measurable_exactResponse w) (rule.measurable_exactResponse w) heps
    (fun n s => by rw [← hRl n]; exact ((R n).exactResponse_bounds w s).1)
    (fun s => (div_le_self rule.lower_pos.le (by exact_mod_cast hN)).trans (rule.exactResponse_bounds w s).1)
    (fun n s => ((R n).exactResponse_bounds w s).2) (fun s => (rule.exactResponse_bounds w s).2) (he w)
  exact le_of_tendsto_of_tendsto' (tendsto_finsetSum _ (fun w _ => hconvPhi w)) tendsto_const_nhds
    (fun n => positive_continuous_bound hd hN ν hH hν (R n) (hR n))

end KernelPotential.NoisyDrift

end OAI

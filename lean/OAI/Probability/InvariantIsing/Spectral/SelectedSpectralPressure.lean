import OAI.Probability.InvariantIsing.Spectral.SelectedCompactPressure
import OAI.Probability.InvariantIsing.Spectral.SpectralExcess

namespace OAI

/-! No-outlier spectral pressure along selected dimensions, used in the
subsequence proof of convergence in probability. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology
namespace InvariantIsing

lemma selected_clip_empirical_tendsto
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (eig : (k : ℕ) → Fin (N k) → ℝ)
    (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (hN k) (eig k)) atTop (𝓝 ν)) :
    Tendsto (fun k => empiricalSpectralLaw (hN k) (fun i => spectralClip a b (eig k i)))
      atTop (𝓝 ν) := by
  have he : ν.map (spectralClip a b)=ν := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_map]
    have h : spectralClip a b =ᵐ[(ν : Measure ℝ)] id := by
      filter_upwards [(ν : Measure ℝ).support_mem_ae] with x hx
      exact spectralClip_eq (hbound hx)
    rw [Measure.map_congr h,Measure.map_id]
  have hh := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ ν hweak
    (continuous_spectralClip a b)
  rw [he] at hh
  apply hh.congr
  intro k
  apply ProbabilityMeasure.toMeasure_injective
  exact empiricalSpectralLaw_map _ _ _ (continuous_spectralClip a b).measurable

theorem selected_spectral_pressure_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant]
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop)
    (eig : (k : ℕ) → Fin (N k) → ℝ) (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hno : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ i, a-ε ≤ eig k i ∧ eig k i ≤ b+ε)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (hN k) (eig k)) atTop (𝓝 ν)) :
    Tendsto (fun k => ∫ V, rotatedPressure (eig k) (matrixRotation V⁻¹) (fun _ => 0) ∂μ (N k))
      atTop (𝓝 (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) := by
  have hab : a ≤ b := (hbound ha).2
  have hc := selected_compact_pressure_tendsto hhaar hgauss hpub μ N hN hNlim
    (fun k i => spectralClip a b (eig k i)) ν a b hcompact hbound ha hb
    (fun k i => spectralClip_mem hab (eig k i))
    (selected_clip_empirical_tendsto N hN eig ν a b hbound hweak)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp hc (ε/2) (by positivity),
    hno (ε/2) (by positivity)] with k hk he
  have hd := spectral_clip_mean_pressure_close (hN k) (μ (N k)) (eig k) a b (ε/2)
    hab (by positivity) he
  rw [Real.dist_eq] at hk ⊢
  rw [abs_sub_comm] at hd
  exact (abs_sub_le _ _ _).trans_lt (add_lt_add_of_le_of_lt hd hk) |>.trans_le (by linarith)

end InvariantIsing

end

end OAI

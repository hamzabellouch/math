import OAI.Analysis.PlanarEndpoint.Fourier

namespace OAI

/-! Gaussian regularization, Fourier evolution and endpoint maximal estimates. -/


noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
namespace PlanarEndpoint

lemma memLp_comp_real_smul {v : Plane → ℂ} (hv : MemLp v 2 volume)
    {r : ℝ} (hr : r ≠ 0) : MemLp (fun ξ : Plane => v (r • ξ)) 2 volume := by
  have h := hv.smul_measure
    (c := ENNReal.ofReal |(r ^ Module.finrank ℝ Plane)⁻¹|) ENNReal.ofReal_ne_top
  rw [← Measure.map_addHaar_smul (volume : Measure Plane) hr] at h
  exact h.comp_of_map (measurable_const_smul _).aemeasurable

def inverseFrequency (v : Plane → ℂ) (hv : MemLp v 2 volume) : L2 :=
  (Lp.fourierTransformₗᵢ Plane ℂ).symm
    ((memLp_comp_real_smul hv (by positivity : (2 * Real.pi : ℝ) ≠ 0)).toLp
      (fun ξ => v ((2 * Real.pi) • ξ)))

lemma fourier_inverseFrequency_ae (v : Plane → ℂ) (hv : MemLp v 2 volume) :
    fourier (inverseFrequency v hv) =ᵐ[volume] v := by
  have h := (memLp_comp_real_smul hv (by positivity : (2 * Real.pi : ℝ) ≠ 0)).coeFn_toLp
  have hh := (Measure.quasiMeasurePreserving_smul volume
    (r := (2 * Real.pi)⁻¹) (by positivity)).ae_eq_comp h
  filter_upwards [hh] with ξ hξ
  simpa only [fourier, inverseFrequency, LinearIsometryEquiv.apply_symm_apply,
    Function.comp_apply, smul_smul, mul_inv_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0),
    one_smul] using hξ

lemma inverseFrequency_norm (v : Plane → ℂ) (hv : MemLp v 2 volume) :
    (2 * Real.pi) * ‖inverseFrequency v hv‖ = ‖hv.toLp v‖ := by
  have h := fourier_energy (inverseFrequency v hv)
  have he : (∫ ξ, ‖fourier (inverseFrequency v hv) ξ‖^2) = ∫ ξ, ‖v ξ‖^2 :=
    integral_congr_ae ((fourier_inverseFrequency_ae v hv).fun_comp (fun z : ℂ => ‖z‖^2))
  rw [he] at h
  have ht : (∫ ξ, ‖v ξ‖^2) = ‖hv.toLp v‖^2 := by
    calc
      _ = ∫ ξ, ‖(hv.toLp v) ξ‖^2 := integral_congr_ae
        ((hv.coeFn_toLp).symm.fun_comp (fun z : ℂ => ‖z‖^2))
      _ = ‖hv.toLp v‖^2 := by rw [← real_inner_self_eq_norm_sq]; simp only [L2.inner_def, real_inner_self_eq_norm_sq]
  rw [ht] at h
  have hn : 0 ≤ (2 * Real.pi) * ‖inverseFrequency v hv‖ := by positivity
  nlinarith [norm_nonneg (hv.toLp v)]

def frequencyExtension (v : Plane → ℂ) (x : Plane) (t : ℝ) : ℂ :=
  ∫ ξ, phase x t ξ * v ξ

lemma evolution_inverseFrequency (v : Plane → ℂ) (hv : MemLp v 2 volume)
    (x : Plane) (t : ℝ) :
    evolution (inverseFrequency v hv) x t =
      (((2 * Real.pi)^2)⁻¹ : ℝ) • frequencyExtension v x t := by
  unfold evolution frequencyExtension
  congr 1
  apply integral_congr_ae
  filter_upwards [fourier_inverseFrequency_ae v hv] with ξ hξ
  rw [hξ]

lemma continuous_frequencyExtension {v : Plane → ℂ} (hv : Integrable v volume) :
    Continuous (fun z : Plane × ℝ => frequencyExtension v z.1 z.2) := by
  apply continuous_iff_continuousAt.2
  intro z
  apply continuousAt_of_dominated (bound := fun ξ => ‖v ξ‖)
  · exact Eventually.of_forall (fun w => ((continuous_phase w.1 w.2).aestronglyMeasurable.mul hv.aestronglyMeasurable))
  · exact Eventually.of_forall (fun w => Eventually.of_forall (fun ξ => by simp))
  · exact hv.norm
  · filter_upwards [] with ξ
    exact (continuous_phase_parameters ξ).mul_const (v ξ) |>.continuousAt

lemma norm_frequencyExtension (v : Plane → ℂ) (hv : MemLp v 2 volume)
    (x : Plane) (t : ℝ) : ‖frequencyExtension v x t‖ =
      (2 * Real.pi)^2 * ‖evolution (inverseFrequency v hv) x t‖ := by
  rw [evolution_inverseFrequency, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < ((2 * Real.pi)^2)⁻¹)]
  field_simp

lemma frequency_weak_of_shortTime {c₀ C₀ p : ℝ}
    (h : ShortTimeWeakEstimate c₀ C₀ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, ∀ (v : Plane → ℂ) (hv : MemLp v 2 volume),
      (∀ᵐ ξ : Plane ∂volume, ξ ∉ {ξ | c₀ * (2:ℝ)^j ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ C₀*(2:ℝ)^j} → v ξ = 0) →
      ∀ (x₀ : Plane) (t₀ s lam : ℝ), 0 ≤ s → s ≤ ((2:ℝ)^j)⁻¹ → 0 < lam →
      volume (Metric.ball x₀ 1 ∩ {x | ∃ t ∈ Icc t₀ (t₀+s), lam < ‖frequencyExtension v x t‖}) ≤
        ENNReal.ofReal ((C * ((2:ℝ)^j)^(1/3:ℝ) * ‖hv.toLp v‖ / lam)^p) := by
  obtain ⟨C,hC,h⟩ := h
  refine ⟨(2*Real.pi)*C, mul_pos (by positivity) hC, ?_⟩
  intro j v hv hs x₀ t₀ s lam hs0 hs1 hlam
  let f := inverseFrequency v hv
  have hf : AnnularFourierSupport f c₀ C₀ ((2:ℝ)^j) := by
    filter_upwards [fourier_inverseFrequency_ae v hv, hs] with ξ hξ hsξ
    rw [hξ]
    exact hsξ
  have he : (Metric.ball x₀ 1 ∩ {x | ∃ t ∈ Icc t₀ (t₀+s), lam < ‖frequencyExtension v x t‖}) =
      shortTimeLevel f x₀ t₀ s (lam / (2*Real.pi)^2) := by
    ext x
    simp only [shortTimeLevel, mem_inter_iff, mem_ofPred_eq]
    apply and_congr_right'
    congr! 2 with t
    rw [norm_frequencyExtension, div_lt_iff₀ (by positivity : 0 < (2 * Real.pi)^2)]
    dsimp [f]
    rw [mul_comm]
  rw [he]
  convert h j f hf x₀ t₀ s hs0 hs1 (lam/(2*Real.pi)^2) (by positivity) using 2
  congr 1
  rw [← inverseFrequency_norm v hv]
  dsimp [f]
  field_simp

end PlanarEndpoint
end

end OAI

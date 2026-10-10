import OAI.Analysis.PlanarEndpoint.Fourier
import OAI.Analysis.PlanarEndpoint.FrequencyWeak
import OAI.Analysis.PlanarEndpoint.GraphScaling
import OAI.Analysis.PlanarEndpoint.GraphTree

namespace OAI

/-! Gaussian regularization, Fourier evolution and endpoint maximal estimates. -/


noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace PlanarEndpoint

def unitFrequencyInput (f : L2) (N t₀ : ℝ) (η : Plane) : ℂ :=
  (N : ℂ) * (phase 0 t₀ (N • η) * fourier f (N • η))

lemma unitFrequencyInput_memLp (f : L2) {N : ℝ} (hN : 0 < N) (t₀ : ℝ) :
    MemLp (unitFrequencyInput f N t₀) 2 volume := by
  have hv := memLp_comp_real_smul (fourier_memLp f) hN.ne'
  apply (hv.const_mul (N : ℂ)).of_le
  · exact aestronglyMeasurable_const.mul
      (((continuous_phase 0 t₀).comp (continuous_const_smul N)).aestronglyMeasurable.mul
        hv.aestronglyMeasurable)
  · exact Eventually.of_forall (fun η => by simp [unitFrequencyInput])

lemma norm_unitFrequencyInput (f : L2) {N : ℝ} (hN : 0 < N) (t₀ : ℝ) (η : Plane) :
    ‖unitFrequencyInput f N t₀ η‖ = N * ‖fourier f (N • η)‖ := by
  simp [unitFrequencyInput,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hN]

lemma unitFrequencyInput_support {f : L2} {c₀ C₀ N : ℝ} (hN : 0 < N)
    (hf : AnnularFourierSupport f c₀ C₀ N) (t₀ : ℝ) :
    ∀ᵐ η : Plane ∂volume,
      η ∉ {η | c₀ ≤ ‖η‖ ∧ ‖η‖ ≤ C₀} → unitFrequencyInput f N t₀ η = 0 := by
  have hh := (Measure.quasiMeasurePreserving_smul volume hN.ne').ae hf
  filter_upwards [hh] with η hη hn
  have hz : fourier f (N • η) = 0 := by
    apply hη
    intro hp
    simp only [norm_smul,Real.norm_eq_abs,abs_of_pos hN] at hp
    apply hn
    exact ⟨(mul_le_mul_iff_right₀ hN).mp (by simpa [mul_comm] using hp.1),
      (mul_le_mul_iff_left₀ hN).mp (by simpa [mul_comm] using hp.2)⟩
  simp [unitFrequencyInput,hz]

lemma unitFrequencyInput_norm (f : L2) {N : ℝ} (hN : 0 < N) (t₀ : ℝ) :
    ‖(unitFrequencyInput_memLp f hN t₀).toLp (unitFrequencyInput f N t₀)‖ =
      (2 * Real.pi) * ‖f‖ := by
  let hv := unitFrequencyInput_memLp f hN t₀
  have he : ‖hv.toLp (unitFrequencyInput f N t₀)‖^2 =
      ∫ η, ‖unitFrequencyInput f N t₀ η‖^2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [L2.inner_def,real_inner_self_eq_norm_sq]
    exact integral_congr_ae (hv.coeFn_toLp.fun_comp (fun z : ℂ => ‖z‖^2))
  simp_rw [norm_unitFrequencyInput f hN t₀,mul_pow] at he
  rw [integral_const_mul,
    Measure.integral_comp_smul_of_nonneg volume (fun ξ => ‖fourier f ξ‖^2) N (hR := hN.le)] at he
  simp only [finrank_euclideanSpace,Fintype.card_fin,smul_eq_mul] at he
  rw [← mul_assoc,mul_inv_cancel₀ (pow_ne_zero 2 hN.ne'),one_mul,fourier_energy] at he
  have hp : 0 ≤ (2 * Real.pi) * ‖f‖ := by positivity
  nlinarith [norm_nonneg (hv.toLp (unitFrequencyInput f N t₀))]

lemma phase_unitFrequency_scaling (x η : Plane) {N : ℝ} (hN : 0 < N) (t t₀ : ℝ) :
    phase (N • x) (N^2*(t-t₀)) η * phase 0 t₀ (N • η) = phase x t (N • η) := by
  have he : (inner ℝ (N • x) η - N^2*(t-t₀)*‖η‖^2) +
      (inner ℝ (0:Plane) (N • η) - t₀*‖N • η‖^2) =
        inner ℝ x (N • η) - t*‖N • η‖^2 := by
    simp only [inner_smul_left,inner_smul_right,inner_zero_left,Real.norm_eq_abs,
      starRingEnd_apply,star_trivial,norm_smul,abs_of_pos hN]
    ring
  unfold phase
  rw [← Complex.exp_add,← mul_add,← Complex.ofReal_add,he]

lemma evolution_unitFrequency_scaling (f : L2) (x : Plane) {N : ℝ}
    (hN : 0 < N) (t t₀ : ℝ) :
    evolution f x t = ((((2*Real.pi)^2)⁻¹ * N : ℝ) : ℂ) *
      frequencyExtension (unitFrequencyInput f N t₀) (N • x) (N^2*(t-t₀)) := by
  have he : frequencyExtension (unitFrequencyInput f N t₀) (N • x) (N^2*(t-t₀)) =
      (N : ℂ) * ∫ η, phase x t (N • η) * fourier f (N • η) := by
    unfold frequencyExtension unitFrequencyInput
    have hh (η : Plane) : phase (N • x) (N^2*(t-t₀)) η *
        ((N:ℂ)*(phase 0 t₀ (N • η)*fourier f (N • η))) =
          (N:ℂ)*(phase x t (N • η)*fourier f (N • η)) := by
      rw [← phase_unitFrequency_scaling x η hN t t₀]
      ring
    simp_rw [hh]
    exact integral_const_mul _ _
  rw [he]
  unfold evolution
  rw [integral_affineScale (fun ξ => phase x t ξ * fourier f ξ) 0 hN]
  simp only [affineScale,zero_add,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_pow]
  ring

lemma norm_evolution_unitFrequency_scaling (f : L2) (x : Plane) {N : ℝ}
    (hN : 0 < N) (t t₀ : ℝ) :
    ‖evolution f x t‖ = ((2*Real.pi)^2)⁻¹ * N *
      ‖frequencyExtension (unitFrequencyInput f N t₀) (N • x) (N^2*(t-t₀))‖ := by
  rw [evolution_unitFrequency_scaling f x hN t t₀,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (by positivity : 0 < ((2*Real.pi)^2)⁻¹*N)]

end PlanarEndpoint
end

end OAI

import OAI.Probability.InvariantIsing.Pressure.PressureMean
import OAI.Probability.InvariantIsing.Core.Ward

namespace OAI

/-! Temperature differentiation for the actual finite Ising pressure. -/

noncomputable section

open IsingPerceptron MeasureTheory Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma rotatedEnergy_scale {N : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (t : ℝ) (σ : Spin N) :
    rotatedEnergy (fun i => t * eig i) U σ = t * rotatedEnergy eig U σ := by
  simp only [rotatedEnergy, mul_assoc, ← Finset.mul_sum]
  ring

lemma abs_rotatedEnergy_le {N : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (K : ℝ) (heig : ∀ i, |eig i| ≤ K) (σ : Spin N) :
    |rotatedEnergy eig U σ| ≤ K * N / 2 := by
  simpa only [rotatedEnergy_constant, zero_mul, zero_div, sub_zero] using
    abs_rotatedEnergy_sub_le eig (fun _ => 0) U K (fun i => by simpa using heig i) σ

lemma GibbsReference_one {S : Type*} [Nonempty S] :
    GibbsReference (fun _ : S => (1 : ℝ)) :=
  ⟨fun _ => zero_le_one, ⟨Classical.choice inferInstance, zero_lt_one⟩⟩

def thermalPressureDerivative {N : ℕ} (eig c : Fin N → ℝ) (U : Rotation N) (t : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * gibbsAverage (fun _ => 1)
    (fun σ => t * rotatedEnergy eig U σ + fieldEnergy c σ) (rotatedEnergy eig U)

lemma hasDerivAt_rotatedPressure_temperature {N : ℕ} (eig c : Fin N → ℝ)
    (U : Rotation N) (t : ℝ) :
    HasDerivAt (fun s => rotatedPressure (fun i => s * eig i) U c)
      (thermalPressureDerivative eig c U t) t := by
  have hd := (hasDerivAt_log_finitePartition GibbsReference_one
    (fun σ : Spin N => ((hasDerivAt_id t).mul_const
      (rotatedEnergy eig U σ)).add_const (fieldEnergy c σ))).sub_const
    (Real.log (Fintype.card (Spin N)))
  have he : (fun s => Real.log (finitePartition (fun _ : Spin N => 1)
      (fun σ => s * rotatedEnergy eig U σ + fieldEnergy c σ)) -
        Real.log (Fintype.card (Spin N))) =
      (fun s => logPartition (fun σ => rotatedEnergy (fun i => s * eig i) U σ + fieldEnergy c σ)) := by
    funext s
    rw [logPartition_eq]
    simp only [finitePartition, one_mul, rotatedEnergy_scale]
  simp only [id_eq, one_mul] at hd
  rw [he] at hd
  exact hd.const_mul (N : ℝ)⁻¹

lemma abs_thermalPressureDerivative_le {N : ℕ} (hN : 0 < N)
    (eig c : Fin N → ℝ) (U : Rotation N) (K : ℝ)
    (heig : ∀ i, |eig i| ≤ K) (t : ℝ) :
    |thermalPressureDerivative eig c U t| ≤ K / 2 := by
  have hb := abs_gibbsAverage_le GibbsReference_one
    (fun σ => t * rotatedEnergy eig U σ + fieldEnergy c σ) (rotatedEnergy eig U)
    (abs_rotatedEnergy_le eig U K heig)
  unfold thermalPressureDerivative
  rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (N : ℝ)⁻¹ by positivity)]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  calc
    _ ≤ (N : ℝ)⁻¹ * (K * N / 2) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = K / 2 := by field_simp

lemma measurable_thermalPressureDerivative {N : ℕ} (eig c : Fin N → ℝ) (t : ℝ) :
    Measurable (fun V : SpecialOrthogonal N => thermalPressureDerivative eig c (specialRotation V) t) := by
  have hE (σ : Spin N) : Measurable (fun V : SpecialOrthogonal N =>
      rotatedEnergy eig (specialRotation V) σ) :=
    (Finset.measurable_sum _ fun i _ =>
      ((measurable_specialRotation_eval (spinVector σ) i).pow_const 2).const_mul (eig i)).const_mul _
  exact (measurable_gibbsAverage (fun _ => 1) _ _
    (fun σ => ((hE σ).const_mul t).add_const _) hE).const_mul _

/-- Differentiation commutes with the disorder expectation. The bound is
uniform in the field and does not require Haar invariance. -/
theorem hasDerivAt_mean_pressure_temperature {N : ℕ} (hN : 0 < N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → SpecialOrthogonal N) (hU : Measurable U)
    (eig c : Fin N → ℝ) (K : ℝ) (heig : ∀ i, |eig i| ≤ K) (t : ℝ) :
    HasDerivAt (fun s => ∫ ω, rotatedPressure (fun i => s * eig i) (specialRotation (U ω)) c ∂P)
      (∫ ω, thermalPressureDerivative eig c (specialRotation (U ω)) t ∂P) t := by
  have hm (s : ℝ) : Measurable (fun ω =>
      rotatedPressure (fun i => s * eig i) (specialRotation (U ω)) c) :=
    (measurable_rotatedPressure _ c).comp hU
  have hi : Integrable (fun ω =>
      rotatedPressure (fun i => t * eig i) (specialRotation (U ω)) c) P := by
    have hb (ω : Ω) : |rotatedPressure (fun i => t * eig i) (specialRotation (U ω)) c| ≤
        |t| * K / 2 + |noninteractingPressure c| := by
      have he : ∀ i, |t * eig i| ≤ |t| * K := fun i => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (heig i) (abs_nonneg _)
      have h := abs_pressure_sub_noninteracting_le hN _ c (specialRotation (U ω)) (|t| * K) he
      have hs := abs_add_le (rotatedPressure (fun i => t * eig i) (specialRotation (U ω)) c -
        noninteractingPressure c) (noninteractingPressure c)
      rw [sub_add_cancel] at hs
      exact hs.trans (add_le_add h le_rfl)
    exact (integrable_const _).mono' (hm t).aestronglyMeasurable
      (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hb ω)
  obtain ⟨_, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by linarith : t - 1 < t) (by linarith : t < t + 1))
    (Filter.Eventually.of_forall fun s => (hm s).aestronglyMeasurable) hi
    ((measurable_thermalPressureDerivative eig c t).comp hU).aestronglyMeasurable
    (ae_of_all _ fun ω s _ => by
      simpa only [Real.norm_eq_abs] using
        abs_thermalPressureDerivative_le hN eig c (specialRotation (U ω)) K heig s)
    (integrable_const (K / 2))
    (ae_of_all _ fun ω s _ => hasDerivAt_rotatedPressure_temperature eig c (specialRotation (U ω)) s)
  exact hd

end InvariantIsing

end

end OAI

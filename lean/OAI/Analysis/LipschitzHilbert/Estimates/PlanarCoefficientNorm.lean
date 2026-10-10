import OAI.Analysis.LipschitzHilbert.Packets.PlanarPacketFamily
import OAI.Analysis.LipschitzHilbert.Packets.AnalyzingCoefficientNorm

namespace OAI

/-! Uniform pointwise normalization of the actual main coefficients,
with no dependence on the number of Hilbert coordinates. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate

namespace LipschitzHilbert
namespace PlanarPacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def envelope (P : PlanarPacketFamily N κ ι) (j : Fin N) (i : ι j) (z : ℝ × ℝ) : ℝ :=
  P.constant * (lineEnvelope (P.centerZ j i) P.width 1 z.1 *
    lineEnvelope (P.centerX j i) (P.length j) 1 z.2)

theorem envelope_nonneg (P : PlanarPacketFamily N κ ι) (j : Fin N) (i : ι j)
    (z : ℝ × ℝ) : 0 ≤ P.envelope j i z :=
  mul_nonneg P.constant_pos.le (mul_nonneg (lineEnvelope_nonneg _ _ _ _)
    (lineEnvelope_nonneg _ _ _ _))

theorem envelope_integrable (P : PlanarPacketFamily N κ ι) (j : Fin N) (i : ι j) :
    Integrable (P.envelope j i) :=
  ((integrable_lineEnvelope_one _ _ P.width_pos).mul_prod
    (integrable_lineEnvelope_one _ _ (P.length_pos j))).const_mul P.constant

theorem integral_envelope (P : PlanarPacketFamily N κ ι) (j : Fin N) (i : ι j) :
    (∫ z, P.envelope j i z) = (P.constant * Real.pi^2) * (P.length j * P.width) := by
  unfold envelope
  rw [integral_const_mul, Measure.volume_eq_prod, integral_prod_mul,
    integral_lineEnvelope_one _ _ P.width_pos,
    integral_lineEnvelope_one _ _ (P.length_pos j)]
  ring

theorem selectedWave_bound (P : PlanarPacketFamily N κ ι) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (s : Σ j, ι j) (k : κ) (z : ℝ × ℝ) :
    ‖P.selectedWave d v s k z‖ ≤ P.envelope s.1 s.2 z := by
  unfold selectedWave
  split_ifs
  · apply (P.wave_bound s.1 s.2 k z.1 z.2).trans
    unfold envelope centerX centerZ
    apply mul_le_mul_of_nonneg_left _ P.constant_pos.le
    rw [mul_comm (lineEnvelope _ _ 1 z.1)]
    exact mul_le_mul (lineEnvelope_antitone _ _ _ (by decide : 1 ≤ 3))
      (lineEnvelope_antitone _ _ _ (by decide : 1 ≤ 3))
      (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)
  · simpa only [norm_zero] using P.envelope_nonneg s.1 s.2 z

theorem mainCoefficient_norm (P : PlanarPacketFamily N κ ι) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (hv : Measurable v)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (j : Fin N) (i : ι j) :
    ‖P.mainCoefficient d v g j i‖ ≤ P.constant * Real.pi^2 := by
  have hm (k : κ) : Measurable (P.selectedWave d v ⟨j,i⟩ k) :=
    Measurable.ite (measurableSet_le hv measurable_const) (P.wave_measurable j i k) measurable_const
  have hint (k : κ) :
      Integrable (fun z => g z k * conj (P.selectedWave d v ⟨j,i⟩ k z)) := by
    have hgm : Measurable (fun z => g z k) :=
      (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hg)
    apply (P.envelope_integrable j i).mono'
      (hgm.mul (continuous_star.measurable.comp (hm k))).aestronglyMeasurable
    filter_upwards [] with z
    dsimp only [Pi.mul_apply, Function.comp_apply]
    rw [norm_mul, norm_star]
    have hgk := (PiLp.norm_apply_le (g z) k).trans (hg1 z)
    exact (mul_le_mul_of_nonneg_right hgk (norm_nonneg _)).trans
      (by simpa only [one_mul] using P.selectedWave_bound d v ⟨j,i⟩ k z)
  have h := analyzingCoefficient_norm_le volume
    (fun s : Σ j, ι j => P.length s.1 * P.width) (P.selectedWave d v) g ⟨j,i⟩
    (P.envelope j i) (mul_pos (P.length_pos j) P.width_pos)
    (P.envelope_integrable j i) (P.envelope_nonneg j i) hint hg1
    (P.selectedWave_bound d v ⟨j,i⟩)
  change ‖P.mainCoefficient d v g j i‖ ≤ _ at h
  rw [P.integral_envelope] at h
  have hz : P.length j * P.width ≠ 0 := (mul_pos (P.length_pos j) P.width_pos).ne'
  convert h using 1
  symm
  calc
    _ = (P.constant * Real.pi^2) * ((P.length j * P.width)⁻¹ * (P.length j * P.width)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hz, mul_one]

end PlanarPacketFamily
end LipschitzHilbert

end

end OAI

import OAI.Analysis.LipschitzHilbert.Fourier.VerticalMoment

namespace OAI

/-! A single measurable energy can control every member of a finite family
of interval sums throughout a vertical neighborhood. -/

noncomputable section
open MeasureTheory Set

namespace LipschitzHilbert

theorem interval_energy_domination {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {a b : ℝ} (hab : a < b)
    (hf : ∀ t ∈ Icc a b, DifferentiableAt ℝ f t)
    (hd : MemLp (deriv f) 2 (volume.restrict (Icc a b)))
    (V D : ℝ → ℝ) (hV : ContinuousOn V (Icc a b)) (hD : ContinuousOn D (Icc a b))
    (hbV : ∀ t ∈ Icc a b, ‖f t‖ ≤ V t)
    (hbD : ∀ t ∈ Icc a b, ‖deriv f t‖ ≤ D t)
    {x : ℝ} (hx : x ∈ Icc a b) :
    ‖f x‖^2 ≤ verticalSquareEnergy (volume.restrict (Icc a b)) V
      (fun t => (b-a)*D t) := by
  have hm : 0 < b-a := sub_pos.mpr hab
  have hcont : ContinuousOn f (Icc a b) := fun t ht =>
    (hf t ht).continuousAt.continuousWithinAt
  have hiV : IntegrableOn (fun t => V t^2) (Icc a b) volume := (hV.pow 2).integrableOn_Icc
  have hiD : IntegrableOn (fun t => D t^2) (Icc a b) volume := (hD.pow 2).integrableOn_Icc
  have hvi : (∫ t in Icc a b, ‖f t‖^2) ≤ ∫ t in Icc a b, V t^2 := by
    apply integral_mono_ae (hcont.norm.pow 2).integrableOn_Icc hiV
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact pow_le_pow_left₀ (norm_nonneg _) (hbV t ht) 2
  have hdi : (∫ t in Icc a b, ‖deriv f t‖^2) ≤ ∫ t in Icc a b, D t^2 := by
    apply integral_mono_ae (hd.integrable_norm_pow (by decide)) hiD
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact pow_le_pow_left₀ (norm_nonneg _) (hbD t ht) 2
  have h := (interval_pointwise_square f hab hf hd hx).trans
    (add_le_add (mul_le_mul_of_nonneg_left hvi (by positivity))
      (mul_le_mul_of_nonneg_left hdi (by positivity)))
  have hmass : (volume.restrict (Icc a b)).real univ = b-a := by
    rw [measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal hm.le]
  change ‖f x‖^2 ≤ 2 * (⨍ t in Icc a b, V t^2+((b-a)*D t)^2)
  rw [average_eq, hmass, smul_eq_mul]
  simp only [mul_pow]
  rw [integral_add hiV (hiD.const_mul _), integral_const_mul]
  have heq : 2 * ((b-a)⁻¹ * ((∫ t in Icc a b, V t^2) +
      (b-a)^2 * (∫ t in Icc a b, D t^2))) =
      (2/(b-a)) * (∫ t in Icc a b, V t^2) +
      2*(b-a)*(∫ t in Icc a b, D t^2) := by field_simp [hm.ne']
  rwa [heq]

theorem neighborhood_energy_domination {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (c r z v : ℝ) (hr : 0 < r) (hz : |z-c| ≤ r) (hv : |v| ≤ r)
    (hf : ∀ t ∈ Icc (c-2*r) (c+2*r), DifferentiableAt ℝ f t)
    (hd : MemLp (deriv f) 2 (volume.restrict (Icc (c-2*r) (c+2*r))))
    (V D : ℝ → ℝ) (hV : ContinuousOn V (Icc (c-2*r) (c+2*r)))
    (hD : ContinuousOn D (Icc (c-2*r) (c+2*r)))
    (hbV : ∀ t ∈ Icc (c-2*r) (c+2*r), ‖f t‖ ≤ V t)
    (hbD : ∀ t ∈ Icc (c-2*r) (c+2*r), ‖deriv f t‖ ≤ D t) :
    ‖f (z+v)‖^2 ≤ verticalSquareEnergy (volume.restrict (Icc (c-2*r) (c+2*r))) V
      (fun t => (4*r)*D t) := by
  have hx : z+v ∈ Icc (c-2*r) (c+2*r) := by
    rcases abs_le.mp hz with ⟨hz1,hz2⟩
    rcases abs_le.mp hv with ⟨hv1,hv2⟩
    constructor <;> linarith
  have h := interval_energy_domination f (by linarith : c-2*r < c+2*r)
    hf hd V D hV hD hbV hbD hx
  convert h using 1
  congr 1
  funext t
  ring

end LipschitzHilbert

end

end OAI

import OAI.Analysis.LipschitzHilbert.Estimates.NeighborhoodEnergy
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

namespace OAI

/-! A measurable exceptional set for a common neighborhood majorant.
The moment order is an integer, so even orders may grow with the manuscript
parameter without changing any packet regularity order. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem interval_vertical_moment (ν : Measure ℝ) [SFinite ν]
    (V D : ℝ × ℝ → ℝ) (hV : Continuous V) (hD : Continuous D)
    {a b : ℝ} (hab : a < b) (n : ℕ) (C : ℝ≥0∞)
    (hline : ∀ t, (∫⁻ x, ENNReal.ofReal (V (t,x)^(2*n)+D (t,x)^(2*n)) ∂ν) ≤ C) :
    (∫⁻ x, ENNReal.ofReal (verticalSquareEnergy (volume.restrict (Icc a b))
      (fun t => V (t,x)) (fun t => D (t,x)))^n ∂ν) ≤ (4:ℝ≥0∞)^n*C := by
  let μ := volume.restrict (Icc a b)
  have hm : μ univ ≠ 0 := by
    dsimp [μ]
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab))
  let : NeZero μ := ⟨fun h => hm (by rw [h]; simp)⟩
  have hcV (x : ℝ) : Continuous (fun t => V (t,x)) := hV.comp (continuous_id.prodMk continuous_const)
  have hcD (x : ℝ) : Continuous (fun t => D (t,x)) := hD.comp (continuous_id.prodMk continuous_const)
  exact verticalSquareEnergy_line_moment μ ν V D hV.measurable hD.measurable n
    (fun x => ((hcV x).pow 2).continuousOn.integrableOn_Icc)
    (fun x => ((hcD x).pow 2).continuousOn.integrableOn_Icc)
    (fun x => (((hcV x).pow 2).add ((hcD x).pow 2)).pow n |>.continuousOn.integrableOn_Icc)
    (fun x => ((hcV x).pow (2*n)).continuousOn.integrableOn_Icc)
    (fun x => ((hcD x).pow (2*n)).continuousOn.integrableOn_Icc) C hline

theorem energy_superlevel_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Ω → ℝ) (hE : Measurable E)
    (threshold : ℝ) (hthreshold : 0 ≤ threshold) (n : ℕ) (C : ℝ≥0∞)
    (hmoment : (∫⁻ x, ENNReal.ofReal (E x)^n ∂μ) ≤ C) :
    (ENNReal.ofReal threshold)^(2*n) * μ {x | threshold^2 ≤ E x} ≤ C := by
  have hsub : {x | threshold^2 ≤ E x} ⊆
      {x | (ENNReal.ofReal threshold)^(2*n) ≤ ENNReal.ofReal (E x)^n} := by
    intro x hx
    change (ENNReal.ofReal threshold)^(2*n) ≤ ENNReal.ofReal (E x)^n
    have h := pow_le_pow_left' (ENNReal.ofReal_le_ofReal hx) n
    simpa only [ENNReal.ofReal_pow hthreshold, pow_mul] using h
  exact (mul_le_mul' le_rfl (measure_mono hsub)).trans
    ((mul_meas_ge_le_lintegral (hE.ennreal_ofReal.pow_const n) _).trans hmoment)

theorem neighborhood_bound_outside_energy {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (c r z v threshold B : ℝ) (hr : 0 < r)
    (hz : |z-c| ≤ r) (hv : |v| ≤ r) (hthreshold : 0 ≤ threshold) (hout : ¬ threshold^2 ≤ B)
    (hf : ∀ t ∈ Icc (c-2*r) (c+2*r), DifferentiableAt ℝ f t)
    (hd : MemLp (deriv f) 2 (volume.restrict (Icc (c-2*r) (c+2*r))))
    (V D : ℝ → ℝ) (hV : ContinuousOn V (Icc (c-2*r) (c+2*r)))
    (hD : ContinuousOn D (Icc (c-2*r) (c+2*r)))
    (hbV : ∀ t ∈ Icc (c-2*r) (c+2*r), ‖f t‖ ≤ V t)
    (hbD : ∀ t ∈ Icc (c-2*r) (c+2*r), ‖deriv f t‖ ≤ D t)
    (hB : verticalSquareEnergy (volume.restrict (Icc (c-2*r) (c+2*r))) V
      (fun t => (4*r)*D t) ≤ B) :
    ‖f (z+v)‖ ≤ threshold := by
  have h := (neighborhood_energy_domination f c r z v hr hz hv hf hd V D hV hD hbV hbD).trans hB
  have hb := lt_of_not_ge hout
  nlinarith [norm_nonneg (f (z+v))]

end LipschitzHilbert

end

end OAI

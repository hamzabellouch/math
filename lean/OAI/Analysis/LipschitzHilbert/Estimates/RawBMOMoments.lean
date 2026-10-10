import OAI.Analysis.LipschitzHilbert.Estimates.ContinuousBMOMoments

namespace OAI

/-! Uncentered interval moments from the proved John--Nirenberg estimate
and a bound for the interval mean. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert.FiniteLineGrid

theorem continuous_raw_moment (g : FiniteLineGrid) (hb : 1 < g.branching)
    (f : ℝ → ℝ) (hm : Measurable f) (hf : Integrable f g.lineMeasure)
    (hc : ∀ x ∈ g.root, ContinuousAt f x) {A B p : ℝ}
    (hA : 0 < A) (hBMO : g.HasFullMeanOscillationBound f A)
    (hmean : |integralAverage g.lineMeasure f| ≤ B) (hp : 0 ≤ p) :
    (∫⁻ x, (ENNReal.ofReal |f x|) ^ p ∂g.lineMeasure) ≤
      (2 : ℝ≥0∞) ^ p *
        (7 * ENNReal.ofReal ((p * (((g.branching : ℝ) + 2) * A) / Real.log (3 / 2)) ^ p) +
          (ENNReal.ofReal B) ^ p) * g.lineMeasure univ := by
  let m := integralAverage g.lineMeasure f
  have hcenter := g.continuous_mean_oscillation_moment hb f hm hf hc hA hBMO hp
  have hpoint (x : ℝ) : (ENNReal.ofReal |f x|) ^ p ≤
      (2 : ℝ≥0∞) ^ p * ((ENNReal.ofReal |f x - m|) ^ p + (ENNReal.ofReal B) ^ p) := by
    have habs : |f x| ≤ |f x - m| + B := by
      have ha := norm_add_le (f x - m) m
      simp only [Real.norm_eq_abs] at ha
      rw [sub_add_cancel] at ha
      exact ha.trans (add_le_add le_rfl hmean)
    have hB : 0 ≤ B := (abs_nonneg m).trans hmean
    have h0 : ENNReal.ofReal |f x| ≤ ENNReal.ofReal |f x - m| + ENNReal.ofReal B := by
      rw [← ENNReal.ofReal_add (abs_nonneg _) hB]
      exact ENNReal.ofReal_le_ofReal habs
    exact (ENNReal.rpow_le_rpow h0 hp).trans
      (ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow _ _ hp)
  have hmcenter : Measurable (fun x => (ENNReal.ofReal |f x - m|) ^ p) := by
    apply Measurable.pow_const
    apply Measurable.ennreal_ofReal
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hm.sub measurable_const).norm
  have heq : (fun x => (ENNReal.ofReal |f x - m|) ^ p) =
      (fun x => ENNReal.ofReal (|f x - m| ^ p)) := by
    funext x
    exact ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp
  calc
    _ ≤ ∫⁻ x, (2 : ℝ≥0∞) ^ p * ((ENNReal.ofReal |f x - m|) ^ p +
          (ENNReal.ofReal B) ^ p) ∂g.lineMeasure := lintegral_mono hpoint
    _ = (2 : ℝ≥0∞) ^ p * ((∫⁻ x, ENNReal.ofReal (|f x - m| ^ p) ∂g.lineMeasure) +
          (ENNReal.ofReal B) ^ p * g.lineMeasure univ) := by
      rw [lintegral_const_mul (f := fun x => (ENNReal.ofReal |f x - m|) ^ p +
          (ENNReal.ofReal B) ^ p) _ (hmcenter.add measurable_const),
        lintegral_add_left hmcenter, lintegral_const, heq]
    _ ≤ _ := by
      calc
        _ ≤ (2 : ℝ≥0∞) ^ p *
            (7 * ENNReal.ofReal ((p * (((g.branching : ℝ) + 2) * A) / Real.log (3 / 2)) ^ p) *
              g.lineMeasure univ + (ENNReal.ofReal B) ^ p * g.lineMeasure univ) := by
          gcongr
        _ = _ := by ring

end LipschitzHilbert.FiniteLineGrid

end

end OAI

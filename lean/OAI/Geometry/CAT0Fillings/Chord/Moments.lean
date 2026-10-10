import Mathlib
import OAI.Geometry.CAT0Fillings.Chord.NonnegativeMeasure
import OAI.Geometry.CAT0Fillings.Powers.PolynomialBound
import OAI.Geometry.CAT0Fillings.Radial.ClosedInequality

namespace OAI

section
namespace CAT0Fillings.Conformal
lemma beta_dimension {n β : ℝ} (hb : 0 < β) (hn : n*β = 1+2*β) : 2 < n := by
  exact (mul_lt_mul_iff_of_pos_right hb).mp (by linarith : 2*β < n*β)
lemma beta_half_dimension {n β : ℝ} (hb : 0 < β) (hn : n*β = 1+2*β) :
    1/(2*β) = (n-2)/2 := by
  apply (div_eq_div_iff (by positivity : (2*β:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0)).mpr
  nlinarith
lemma beta_inverse_half {β : ℝ} (hb : 0 < β) : 1/(2*(1/(2*β))) = β := by field_simp
lemma beta_critical_ratio {n β : ℝ} (hb : 0 < β) (hn : n*β = 1+2*β) :
    2/(2+4*β) = (n-2)/n := by
  have hn0 : 0 < n := lt_trans (by norm_num) (beta_dimension hb hn)
  apply (div_eq_div_iff (by positivity : (2+4*β:ℝ) ≠ 0) hn0.ne').mpr
  nlinarith
lemma beta_critical_product {n β : ℝ} (hb : 0 < β) (hn : n*β = 1+2*β) :
    -(1/(2*β))*(2+4*β) = -n := by
  rw [neg_mul,neg_inj]
  field_simp
  nlinarith
end CAT0Fillings.Conformal
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ChordMeasure
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X]
  (μ : Measure X) [IsFiniteMeasure μ] {v : X → ℝ}
omit [CompactSpace X] [Nonempty X] [IsFiniteMeasure μ] in
lemma chord_measurable [CompactSpace X] [Nonempty X] [IsFiniteMeasure μ]
    (o : X) (hv : AEStronglyMeasurable v μ) (κ β : ℝ) :
    AEStronglyMeasurable (fun x => κ*dist o x*(v x)^β) μ := by
  exact (aestronglyMeasurable_const.mul (continuous_const.dist continuous_id).aestronglyMeasurable).mul
    (hv.aemeasurable.pow_const _).aestronglyMeasurable
omit [MetricSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X] in
lemma integral_power [MetricSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X]
    (hv : ∀ᵐ x ∂μ, 0 ≤ v x)
    (hm : ∀ b : ℝ, 0 < b → MemLp v (ENNReal.ofReal b) μ) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun x => (v x)^p) μ :=
  (ClosedCalculus.power_memLp_two hv hm hp).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
lemma chord_second_moment (o : X) (hv : ∀ᵐ x ∂μ, 0 ≤ v x)
    (hm : ∀ b : ℝ, 0 < b → MemLp v (ENNReal.ofReal b) μ) {β : ℝ} (hb : 0 < β)
    (hW : 0 < total μ (fun x => |v x|^(2+4*β))) (κ : ℝ) :
    Integrable (fun x => (κ*dist o x*(v x)^β)^2)
      (probability μ (fun x => |v x|^(2+4*β))) := by
  have hvm := (hm 2 (by norm_num)).aestronglyMeasurable
  have hsm := chord_measurable μ o hvm κ β
  apply integrable_probability μ _ (hvm.aemeasurable.abs.pow_const _).aestronglyMeasurable
    (Eventually.of_forall fun _ => Real.rpow_nonneg (abs_nonneg _) _) hW (hsm.pow 2)
  have hp := integral_power μ hv hm (p := 2+6*β) (by positivity)
  have hi : Integrable (fun x => |v x|^(2+4*β)*(κ*dist o x*(v x)^β)^2) μ := by
    apply (hp.const_mul (κ^2*Metric.diam (univ : Set X)^2)).mono'
      (((hvm.aemeasurable.abs.pow_const _).aestronglyMeasurable).mul (hsm.pow 2))
    filter_upwards [hv] with x hx
    have hpw : |v x|^(2+4*β)*(κ*dist o x*(v x)^β)^2 = κ^2*dist o x^2*(v x)^(2+6*β) := by
      rw [abs_of_nonneg hx,mul_pow,mul_pow,←Real.rpow_mul_natCast hx,Nat.cast_ofNat]
      rw [show (2+6*β:ℝ) = (2+4*β)+β*2 by ring,
        Real.rpow_add' hx (by linarith : 2+4*β+β*2 ≠ 0)]
      ring
    change ‖|v x|^(2+4*β)*(κ*dist o x*(v x)^β)^2‖ ≤ _
    rw [hpw,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have hdist := ChartGeometry.radius_bound o x
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ dist_nonneg hdist 2) (sq_nonneg κ)) (Real.rpow_nonneg hx _)
  exact hi
end CAT0Fillings.ChordMeasure
end

end OAI

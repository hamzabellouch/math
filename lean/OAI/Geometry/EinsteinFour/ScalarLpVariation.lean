import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.ContinuousMap.Compact

namespace OAI

/-! Differentiation of the scalar p-moment along bounded directions.
The base function need only belong to Lp, including at its zero set. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable section

private theorem scalarMoment_point_derivative {p : ℝ} (hp : 2 < p)
    (f b t : ℝ) :
    HasDerivAt (fun s : ℝ => |f + s * b| ^ p)
      (p * |f + t * b| ^ (p - 2) * (f + t * b) * b) t := by
  have hlin : HasDerivAt (fun s : ℝ => f + s * b) b t := by
    simpa only [one_mul, zero_add, Pi.add_apply, id_eq] using!
      (hasDerivAt_const t f).add ((hasDerivAt_id t).mul_const b)
  simpa only [Function.comp_def] using
    (hasDerivAt_abs_rpow (f + t * b) (by linarith : 1 < p)).comp t hlin

private theorem scalarMoment_derivative_bound {p B : ℝ} (hp : 2 < p) (hB : 0 ≤ B)
    {f b t : ℝ} (hb : |b| ≤ B) (ht : |t| ≤ 1) :
    ‖p * |f + t * b| ^ (p - 2) * (f + t * b) * b‖ ≤
      (p * B) * (|f| + B) ^ (p - 1) := by
  have hpow : |f + t * b| ^ (p - 2) * |f + t * b| =
      |f + t * b| ^ (p - 1) := by
    rw [← Real.rpow_add_one' (abs_nonneg _) (by linarith : p - 2 + 1 ≠ 0)]
    congr 1
    ring
  have hbase : |f + t * b| ≤ |f| + B :=
    (abs_add_le _ _).trans (add_le_add le_rfl
      ((abs_mul t b).le.trans ((mul_le_mul ht hb (abs_nonneg b) zero_le_one).trans_eq
        (one_mul B))))
  calc
    ‖p * |f + t * b| ^ (p - 2) * (f + t * b) * b‖ =
        p * |f + t * b| ^ (p - 1) * |b| := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
        abs_of_pos (by linarith : 0 < p),
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      rw [mul_assoc p, hpow]
    _ ≤ p * (|f| + B) ^ (p - 1) * B := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (abs_nonneg _) hbase (by linarith)) (by linarith)
      · exact hb
      · exact abs_nonneg b
      · exact mul_nonneg (by linarith) (Real.rpow_nonneg (by positivity) _)
    _ = (p * B) * (|f| + B) ^ (p - 1) := by ring

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- A bounded measurable direction differentiates the p-moment of an arbitrary
Lp function.  No nonvanishing or regularity assumption is placed on the latter. -/
theorem scalarLpMoment_hasDerivAt {p : ℝ} (hp : 2 < p) {f b : X → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) μ) (hb : AEStronglyMeasurable b μ)
    {B : ℝ} (hB : 0 ≤ B) (hbBound : ∀ᵐ x ∂μ, |b x| ≤ B) :
    Integrable (fun x => |f x| ^ (p - 2) * f x * b x) μ ∧
      HasDerivAt (fun t : ℝ => ∫ x, |f x + t * b x| ^ p ∂μ)
        (p * ∫ x, |f x| ^ (p - 2) * f x * b x ∂μ) 0 := by
  let F (t : ℝ) (x : X) := |f x + t * b x| ^ p
  let G (t : ℝ) (x : X) := p * |f x + t * b x| ^ (p - 2) * (f x + t * b x) * b x
  let H (x : X) := (p * B) * (|f x| + B) ^ (p - 1)
  have hp0 : 0 < p := by linarith
  have hpowMeas {q : ℝ} (hq : 0 ≤ q) {h : X → ℝ}
      (hh : AEStronglyMeasurable h μ) :
      AEStronglyMeasurable (fun x => |h x| ^ q) μ := by
    have hc : Continuous (fun r : ℝ => |r| ^ q) :=
      continuous_abs.rpow_const (fun _ => Or.inr hq)
    exact hc.comp_aestronglyMeasurable hh
  have hFm : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F t) μ := by
    exact Eventually.of_forall fun t => hpowMeas hp0.le
      (hf.aestronglyMeasurable.add (hb.const_mul t))
  have hFi : Integrable (F 0) μ := by
    simpa only [F, zero_mul, add_zero, Real.norm_eq_abs,
      ENNReal.toReal_ofReal hp0.le] using hf.integrable_norm_rpow'
  have hGm : AEStronglyMeasurable (G 0) μ := by
    simpa only [G, zero_mul, add_zero, Pi.mul_apply] using!
      (((hpowMeas (by linarith : 0 ≤ p - 2) hf.aestronglyMeasurable).const_mul p).mul
        hf.aestronglyMeasurable).mul hb
  have hbaseLp : MemLp (fun x => |f x| + B) (ENNReal.ofReal p) μ := by
    simpa only [Real.norm_eq_abs, Pi.add_apply] using! hf.norm.add (memLp_const B)
  have hbaseInt : Integrable (fun x => ‖|f x| + B‖ ^ p) μ := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using hbaseLp.integrable_norm_rpow'
  have hlessInt : Integrable (fun x => (|f x| + B) ^ (p - 1)) μ := by
    have hi := integrable_norm_rpow_of_le hbaseLp.aestronglyMeasurable
      (by linarith : 0 ≤ p - 1) hp0.le (by linarith : p - 1 ≤ p) hbaseInt
    simpa only [Real.norm_of_nonneg (add_nonneg (abs_nonneg _) hB)] using hi
  have hHi : Integrable H μ := hlessInt.const_mul (p * B)
  have hbound : ∀ᵐ x ∂μ, ∀ t ∈ Ioo (-1 : ℝ) 1, ‖G t x‖ ≤ H x := by
    filter_upwards [hbBound] with x hx t ht
    exact scalarMoment_derivative_bound hp hB hx (abs_le.mpr ⟨ht.1.le, ht.2.le⟩)
  have hdiff : ∀ᵐ x ∂μ, ∀ t ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun s => F s x) (G t x) t :=
    Eventually.of_forall fun x t _ => scalarMoment_point_derivative hp (f x) (b x) t
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 by constructor <;> norm_num))
    hFm hFi hGm hbound hHi hdiff
  have hi : Integrable (fun x => |f x| ^ (p - 2) * f x * b x) μ := by
    have hscaled := h.1.const_mul p⁻¹
    convert hscaled using 1
    ext x
    simp only [G, zero_mul, add_zero]
    field_simp [ne_of_gt hp0]
  refine ⟨hi, ?_⟩
  have heq : (fun x => G 0 x) = fun x => p * (|f x| ^ (p - 2) * f x * b x) := by
    funext x
    dsimp [G]
    simp only [zero_mul, add_zero]
    ring
  simpa only [heq, integral_const_mul] using h.2

/-- Lp-space version, ready for a weak variational equation. -/
theorem scalarLpMoment_hasDerivAt_lp {p : ℝ} (hp : 2 < p)
    (f : Lp ℝ (ENNReal.ofReal p) μ) {b : X → ℝ}
    (hb : AEStronglyMeasurable b μ) {B : ℝ} (hB : 0 ≤ B)
    (hbBound : ∀ᵐ x ∂μ, |b x| ≤ B) :
    HasDerivAt (fun t : ℝ => ∫ x, |f x + t * b x| ^ p ∂μ)
      (p * ∫ x, |f x| ^ (p - 2) * f x * b x ∂μ) 0 :=
  (scalarLpMoment_hasDerivAt hp (Lp.memLp f) hb hB hbBound).2

/-- On a compact base every continuous, hence every smooth, test direction
automatically satisfies the required domination. -/
theorem scalarLpMoment_hasDerivAt_continuous [TopologicalSpace X]
    [OpensMeasurableSpace X] [CompactSpace X] {p : ℝ} (hp : 2 < p)
    {f : X → ℝ} (hf : MemLp f (ENNReal.ofReal p) μ) (b : C(X, ℝ)) :
    Integrable (fun x => |f x| ^ (p - 2) * f x * b x) μ ∧
      HasDerivAt (fun t : ℝ => ∫ x, |f x + t * b x| ^ p ∂μ)
        (p * ∫ x, |f x| ^ (p - 2) * f x * b x ∂μ) 0 :=
  scalarLpMoment_hasDerivAt hp hf b.continuous.aestronglyMeasurable (norm_nonneg b)
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using b.norm_coe_le_norm x)

end
end PositiveEinsteinFour.Geometry

end OAI

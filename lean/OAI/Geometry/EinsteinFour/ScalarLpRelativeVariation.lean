import OAI.Geometry.EinsteinFour.ScalarLpNormVariation

namespace OAI

/-! First variation along a direction dominated by the original Lp function.
This covers rational truncations of a Sobolev minimizer without boundedness
of the minimizer or a separate extension of its Euler equation. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable section

private theorem scalarRelativeMoment_point_derivative {p : ℝ} (hp : 2 < p)
    (f b t : ℝ) :
    HasDerivAt (fun s : ℝ => |f + s * b| ^ p)
      (p * |f + t * b| ^ (p - 2) * (f + t * b) * b) t := by
  have hlin : HasDerivAt (fun s : ℝ => f + s * b) b t := by
    simpa only [one_mul, zero_add, Pi.add_apply, id_eq] using!
      (hasDerivAt_const t f).add ((hasDerivAt_id t).mul_const b)
  simpa only [Function.comp_def] using
    (hasDerivAt_abs_rpow (f + t * b) (by linarith : 1 < p)).comp t hlin

private theorem scalarRelativeMoment_bound {p B : ℝ} (hp : 2 < p) (hB : 0 ≤ B)
    {f b t : ℝ} (hb : |b| ≤ B * |f|) (ht : |t| ≤ 1) :
    ‖p * |f + t * b| ^ (p - 2) * (f + t * b) * b‖ ≤
      (p * B * (1 + B) ^ (p - 1)) * |f| ^ p := by
  have hbase : |f + t * b| ≤ (1 + B) * |f| := by
    calc
      _ ≤ |f| + |t| * |b| := by simpa only [abs_mul] using abs_add_le f (t * b)
      _ ≤ |f| + B * |f| := add_le_add le_rfl
        ((mul_le_mul_of_nonneg_right ht (abs_nonneg b)).trans (by simpa using hb))
      _ = _ := by ring
  have hpow : |f + t * b| ^ (p - 2) * |f + t * b| = |f + t * b| ^ (p - 1) := by
    rw [← Real.rpow_add_one' (abs_nonneg _) (by linarith : p - 2 + 1 ≠ 0)]
    congr 1
    ring
  calc
    _ = p * |f + t * b| ^ (p - 1) * |b| := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
        abs_of_pos (by linarith : 0 < p),
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      rw [mul_assoc p, hpow]
    _ ≤ p * ((1 + B) * |f|) ^ (p - 1) * (B * |f|) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (abs_nonneg _) hbase (by linarith)) (by linarith)
      · exact hb
      · exact abs_nonneg _
      · exact mul_nonneg (by linarith) (Real.rpow_nonneg (by positivity) _)
    _ = _ := by
      rw [Real.mul_rpow (by positivity) (abs_nonneg _)]
      have hf : |f| ^ (p - 1) * |f| = |f| ^ p := by
        rw [← Real.rpow_add_one' (abs_nonneg _) (by linarith : p - 1 + 1 ≠ 0)]
        congr 1
        ring
      calc
        _ = (p * B * (1 + B) ^ (p - 1)) * (|f| ^ (p - 1) * |f|) := by ring
        _ = _ := by rw [hf]

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem scalarLpRelativeMoment_hasDerivAt {p : ℝ} (hp : 2 < p) {f b : X → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) μ) (hb : AEStronglyMeasurable b μ)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ᵐ x ∂μ, |b x| ≤ B * |f x|) :
    Integrable (fun x => |f x| ^ (p - 2) * f x * b x) μ ∧
      HasDerivAt (fun t : ℝ => ∫ x, |f x + t * b x| ^ p ∂μ)
        (p * ∫ x, |f x| ^ (p - 2) * f x * b x ∂μ) 0 := by
  let F (t : ℝ) (x : X) := |f x + t * b x| ^ p
  let G (t : ℝ) (x : X) := p * |f x + t * b x| ^ (p - 2) * (f x + t * b x) * b x
  let H (x : X) := (p * B * (1 + B) ^ (p - 1)) * |f x| ^ p
  have hp0 : 0 < p := by linarith
  have hpowMeas {q : ℝ} (hq : 0 ≤ q) {h : X → ℝ}
      (hh : AEStronglyMeasurable h μ) :
      AEStronglyMeasurable (fun x => |h x| ^ q) μ :=
    (continuous_abs.rpow_const (fun _ => Or.inr hq)).comp_aestronglyMeasurable hh
  have hFm : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F t) μ :=
    Eventually.of_forall fun t => hpowMeas hp0.le
      (hf.aestronglyMeasurable.add (hb.const_mul t))
  have hFi : Integrable (F 0) μ := by
    simpa only [F, zero_mul, add_zero, Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le]
      using hf.integrable_norm_rpow'
  have hGm : AEStronglyMeasurable (G 0) μ := by
    simpa only [G, zero_mul, add_zero, Pi.mul_apply] using!
      (((hpowMeas (by linarith : 0 ≤ p - 2) hf.aestronglyMeasurable).const_mul p).mul
        hf.aestronglyMeasurable).mul hb
  have hHi : Integrable H μ := by
    apply Integrable.const_mul
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le] using hf.integrable_norm_rpow'
  have hbound' : ∀ᵐ x ∂μ, ∀ t ∈ Ioo (-1 : ℝ) 1, ‖G t x‖ ≤ H x := by
    filter_upwards [hbound] with x hx t ht
    exact scalarRelativeMoment_bound hp hB hx (abs_le.mpr ⟨ht.1.le, ht.2.le⟩)
  have hdiff : ∀ᵐ x ∂μ, ∀ t ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun s => F s x) (G t x) t :=
    Eventually.of_forall fun x t _ => scalarRelativeMoment_point_derivative hp (f x) (b x) t
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 by constructor <;> norm_num))
    hFm hFi hGm hbound' hHi hdiff
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

/-- The squared norm derivative used to test a homogeneous energy minimum
with a rational truncation of the minimizer itself. -/
theorem scalarLpRelativeNormSq_hasDerivAt {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 2 < p) (f b : Lp ℝ (ENNReal.ofReal p) μ) (hf : ‖f‖ = 1)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ᵐ x ∂μ, |b x| ≤ B * |f x|) :
    HasDerivAt (fun t : ℝ => ‖f + t • b‖ ^ 2)
      (2 * ∫ x, |f x| ^ (p - 2) * f x * b x ∂μ) 0 := by
  have hp0 : 0 < p := by linarith
  have hd := (scalarLpRelativeMoment_hasDerivAt hp (Lp.memLp f)
    (Lp.aestronglyMeasurable b) hB hbound).2
  have hz : (∫ x, |f x + (0 : ℝ) * b x| ^ p ∂μ) = 1 := by
    simp only [zero_mul, add_zero]
    rw [scalarLp_moment_eq_norm_rpow hp0 f, hf, Real.one_rpow]
  have hpow := hd.rpow_const (p := 2 / p) (Or.inl (by rw [hz]; norm_num))
  have heq : (fun t : ℝ => ‖f + t • b‖ ^ 2) =
      fun t => (∫ x, |f x + t * b x| ^ p ∂μ) ^ (2 / p) := by
    funext t
    rw [scalarLp_norm_sq_eq_moment hp0]
    congr 1
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add f (t • b), Lp.coeFn_smul t b] with x hsum hsmul
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hsum hsmul
    rw [hsum, hsmul]
  rw [← heq] at hpow
  convert hpow using 1
  rw [hz, Real.one_rpow, mul_one]
  field_simp [hp0.ne']

end
end PositiveEinsteinFour.Geometry

end OAI

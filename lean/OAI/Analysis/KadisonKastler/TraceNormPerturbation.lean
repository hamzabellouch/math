import OAI.Analysis.KadisonKastler.TraceOneNorm

namespace OAI

/-! # Trace-norm triangle and sandwich perturbation estimates -/

namespace KadisonKastler

noncomputable section

universe u

variable {B : Type u} [CStarAlgebra B]

local instance : PartialOrder B := CStarAlgebra.spectralOrder B
local instance : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

/-- The trace of a positive element is nonnegative. -/
private theorem trace_re_nonneg (τ : FaithfulTracialState B) {a : B} (ha : 0 ≤ a) :
    0 ≤ (τ.toLinearMap a).re := by
  obtain ⟨b, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
  exact τ.positive b

/-- The tracial one-norm is nonnegative. -/
theorem traceOneNorm_nonneg (τ : FaithfulTracialState B) (x : B) :
    0 ≤ traceOneNorm τ x := trace_re_nonneg τ (CFC.abs_nonneg x)

/-- A positive element defines a trace functional bounded by its trace. -/
private theorem norm_trace_mul_positive_le (τ : FaithfulTracialState B)
    (w a : B) (ha : 0 ≤ a) :
    ‖τ.toLinearMap (w * a)‖ ≤ ‖w‖ * (τ.toLinearMap a).re := by
  obtain ⟨b, hb, hab⟩ := CStarAlgebra.nonneg_iff_exists_isSelfAdjoint_and_eq_mul_self.mp ha
  have htrace : τ.toLinearMap (w * a) = τ.toLinearMap (star (star w * b) * b) := by
    rw [hab, star_mul, star_star, hb.star_eq]
    calc
      τ.toLinearMap (w * (b * b)) = τ.toLinearMap ((w * b) * b) := by rw [mul_assoc]
      _ = τ.toLinearMap (b * (w * b)) := τ.tracial _ _
      _ = τ.toLinearMap (b * w * b) := by rw [mul_assoc]
  rw [htrace]
  calc
    ‖τ.toLinearMap (star (star w * b) * b)‖ ≤
        traceTwoNorm τ (star w * b) * traceTwoNorm τ b := τ.cauchySchwarz _ _
    _ ≤ (‖star w‖ * traceTwoNorm τ b) * traceTwoNorm τ b :=
      mul_le_mul_of_nonneg_right (traceTwoNorm_mul_le_left τ _ _) (traceTwoNorm_nonneg τ b)
    _ = ‖w‖ * (τ.toLinearMap a).re := by
      rw [norm_star, mul_assoc, ← pow_two, traceTwoNorm_sq, hb.star_eq, ← hab]

private def reconstructionFunction (ε t : ℝ) : ℝ :=
  1 - ε⁻¹ * (clippingFunction ε t * t)

private theorem reconstructionFunction_continuous {ε : ℝ} (hε : 0 < ε) :
    Continuous (reconstructionFunction ε) :=
  continuous_const.sub (continuous_const.mul ((clippingFunction_continuous hε).mul continuous_id))

private theorem reconstructionFunction_bound {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) :
    0 ≤ t * reconstructionFunction ε t ∧ t * reconstructionFunction ε t ≤ ε := by
  by_cases hs : t ≤ ε
  · have hmul : ε⁻¹ * t ≤ 1 := by
      have hm := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hε.le)
      rwa [inv_mul_cancel₀ hε.ne'] at hm
    have hmul0 : 0 ≤ ε⁻¹ * t := mul_nonneg (inv_nonneg.mpr hε.le) ht
    simp only [reconstructionFunction, clippingFunction, max_eq_left hs,
      div_self hε.ne', one_mul]
    constructor
    · exact mul_nonneg ht (sub_nonneg.mpr hmul)
    · nlinarith [mul_nonneg ht hmul0]
  · have hs' : ε ≤ t := le_of_lt (lt_of_not_ge hs)
    have ht' : 0 < t := hε.trans_le hs'
    have he : reconstructionFunction ε t = 0 := by
      simp only [reconstructionFunction, clippingFunction, max_eq_right hs']
      field_simp
      norm_num
    simp only [he, mul_zero]
    exact ⟨le_rfl, hε.le⟩

private def normalizedClip (ε : ℝ) (x : B) : B := ε⁻¹ • spectralClip ε x

private theorem normalizedClip_norm_le {ε : ℝ} (hε : 0 < ε) (x : B) :
    ‖normalizedClip ε x‖ ≤ 1 := by
  rw [normalizedClip, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε)]
  calc
    ε⁻¹ * ‖spectralClip ε x‖ ≤ ε⁻¹ * ε :=
      mul_le_mul_of_nonneg_left (spectralClip_norm_le hε x) (inv_nonneg.mpr hε.le)
    _ = 1 := inv_mul_cancel₀ hε.ne'

private theorem normalizedClip_reconstruction {ε : ℝ} (hε : 0 < ε) (x : B) :
    ‖x - normalizedClip ε x * CFC.abs x‖ ≤ ε := by
  have hf := clippingFunction_continuous hε
  have hrep : x - normalizedClip ε x * CFC.abs x =
      x * cfc (reconstructionFunction ε) (CFC.abs x) := by
    have hm : normalizedClip ε x * CFC.abs x =
        x * cfc (fun t : ℝ => ε⁻¹ * (clippingFunction ε t * t)) (CFC.abs x) := by
      rw [cfc_const_mul ε⁻¹ _ _ (by fun_prop),
        cfc_mul (clippingFunction ε) (fun t : ℝ => t) _ hf.continuousOn continuous_id.continuousOn,
        cfc_id' ℝ (CFC.abs x)]
      simp only [normalizedClip, spectralClip, mul_smul_comm, smul_mul_assoc, mul_assoc]
    rw [hm]
    change _ = x * cfc (fun t : ℝ => 1 - ε⁻¹ * (clippingFunction ε t * t)) (CFC.abs x)
    rw [cfc_sub (fun _ : ℝ => 1) (fun t : ℝ => ε⁻¹ * (clippingFunction ε t * t)) _
      (by fun_prop) (by fun_prop), cfc_const_one ℝ (CFC.abs x), mul_sub, mul_one]
  rw [hrep]
  have hs : ‖x * cfc (reconstructionFunction ε) (CFC.abs x)‖ ^ 2 ≤ ε ^ 2 := by
    rw [pow_two, ← CStarRing.norm_star_mul_self,
      star_mul_cfc_abs x _ (reconstructionFunction_continuous hε)]
    apply norm_cfc_le (sq_nonneg ε)
    intro t ht
    obtain ⟨h0, h1⟩ := reconstructionFunction_bound hε
      (spectrum_nonneg_of_nonneg (CFC.abs_nonneg x) ht)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ h0 h1 2
  nlinarith [norm_nonneg (x * cfc (reconstructionFunction ε) (CFC.abs x))]

/-- A contraction paired with any element is bounded by its tracial
one-norm. Together with approximate duality, this identifies the norm. -/
theorem norm_trace_mul_le_traceOneNorm (τ : FaithfulTracialState B)
    (w x : B) (hw : ‖w‖ ≤ 1) :
    ‖τ.toLinearMap (w * x)‖ ≤ traceOneNorm τ x := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let v : B := normalizedClip ε x
  have hv : ‖v‖ ≤ 1 := normalizedClip_norm_le hε x
  have herror : ‖x - v * CFC.abs x‖ ≤ ε := normalizedClip_reconstruction hε x
  have hsplit : w * x = w * (x - v * CFC.abs x) + (w * v) * CFC.abs x := by
    noncomm_ring
  have herr : ‖τ.toLinearMap (w * (x - v * CFC.abs x))‖ ≤ ε := by
    calc
      ‖τ.toLinearMap (w * (x - v * CFC.abs x))‖ ≤ ‖w * (x - v * CFC.abs x)‖ :=
        τ.norm_apply_le_norm _
      _ ≤ ‖w‖ * ‖x - v * CFC.abs x‖ := norm_mul_le _ _
      _ ≤ 1 * ε := mul_le_mul hw herror (norm_nonneg _) (by norm_num)
      _ = ε := one_mul _
  have hmain : ‖τ.toLinearMap ((w * v) * CFC.abs x)‖ ≤ traceOneNorm τ x := by
    calc
      ‖τ.toLinearMap ((w * v) * CFC.abs x)‖ ≤
          ‖w * v‖ * traceOneNorm τ x := norm_trace_mul_positive_le τ _ _ (CFC.abs_nonneg x)
      _ ≤ 1 * traceOneNorm τ x := mul_le_mul_of_nonneg_right
        ((norm_mul_le w v).trans (by nlinarith [norm_nonneg w, norm_nonneg v]))
        (traceOneNorm_nonneg τ x)
      _ = traceOneNorm τ x := one_mul _
  rw [hsplit, map_add]
  exact (norm_add_le _ _).trans (by linarith)

/-- Triangle inequality for the tracial one-norm. -/
theorem traceOneNorm_add_le (τ : FaithfulTracialState B) (x y : B) :
    traceOneNorm τ (x + y) ≤ traceOneNorm τ x + traceOneNorm τ y := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨v, hv, happ⟩ := traceOneNorm_approx_dual τ (x + y) hε
  have hx := (Complex.re_le_norm _).trans
    (norm_trace_mul_le_traceOneNorm τ (star v) x (by simpa only [norm_star] using hv))
  have hy := (Complex.re_le_norm _).trans
    (norm_trace_mul_le_traceOneNorm τ (star v) y (by simpa only [norm_star] using hv))
  rw [mul_add, map_add, Complex.add_re] at happ
  linarith

/-- Left multiplication by a contraction decreases the tracial one-norm. -/
theorem traceOneNorm_mul_left_le_of_norm_le_one (τ : FaithfulTracialState B)
    (a x : B) (ha : ‖a‖ ≤ 1) : traceOneNorm τ (a * x) ≤ traceOneNorm τ x := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨v, hv, happ⟩ := traceOneNorm_approx_dual τ (a * x) hε
  have hnorm : ‖star v * a‖ ≤ 1 := by
    refine (norm_mul_le _ _).trans ?_
    rw [norm_star]
    nlinarith [norm_nonneg v, norm_nonneg a]
  have hb := (Complex.re_le_norm _).trans
    (norm_trace_mul_le_traceOneNorm τ (star v * a) x hnorm)
  rw [mul_assoc] at hb
  linarith

/-- Right multiplication by a contraction decreases the tracial one-norm. -/
theorem traceOneNorm_mul_right_le_of_norm_le_one (τ : FaithfulTracialState B)
    (x a : B) (ha : ‖a‖ ≤ 1) : traceOneNorm τ (x * a) ≤ traceOneNorm τ x := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨v, hv, happ⟩ := traceOneNorm_approx_dual τ (x * a) hε
  have hnorm : ‖a * star v‖ ≤ 1 := by
    refine (norm_mul_le _ _).trans ?_
    rw [norm_star]
    nlinarith [norm_nonneg v, norm_nonneg a]
  have hb := (Complex.re_le_norm _).trans
    (norm_trace_mul_le_traceOneNorm τ (a * star v) x hnorm)
  have he : τ.toLinearMap (star v * (x * a)) = τ.toLinearMap ((a * star v) * x) := by
    rw [← mul_assoc, τ.tracial (star v * x) a, mul_assoc]
  rw [he] at happ
  linarith

/-- Conjugation by a partial isometry preserves the one-norm of an
operator supported on its initial projection. -/
theorem traceOneNorm_partialIsometry_conjugate (τ : FaithfulTracialState B)
    (w x : B) (hw : IsStarProjection (star w * w))
    (hxL : (star w * w) * x = x) (hxR : x * (star w * w) = x) :
    traceOneNorm τ (w * x * star w) = traceOneNorm τ x := by
  have hnorm : ‖w‖ ≤ 1 := by
    have hs : ‖w‖ ^ 2 ≤ 1 := by
      rw [pow_two, ← CStarRing.norm_star_mul_self]
      exact IsStarProjection.norm_le _ hw
    nlinarith [norm_nonneg w]
  have hnormStar : ‖star w‖ ≤ 1 := by simpa only [norm_star] using hnorm
  have he : star w * (w * x * star w) * w = x := by
    calc
      star w * (w * x * star w) * w = (star w * w) * x * (star w * w) := by noncomm_ring
      _ = x := by rw [hxL, hxR]
  apply le_antisymm
  · exact (traceOneNorm_mul_right_le_of_norm_le_one τ (w * x) (star w) hnormStar).trans
      (traceOneNorm_mul_left_le_of_norm_le_one τ w x hnorm)
  · calc
      traceOneNorm τ x = traceOneNorm τ (star w * (w * x * star w) * w) :=
        congrArg (traceOneNorm τ) he.symm
      _ ≤ traceOneNorm τ (w * x * star w) :=
        (traceOneNorm_mul_right_le_of_norm_le_one τ (star w * (w * x * star w)) w hnorm).trans
          (traceOneNorm_mul_left_le_of_norm_le_one τ (star w) (w * x * star w) hnormStar)

/-- Sandwich perturbation, with no selfadjointness requirements on the
three elements. -/
theorem traceOneNorm_sandwich_sub_le (τ : FaithfulTracialState B) (s e a : B) :
    traceOneNorm τ (s * a * s - e * a * e) ≤
      traceTwoNorm τ (s - e) * ‖a‖ * (traceTwoNorm τ s + traceTwoNorm τ e) := by
  have he : s * a * s - e * a * e = (s - e) * a * s + e * a * (s - e) := by
    noncomm_ring
  rw [he]
  have h1 := traceOneNorm_mul_le τ ((s - e) * a) s
  have h2 := traceOneNorm_mul_le τ (e * a) (s - e)
  have hm1 := mul_le_mul_of_nonneg_right (traceTwoNorm_mul_le_right τ (s - e) a)
    (traceTwoNorm_nonneg τ s)
  have hm2 := mul_le_mul_of_nonneg_right (traceTwoNorm_mul_le_right τ e a)
    (traceTwoNorm_nonneg τ (s - e))
  calc
    _ ≤ traceOneNorm τ ((s - e) * a * s) + traceOneNorm τ (e * a * (s - e)) :=
      traceOneNorm_add_le τ _ _
    _ ≤ (traceTwoNorm τ (s - e) * ‖a‖) * traceTwoNorm τ s +
        (traceTwoNorm τ e * ‖a‖) * traceTwoNorm τ (s - e) := by linarith
    _ = _ := by ring

end

end KadisonKastler

end OAI

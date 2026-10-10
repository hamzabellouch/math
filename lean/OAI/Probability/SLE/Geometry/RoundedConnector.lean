import OAI.Probability.SLE.Gauge.SerpentineCurve

namespace OAI

/-! The two quarter-circles used by the low connector from the real
boundary to the first serpentine column. The radius is measured in
ribbon-width units, so a radius at least fifty gives the same derivative
and tangent bounds as the array. -/

noncomputable section
open Set Metric
open scoped NNReal

namespace SLEExactGauge.Serpentine

def quarterLength (r : ℝ) : ℝ := Real.pi * r / 2

def quarterBend (r t : ℝ) : ℂ :=
  ((r / 50 : ℝ) : ℂ) * circularPiece 0 0 (50 * t / r)

def quarterTangent (r t : ℝ) : ℂ := circularTangent 0 (50 * t / r)

def upperQuarter (r t : ℝ) : ℂ :=
  ((r : ℂ) + (r : ℂ) * Complex.I) - quarterBend r (quarterLength r - t)

def upperQuarterTangent (r t : ℝ) : ℂ := quarterTangent r (quarterLength r - t)

lemma quarterBend_eq (r t : ℝ) :
    quarterBend r t = ((r - r * Real.cos (t / r) : ℝ) : ℂ) +
      ((r * Real.sin (t / r) : ℝ) : ℂ) * Complex.I := by
  have hs : side 0 = 1 := by simp [side]
  have he : 50 * t / r / 50 = t / r := by ring
  simp only [quarterBend, circularPiece, Nat.cast_zero, mul_zero, zero_add,
    hs, one_mul, he]
  push_cast
  ring

lemma quarterTangent_eq (r t : ℝ) :
    quarterTangent r t = (Real.sin (t / r) : ℂ) +
      (Real.cos (t / r) : ℂ) * Complex.I := by
  have hs : side 0 = 1 := by simp [side]
  have he : 50 * t / r / 50 = t / r := by ring
  simp only [quarterTangent, circularTangent, hs, one_mul, he]

lemma quarterBend_hasDerivAt {r : ℝ} (hr : 0 < r) (t : ℝ) :
    HasDerivAt (quarterBend r) (quarterTangent r t) t := by
  have ht : HasDerivAt (fun u : ℝ => 50 * u / r) (50 / r) t := by
    simpa using ((hasDerivAt_id t).const_mul 50).div_const r
  have hh := (circularPiece_hasDerivAt 0 0 (50 * t / r)).scomp t ht
  have hh' := hh.const_mul ((r / 50 : ℝ) : ℂ)
  convert hh' using 1 <;> try rfl
  change quarterTangent r t = ((r / 50 : ℝ) : ℂ) * ((50 / r : ℝ) • circularTangent 0 (50 * t / r))
  rw [Complex.real_smul, ← mul_assoc]
  have he : ((r / 50 : ℝ) : ℂ) * ((50 / r : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp [hr.ne']
  rw [he, one_mul]
  rfl

lemma quarterTangent_norm (r t : ℝ) : ‖quarterTangent r t‖ = 1 :=
  circularTangent_norm 0 _

lemma quarterTangent_lipschitz {r : ℝ} (hr : 50 ≤ r) :
    LipschitzWith (1 / 50) (quarterTangent r) := by
  have hr0 : 0 < r := by linarith
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro t u
  have hh := (circularTangent_lipschitz 0).dist_le_mul (50 * t / r) (50 * u / r)
  have he : dist (50 * t / r) (50 * u / r) = (50 / r) * dist t u := by
    have halg : 50 * t / r - 50 * u / r = (50 / r) * (t - u) := by ring
    rw [Real.dist_eq, Real.dist_eq, halg,
      abs_mul, abs_of_pos (div_pos (by norm_num) hr0)]
  have hfac : (50 : ℝ) / r ≤ 1 := (div_le_one hr0).mpr hr
  change dist (circularTangent 0 (50 * t / r)) (circularTangent 0 (50 * u / r)) ≤ _
  rw [he] at hh
  calc
    _ ≤ (1 / 50 : ℝ) * ((50 / r) * dist t u) := hh
    _ ≤ (1 / 50 : ℝ) * dist t u := by
      gcongr
      exact mul_le_of_le_one_left (dist_nonneg) hfac

lemma quarterBend_zero (r : ℝ) : quarterBend r 0 = 0 := by
  simp [quarterBend_eq]

lemma quarterTangent_zero (r : ℝ) : quarterTangent r 0 = Complex.I := by
  simp [quarterTangent_eq]

lemma quarterBend_end {r : ℝ} (hr : 0 < r) :
    quarterBend r (quarterLength r) = (r : ℂ) + (r : ℂ) * Complex.I := by
  have he : quarterLength r / r = Real.pi / 2 := by unfold quarterLength; field_simp [hr.ne']
  simp [quarterBend_eq, he]

lemma quarterTangent_end {r : ℝ} (hr : 0 < r) :
    quarterTangent r (quarterLength r) = 1 := by
  have he : quarterLength r / r = Real.pi / 2 := by unfold quarterLength; field_simp [hr.ne']
  simp [quarterTangent_eq, he]

lemma upperQuarter_hasDerivAt {r : ℝ} (hr : 0 < r) (t : ℝ) :
    HasDerivAt (upperQuarter r) (upperQuarterTangent r t) t := by
  have ht : HasDerivAt (fun u : ℝ => quarterLength r - u) (-1) t :=
    (hasDerivAt_id t).const_sub _
  have hh := ((quarterBend_hasDerivAt hr (quarterLength r - t)).scomp t ht).const_sub
    ((r : ℂ) + (r : ℂ) * Complex.I)
  convert hh using 1 <;> first | rfl | simp only [neg_smul, one_smul, neg_neg]
  rfl

lemma upperQuarterTangent_norm (r t : ℝ) : ‖upperQuarterTangent r t‖ = 1 :=
  quarterTangent_norm _ _

lemma upperQuarterTangent_lipschitz {r : ℝ} (hr : 50 ≤ r) :
    LipschitzWith (1 / 50) (upperQuarterTangent r) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro t u
  simpa only [upperQuarterTangent, dist_sub_left] using
    (quarterTangent_lipschitz hr).dist_le_mul (quarterLength r - t) (quarterLength r - u)

lemma upperQuarter_zero {r : ℝ} (hr : 0 < r) : upperQuarter r 0 = 0 := by
  simp [upperQuarter, quarterBend_end hr]

lemma upperQuarter_end {r : ℝ} :
    upperQuarter r (quarterLength r) = (r : ℂ) + (r : ℂ) * Complex.I := by
  simp [upperQuarter, quarterBend_zero]

lemma upperQuarterTangent_zero {r : ℝ} (hr : 0 < r) : upperQuarterTangent r 0 = 1 := by
  simp [upperQuarterTangent, quarterTangent_end hr]

lemma upperQuarterTangent_end (r : ℝ) :
    upperQuarterTangent r (quarterLength r) = Complex.I := by
  simp [upperQuarterTangent, quarterTangent_zero]

end SLEExactGauge.Serpentine

end

end OAI

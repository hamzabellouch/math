import OAI.NumberTheory.TwoPoint.Bounds.ResolventBounds

namespace OAI

/-!
# Noncommuting spectral transfer

The manuscript's Lemma `q:noncommuting`, in a form with any common upper
bound on the single-edge norms, the square function, and the spectral
radius. No commutation between distinct edges is assumed.
-/

open scoped BigOperators NNReal ENNReal

namespace TwoPointCorrelations

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

lemma projection_norm_apply_le (P : E →L[ℂ] E) (hP : IsSelfAdjoint P)
    (hPP : P * P = P) (v : E) : ‖P v‖ ≤ ‖v‖ := by
  have heq : inner ℂ (P v) (P v) = inner ℂ (P v) v := by
    have h := congrArg (fun T : E →L[ℂ] E => T v) hPP
    calc
      _ = inner ℂ (P (P v)) v := (hP.isSymmetric _ _).symm
      _ = _ := by
        simpa only [mul_apply_eq_comp] using congrArg (fun w => inner ℂ w v) h
  have hi := Complex.abs_re_le_norm (inner ℂ (P v) v)
  have hj := norm_inner_le_norm (𝕜 := ℂ) (P v) v
  have heq' : (inner ℂ (P v) v).re = ‖P v‖ ^ 2 := by
    rw [← heq, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  rw [heq', abs_of_nonneg (sq_nonneg _)] at hi
  by_cases hzero : ‖P v‖ = 0
  · simp [hzero]
  · have hp : 0 < ‖P v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    nlinarith [hi.trans hj]

lemma compression_norm_le_of_quadratic (S P : E →L[ℂ] E)
    (hS : IsSelfAdjoint S) (hP : IsSelfAdjoint P) (hPP : P * P = P)
    (c : ℝ) (hc : 0 ≤ c)
    (hform : ∀ v : E, P v = v → |(inner ℂ (S v) v).re| ≤ c * ‖v‖ ^ 2) :
    ‖P * S * P‖ ≤ c := by
  have hself : IsSelfAdjoint (P * S * P) := by
    change star (P * S * P) = P * S * P
    simp only [star_mul, hP.star_eq, hS.star_eq, mul_assoc]
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ hself.isSymmetric]
  apply ciSup_le
  intro v
  have hPv : P (P v) = P v := by
    simpa only [mul_apply_eq_comp] using
      congrArg (fun T : E →L[ℂ] E => T v) hPP
  have hbound := hform (P v) hPv
  have hnorm := projection_norm_apply_le P hP hPP v
  have heq : inner ℂ ((P * S * P) v) v = inner ℂ (S (P v)) (P v) := by
    simp only [mul_apply_eq_comp]
    exact hP.isSymmetric _ _
  by_cases hv : v = 0
  · simpa [hv] using hc
  · have hvp : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
    simp only [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply, heq, abs_div, abs_sq]
    apply (div_le_iff₀ hvp).mpr
    exact hbound.trans (mul_le_mul_of_nonneg_left
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hnorm) hc)

/-- A common-bound version of the noncommuting transfer lemma. -/
theorem noncommuting_spectral_transfer
    (B : ι → E →L[ℂ] E) (hB : ∀ i, IsSelfAdjoint (B i))
    (P : E →L[ℂ] E) (hP : IsSelfAdjoint P) (hPP : P * P = P)
    (m : ℝ≥0) (hnorm : ∀ i, ‖B i‖ ≤ (m : ℝ))
    (hsq : ∀ v : E, P v = v → ∑ i, ‖B i v‖ ^ 2 ≤ (m : ℝ) ^ 2 * ‖v‖ ^ 2)
    (hrad : spectralRadius ℂ (nonbacktrackingContinuous B) ≤ (m : ℝ≥0∞)) :
    ‖P * (∑ i, B i) * P‖ ≤ 3 * (m : ℝ) := by
  nontriviality E
  by_cases hm : m = 0
  · have hzero (i : ι) : B i = 0 := norm_eq_zero.mp (le_antisymm (by simpa [hm] using hnorm i) (norm_nonneg _))
    simp [hzero, hm]
  have hmpos : 0 < m := pos_iff_ne_zero.mpr hm
  have hmr : 0 < (m : ℝ) := by exact_mod_cast hmpos
  let t : ℝ := (2 * (m : ℝ))⁻¹
  have ht : 0 < t := by positivity
  have htm : t * (m : ℝ) = 1 / 2 := by dsimp [t]; field_simp
  have htinv : t < (m : ℝ)⁻¹ := by
    dsimp [t]
    exact (inv_lt_inv₀ (by positivity) hmr).mpr (by linarith)
  have hsmall (u : ℝ) (hu : |u| ≤ t) (i : ι) : ‖u • B i‖ ≤ 1 / 2 := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |u| * ‖B i‖ ≤ t * (m : ℝ) := mul_le_mul hu (hnorm i) (norm_nonneg _) ht.le
      _ = _ := htm
  have hform (v : E) (hv : P v = v) :
      |(inner ℂ (∑ i, B i v) v).re| ≤ 3 * (m : ℝ) * ‖v‖ ^ 2 := by
    have hpositive (u : ℝ) (hu : |u| = t) (w : E) :
        0 ≤ (inner ℂ (transferResolvent B u w) w).re := by
      by_cases hw : w = 0
      · simp [hw]
      · apply (transferResolvent_positive_abs B hB u
          (fun s hs i => (hsmall s (hs.trans_eq hu) i).trans_lt (by norm_num))
          (fun s hs => nonbacktracking_resolvent_isUnit B m hmpos hrad s
            ((hs.trans_eq hu).trans_lt htinv)) w hw).le
    have h := edge_sum_quadratic_bound B hB t m ht (hsmall t (by rw [abs_of_pos ht]))
      (hpositive t (abs_of_pos ht))
      (hpositive (-t) (by simp [abs_of_pos ht])) v (hsq v hv)
    have hc : (1 + 2 * t ^ 2 * (m : ℝ) ^ 2) / t = 3 * (m : ℝ) := by
      dsimp [t]
      field_simp
      ring
    simpa only [hc] using h
  apply compression_norm_le_of_quadratic (∑ i, B i) P
    (isSelfAdjoint_sum _ (fun i _ => hB i)) hP hPP (3 * (m : ℝ)) (by positivity)
  intro v hv
  simpa only [sum_apply] using hform v hv

/-- Lemma `q:noncommuting`, with its three separate bounds. The spectral
radius is finite because the operator is bounded. -/
theorem noncommuting_spectral_transfer_max
    (B : ι → E →L[ℂ] E) (hB : ∀ i, IsSelfAdjoint (B i))
    (P : E →L[ℂ] E) (hP : IsSelfAdjoint P) (hPP : P * P = P)
    (a b : ℝ≥0) (hnorm : ∀ i, ‖B i‖ ≤ (a : ℝ))
    (hsq : ∀ v : E, P v = v → ∑ i, ‖B i v‖ ^ 2 ≤ (b : ℝ) ^ 2 * ‖v‖ ^ 2) :
    ‖P * (∑ i, B i) * P‖ ≤
      3 * ((max (max a b) ((spectralRadius ℂ (nonbacktrackingContinuous B)).toNNReal) : ℝ≥0) : ℝ) := by
  let ρ := (spectralRadius ℂ (nonbacktrackingContinuous B)).toNNReal
  let m := max (max a b) ρ
  have ha : (a : ℝ) ≤ (m : ℝ) := NNReal.coe_le_coe.mpr
    ((le_max_left a b).trans (le_max_left (max a b) ρ))
  have hb : (b : ℝ) ≤ (m : ℝ) := NNReal.coe_le_coe.mpr
    ((le_max_right a b).trans (le_max_left (max a b) ρ))
  have hfinite : spectralRadius ℂ (nonbacktrackingContinuous B) ≠ ⊤ :=
    ne_of_lt ((spectralRadius_le_nnnorm (𝕜 := ℂ) (nonbacktrackingContinuous B)).trans_lt
      ENNReal.coe_lt_top)
  apply noncommuting_spectral_transfer B hB P hP hPP m (fun i => (hnorm i).trans ha)
  · intro v hv
    apply (hsq v hv).trans
    exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ b.coe_nonneg m.coe_nonneg).mpr hb) (sq_nonneg _)
  · rw [← ENNReal.coe_toNNReal hfinite]
    exact ENNReal.coe_le_coe.mpr (le_max_right (max a b) ρ)

end TwoPointCorrelations

end OAI

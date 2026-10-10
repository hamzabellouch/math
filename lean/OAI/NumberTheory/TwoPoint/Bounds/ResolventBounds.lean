import OAI.NumberTheory.TwoPoint.Bounds.ResolventTransfer

namespace OAI

/-!
# Quadratic-form bounds for the noncommuting resolvent

The correction is estimated using the norm of each individual resolvent.
This avoids imposing any commutation relation between distinct edges.
-/

open scoped BigOperators

namespace TwoPointCorrelations

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem transferResolvent_positive_abs [Nontrivial E] (B : ι → E →L[ℂ] E)
    (hB : ∀ i, IsSelfAdjoint (B i)) (t : ℝ)
    (hsmall : ∀ u : ℝ, |u| ≤ |t| → ∀ i, ‖u • B i‖ < 1)
    (hH : ∀ u : ℝ, |u| ≤ |t| →
      IsUnit (1 - (u : ℂ) • nonbacktrackingContinuous B)) :
    ∀ v : E, v ≠ 0 → 0 < (inner ℂ (transferResolvent B t v) v).re := by
  have hu (u : ℝ) (h : |u| ≤ |t|) (i : ι) : IsUnit (1 + u • B i) :=
    isUnit_edge_shift _ _ (hsmall u h i)
  have hmul (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) : |s * t| ≤ |t| := by
    rw [abs_mul, abs_of_nonneg hs.1]
    exact mul_le_of_le_one_left (abs_nonneg t) hs.2
  have hc := transferResolvent_continuousOn B (-|t|) |t|
    (fun u hu' i => hu u (abs_le.mpr hu') i)
  have hpath : ContinuousOn (fun s : ℝ => transferResolvent B (s * t))
      (Set.Icc 0 1) := hc.comp (by fun_prop) (fun s hs => abs_le.mp (hmul s hs))
  have h := selfAdjoint_path_positive (fun s : ℝ => transferResolvent B (s * t)) 0 1
    zero_le_one hpath (by ext v; simp [transferResolvent])
    (fun s hs => (transferResolvent_selfAdjoint B hB (s * t)
      (hu (s * t) (hmul s hs))).isSymmetric)
    (fun s hs => transferResolvent_injective B (s * t)
      (hu (s * t) (hmul s hs)) (hH (s * t) (hmul s hs)))
  simpa only [one_mul] using h

omit [DecidableEq ι] [FiniteDimensional ℂ E] in
theorem transferResolvent_apply_expansion (B : ι → E →L[ℂ] E) (u : ℝ)
    (hunit : ∀ i, IsUnit (1 + u • B i)) (v : E) :
    transferResolvent B u v = v - u • (∑ i, B i v) +
      u ^ 2 • (∑ i, B i (B i (edgeResolvent (B i) u v))) := by
  have hi (i : ι) : u • B i (edgeResolvent (B i) u v) =
      u • B i v - u ^ 2 • B i (B i (edgeResolvent (B i) u v)) := by
    have hR := congrArg (fun T : E →L[ℂ] E => T v) (edgeResolvent_mul (B i) u (hunit i))
    have h := congrArg (fun z : E => u • B i z) hR
    simp only [add_apply, one_apply_eq_self, smul_apply, mul_apply_eq_comp,
      map_add, ContinuousLinearMap.map_smul_of_tower, smul_add, smul_smul, ← pow_two] at h
    exact eq_sub_of_add_eq h
  simp only [transferResolvent, sub_apply, one_apply_eq_self, sum_apply,
    smul_apply, mul_apply_eq_comp]
  simp_rw [hi]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, ← Finset.smul_sum]
  abel

omit [DecidableEq ι] in
theorem resolventCorrection_bound [Nontrivial E] (B : ι → E →L[ℂ] E)
    (hB : ∀ i, IsSelfAdjoint (B i)) (u : ℝ)
    (hsmall : ∀ i, ‖u • B i‖ ≤ 1 / 2) (v : E) :
    |(inner ℂ (∑ i, B i (B i (edgeResolvent (B i) u v))) v).re| ≤
      2 * ∑ i, ‖B i v‖ ^ 2 := by
  have hi (i : ι) : |(inner ℂ (B i (B i (edgeResolvent (B i) u v))) v).re| ≤
      2 * ‖B i v‖ ^ 2 := by
    have hu := isUnit_edge_shift (B i) u ((hsmall i).trans_lt (by norm_num))
    have hc := congrArg (fun T : E →L[ℂ] E => T v) (edgeResolvent_commute (B i) u hu)
    have heq : inner ℂ (B i (B i (edgeResolvent (B i) u v))) v =
        inner ℂ (edgeResolvent (B i) u (B i v)) (B i v) := by
      calc
        _ = inner ℂ (B i (edgeResolvent (B i) u v)) (B i v) := (hB i).isSymmetric _ _
        _ = _ := by
          simpa only [mul_apply_eq_comp] using congrArg (fun w => inner ℂ w (B i v)) hc
    rw [heq]
    calc
      |(inner ℂ (edgeResolvent (B i) u (B i v)) (B i v)).re| ≤
          ‖inner ℂ (edgeResolvent (B i) u (B i v)) (B i v)‖ := Complex.abs_re_le_norm _
      _ ≤ ‖edgeResolvent (B i) u (B i v)‖ * ‖B i v‖ := norm_inner_le_norm _ _
      _ ≤ (2 * ‖B i v‖) * ‖B i v‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (edgeResolvent_norm_le_two (B i) u (hsmall i))
            (norm_nonneg _))
      _ = 2 * ‖B i v‖ ^ 2 := by ring
  simp only [sum_inner, Complex.re_sum]
  calc
    |∑ i, (inner ℂ (B i (B i (edgeResolvent (B i) u v))) v).re| ≤
        ∑ i, |(inner ℂ (B i (B i (edgeResolvent (B i) u v))) v).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, 2 * ‖B i v‖ ^ 2 := Finset.sum_le_sum (fun i _ => hi i)
    _ = _ := (Finset.mul_sum ..).symm

omit [DecidableEq ι] [FiniteDimensional ℂ E] in
theorem transferResolvent_inner_expansion (B : ι → E →L[ℂ] E) (u : ℝ)
    (hunit : ∀ i, IsUnit (1 + u • B i)) (v : E) :
    (inner ℂ (transferResolvent B u v) v).re = ‖v‖ ^ 2 -
      u * (inner ℂ (∑ i, B i v) v).re +
      u ^ 2 * (inner ℂ (∑ i, B i (B i (edgeResolvent (B i) u v))) v).re := by
  rw [transferResolvent_apply_expansion B u hunit v]
  simp only [inner_add_left, inner_sub_left, inner_smul_left_eq_star_smul,
    Complex.add_re, Complex.sub_re, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

omit [DecidableEq ι] in
/-- Positivity of the resolvent at both endpoints controls the quadratic
form of the edge sum on each vector satisfying the square-function bound. -/
theorem edge_sum_quadratic_bound [Nontrivial E] (B : ι → E →L[ℂ] E)
    (hB : ∀ i, IsSelfAdjoint (B i)) (t b : ℝ) (ht : 0 < t)
    (hsmall : ∀ i, ‖t • B i‖ ≤ 1 / 2)
    (hplus : ∀ v : E, 0 ≤ (inner ℂ (transferResolvent B t v) v).re)
    (hminus : ∀ v : E, 0 ≤ (inner ℂ (transferResolvent B (-t) v) v).re)
    (v : E) (hsq : ∑ i, ‖B i v‖ ^ 2 ≤ b ^ 2 * ‖v‖ ^ 2) :
    |(inner ℂ (∑ i, B i v) v).re| ≤ ((1 + 2 * t ^ 2 * b ^ 2) / t) * ‖v‖ ^ 2 := by
  have hsmallNeg (i : ι) : ‖(-t) • B i‖ ≤ 1 / 2 := by simpa using hsmall i
  have hup := (resolventCorrection_bound B hB t hsmall v).trans (mul_le_mul_of_nonneg_left hsq (by norm_num))
  have hum := (resolventCorrection_bound B hB (-t) hsmallNeg v).trans (mul_le_mul_of_nonneg_left hsq (by norm_num))
  have hp := hplus v
  have hm := hminus v
  rw [transferResolvent_inner_expansion B t
    (fun i => isUnit_edge_shift _ _ ((hsmall i).trans_lt (by norm_num)))] at hp
  rw [transferResolvent_inner_expansion B (-t)
    (fun i => isUnit_edge_shift _ _ ((hsmallNeg i).trans_lt (by norm_num)))] at hm
  rw [abs_le] at hup hum ⊢
  have hup' := mul_le_mul_of_nonneg_left hup.2 (sq_nonneg t)
  have hum' := mul_le_mul_of_nonneg_left hum.2 (sq_nonneg t)
  rw [div_mul_eq_mul_div]
  constructor
  · rw [← neg_div]
    apply (div_le_iff₀ ht).mpr
    nlinarith only [hm, hum']
  · apply (le_div_iff₀ ht).mpr
    nlinarith only [hp, hup']

end TwoPointCorrelations

end OAI

import OAI.Analysis.LipschitzHilbert.Estimates.ExponentialVariation

namespace OAI

/-! Variation of differences of exponential endpoint weights. The bound
is polynomial in logarithmic variation; it never exponentiates the size
of a top's logarithmic loss. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

private def complexSegment (a b : ℂ) (t : ℝ) : ℂ := (1-t) • a + t • b

private theorem complexSegment_re_le (a b : ℂ) (C t : ℝ)
    (ha : a.re ≤ C) (hb : b.re ≤ C) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (complexSegment a b t).re ≤ C := by
  simp only [complexSegment, Complex.add_re, Complex.smul_re, smul_eq_mul]
  nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr ha),
    mul_nonneg ht0 (sub_nonneg.mpr hb)]

private theorem complexSegment_difference (a b c d : ℂ) (D t : ℝ)
    (ha : ‖c-a‖ ≤ D) (hb : ‖d-b‖ ≤ D) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖complexSegment c d t-complexSegment a b t‖ ≤ D := by
  have heq : complexSegment c d t-complexSegment a b t =
      (1-t) • (c-a) + t • (d-b) := by simp [complexSegment, smul_sub]; abel
  rw [heq]
  calc
    _ ≤ ‖(1-t) • (c-a)‖ + ‖t • (d-b)‖ := norm_add_le _ _
    _ = (1-t)*‖c-a‖ + t*‖d-b‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr ht1), abs_of_nonneg ht0]
    _ ≤ (1-t)*D + t*D := add_le_add
      (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr ht1))
      (mul_le_mul_of_nonneg_left hb ht0)
    _ = D := by ring

private theorem hasDerivAt_complexSegment (a b : ℂ) (t : ℝ) :
    HasDerivAt (complexSegment a b) (b-a) t := by
  have h := (((hasDerivAt_const t (1:ℝ)).fun_sub (hasDerivAt_id t)).smul_const a).fun_add
    ((hasDerivAt_id t).smul_const b)
  change HasDerivAt (fun y : ℝ => (1-y) • a+y • b) (b-a) t
  convert h using 1 <;> simp [neg_add_eq_sub]

/-- A four-point exponential estimate on a left half-plane. Only the
uniform real-part bound is exponentiated. -/
theorem exp_increment_difference_bound (a b c d : ℂ) (C D : ℝ)
    (ha : a.re ≤ C) (hb : b.re ≤ C) (hc : c.re ≤ C) (hd : d.re ≤ C)
    (hac : ‖c-a‖ ≤ D) (hbd : ‖d-b‖ ≤ D) :
    ‖(Complex.exp d-Complex.exp c)-(Complex.exp b-Complex.exp a)‖ ≤
      Real.exp C*(‖(d-c)-(b-a)‖+D*‖b-a‖) := by
  let F := fun t : ℝ => Complex.exp (complexSegment c d t)-
    Complex.exp (complexSegment a b t)
  let F' := fun t : ℝ => Complex.exp (complexSegment c d t)*(d-c)-
    Complex.exp (complexSegment a b t)*(b-a)
  have hderiv (t : ℝ) : HasDerivAt F (F' t) t :=
    (hasDerivAt_complexSegment c d t).cexp.sub (hasDerivAt_complexSegment a b t).cexp
  have hbound (t : ℝ) (ht : t ∈ Set.Ico (0:ℝ) 1) :
      ‖F' t‖ ≤ Real.exp C*(‖(d-c)-(b-a)‖+D*‖b-a‖) := by
    have hcd := complexSegment_re_le c d C t hc hd ht.1 ht.2.le
    have hab := complexSegment_re_le a b C t ha hb ht.1 ht.2.le
    have hdiff := (norm_exp_sub_le_of_re_le (complexSegment a b t)
      (complexSegment c d t) C hab hcd).trans
      (mul_le_mul_of_nonneg_left
        (complexSegment_difference a b c d D t hac hbd ht.1 ht.2.le)
        (Real.exp_pos C).le)
    have hexp : ‖Complex.exp (complexSegment c d t)‖ ≤ Real.exp C := by
      rw [Complex.norm_exp]
      exact Real.exp_le_exp.mpr hcd
    have heq : F' t = Complex.exp (complexSegment c d t)*((d-c)-(b-a)) +
        (Complex.exp (complexSegment c d t)-Complex.exp (complexSegment a b t))*(b-a) := by
      dsimp [F']; ring
    rw [heq]
    calc
      _ ≤ ‖Complex.exp (complexSegment c d t)*((d-c)-(b-a))‖ +
          ‖(Complex.exp (complexSegment c d t)-Complex.exp (complexSegment a b t))*(b-a)‖ :=
        norm_add_le _ _
      _ ≤ Real.exp C*‖(d-c)-(b-a)‖ + (Real.exp C*D)*‖b-a‖ := by
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_right hexp (norm_nonneg _))
          (mul_le_mul_of_nonneg_right hdiff (norm_nonneg _))
      _ = _ := by ring
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hderiv t).hasDerivWithinAt) hbound
  have heq : (Complex.exp d-Complex.exp c)-(Complex.exp b-Complex.exp a) =
      (Complex.exp d-Complex.exp b)-(Complex.exp c-Complex.exp a) := by ring
  rw [heq]
  simpa only [F, complexSegment, sub_self, zero_smul, one_smul, zero_add,
    sub_zero, add_zero] using h

/-- The endpoint-plus-variation norm of a moving exponential difference
is controlled by the logarithmic differences and their variation. -/
theorem exponential_sequence_difference_variation (L M : ℕ → ℂ) (N : ℕ)
    (C D V W : ℝ) (hD : 0 ≤ D)
    (hL : ∀ j ≤ N, (L j).re ≤ C) (hM : ∀ j ≤ N, (M j).re ≤ C)
    (hdiff : ∀ j ≤ N, ‖M j-L j‖ ≤ D)
    (hvar : (∑ j ∈ Finset.range N, ‖L (j+1)-L j‖) ≤ V)
    (hdvar : (∑ j ∈ Finset.range N, ‖(M (j+1)-M j)-(L (j+1)-L j)‖) ≤ W) :
    ‖Complex.exp (M N)-Complex.exp (L N)‖ +
      (∑ j ∈ Finset.range N,
        ‖(Complex.exp (M (j+1))-Complex.exp (L (j+1)))-
          (Complex.exp (M j)-Complex.exp (L j))‖) ≤
      Real.exp C*(D+W+D*V) := by
  have hend := (norm_exp_sub_le_of_re_le (L N) (M N) C (hL N le_rfl) (hM N le_rfl)).trans
    (mul_le_mul_of_nonneg_left (hdiff N le_rfl) (Real.exp_pos C).le)
  have hsum : (∑ j ∈ Finset.range N,
      ‖(Complex.exp (M (j+1))-Complex.exp (L (j+1)))-
        (Complex.exp (M j)-Complex.exp (L j))‖) ≤ Real.exp C*(W+D*V) := by
    calc
      _ ≤ ∑ j ∈ Finset.range N, Real.exp C*
          (‖(M (j+1)-M j)-(L (j+1)-L j)‖+D*‖L (j+1)-L j‖) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjN := Finset.mem_range.mp hj
        have heq : (Complex.exp (M (j+1))-Complex.exp (L (j+1)))-
            (Complex.exp (M j)-Complex.exp (L j)) =
            (Complex.exp (M (j+1))-Complex.exp (M j))-
            (Complex.exp (L (j+1))-Complex.exp (L j)) := by ring
        rw [heq]
        exact exp_increment_difference_bound (L j) (L (j+1)) (M j) (M (j+1)) C D
          (hL j (by omega)) (hL (j+1) (by omega)) (hM j (by omega))
          (hM (j+1) (by omega)) (hdiff j (by omega)) (hdiff (j+1) (by omega))
      _ = Real.exp C*((∑ j ∈ Finset.range N, ‖(M (j+1)-M j)-(L (j+1)-L j)‖) +
          D*(∑ j ∈ Finset.range N, ‖L (j+1)-L j‖)) := by
        simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
      _ ≤ Real.exp C*(W+D*V) := mul_le_mul_of_nonneg_left
        (add_le_add hdvar (mul_le_mul_of_nonneg_left hvar hD)) (Real.exp_pos C).le
  calc
    _ ≤ Real.exp C*D + Real.exp C*(W+D*V) := add_le_add hend hsum
    _ = _ := by ring

end LipschitzHilbert

end

end OAI

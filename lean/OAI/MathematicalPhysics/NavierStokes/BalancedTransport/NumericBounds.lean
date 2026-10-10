import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.NumericPrograms

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity

lemma exp_difference_bound {x y T : ℝ} (hx : x ≤ T) (hy : y ≤ T) :
    |Real.exp x - Real.exp y| ≤ Real.exp T * |x - y| := by
  simpa only [Real.norm_eq_abs] using
    (convex_Iic T).norm_image_sub_le_of_norm_deriv_le
      (fun z _ => Real.differentiableAt_exp) (fun z hz => by
        rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr hz) hy hx

lemma exp_nat_bound (n : ℕ) : Real.exp (n : ℝ) ≤ (3 : ℝ) ^ n := by
  rw [← mul_one (n : ℝ), Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos _).le (by linarith [Real.exp_one_lt_d9]) _

lemma clipped_inverse_bound {x q c : ℝ} (hc : 0 < c) (hx : c ≤ x) :
    |(max c q)⁻¹ - x⁻¹| ≤ c⁻¹ ^ 2 * |q - x| := by
  have hm : c ≤ max c q := le_max_left _ _
  have hmp := hc.trans_le hm
  have hxp := hc.trans_le hx
  have hdist : |max c q - x| ≤ |q - x| := by
    rcases le_total c q with h | h
    · rw [max_eq_right h]
    · rw [max_eq_left h, abs_of_nonpos (sub_nonpos.mpr hx),
        abs_of_nonpos (sub_nonpos.mpr (h.trans hx))]
      linarith
  have hlow : c*c ≤ max c q * x := mul_le_mul hm hx hc.le hmp.le
  calc
    |(max c q)⁻¹ - x⁻¹| = |max c q - x| / (max c q * x) := by
      rw [inv_sub_inv hmp.ne' hxp.ne', abs_div,
        abs_of_pos (mul_pos hmp hxp), abs_sub_comm]
    _ ≤ |q - x| / (c*c) := div_le_div₀ (abs_nonneg _) hdist (mul_pos hc hc) hlow
    _ = c⁻¹ ^ 2 * |q - x| := by rw [div_eq_mul_inv, mul_inv_rev]; ring

structure RegisterEstimate (p : ℕ) (s : List ℝ) (q : List ℚ) (b : List (ℕ × ℕ)) : Prop where
  magnitude : ∀ j, |s.getD j 0| ≤ ((b.getD j (0,0)).1 : ℝ)
  accuracy : ∀ j, |(q.getD j 0 : ℝ) - s.getD j 0| ≤ ((b.getD j (0,0)).2 : ℝ) * error p

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp

lemma estimate (d : ℕ) [NeZero d] (o : NumericOp) (x : Fin d → ℚ)
    (p C : ℕ) (s : List ℝ) (q : List ℚ) (b : List (ℕ × ℕ))
    (hi : ∀ i, |(x i : ℝ)| ≤ C) (hb : RegisterEstimate p s q b) (hv : Valid o s) :
    |real d o (fun i => (x i : ℝ)) s| ≤ ((bound o C b).1 : ℝ) ∧
    |(rational d o x p q : ℝ) - real d o (fun i => (x i : ℝ)) s| ≤
      ((bound o C b).2 : ℝ) * error p := by
  rcases o with ⟨j,r,a,b'⟩
  have hA := hb.magnitude a
  have hB := hb.magnitude b'
  have hE := hb.accuracy a
  have hF := hb.accuracy b'
  have herr := error_nonneg p
  have herr1 := error_le_one p
  have hsize : |(q.getD a 0 : ℝ)| ≤ ((b.getD a (0,0)).1 : ℝ) +
      ((b.getD a (0,0)).2 : ℝ) := by
    calc
      _ ≤ |(q.getD a 0 : ℝ) - s.getD a 0| + |s.getD a 0| :=
        by simpa only [sub_add_cancel] using abs_add_le ((q.getD a 0 : ℝ) - s.getD a 0) (s.getD a 0)
      _ ≤ ((b.getD a (0,0)).2 : ℝ) * error p + ((b.getD a (0,0)).1 : ℝ) :=
        add_le_add hE hA
      _ ≤ _ := by nlinarith [Nat.cast_nonneg (b.getD a (0,0)).2 (α := ℝ)]
  fin_cases j <;> simp only [real, rational, rationalCase, bound, boundCase, tag, rat, left, right, Valid] at hv ⊢
  · exact ⟨rat_abs_le_num r, by simp⟩
  · exact ⟨hi _, by simp⟩
  · constructor
    · simpa only [Nat.cast_add] using (abs_add_le _ _).trans (add_le_add hA hB)
    · push_cast
      have he : (q.getD a 0 : ℝ) + (q.getD b' 0 : ℝ) - (s.getD a 0 + s.getD b' 0) =
          ((q.getD a 0 : ℝ) - s.getD a 0) + ((q.getD b' 0 : ℝ) - s.getD b' 0) := by ring
      rw [he, add_mul]
      exact (abs_add_le _ _).trans (add_le_add hE hF)
  · constructor
    · simpa only [Nat.cast_mul, abs_mul] using
        mul_le_mul hA hB (abs_nonneg _) (by positivity)
    · push_cast
      have he : (q.getD a 0 : ℝ) * (q.getD b' 0 : ℝ) - s.getD a 0 * s.getD b' 0 =
          (q.getD a 0 : ℝ) * ((q.getD b' 0 : ℝ) - s.getD b' 0) +
          s.getD b' 0 * ((q.getD a 0 : ℝ) - s.getD a 0) := by ring
      rw [he]
      calc
        _ ≤ |(q.getD a 0 : ℝ)| * |(q.getD b' 0 : ℝ) - s.getD b' 0| +
            |s.getD b' 0| * |(q.getD a 0 : ℝ) - s.getD a 0| := by
          simpa only [abs_mul] using abs_add_le
            ((q.getD a 0 : ℝ) * ((q.getD b' 0 : ℝ) - s.getD b' 0))
            (s.getD b' 0 * ((q.getD a 0 : ℝ) - s.getD a 0))
        _ ≤ (((b.getD a (0,0)).1 : ℝ) + (b.getD a (0,0)).2) *
            ((b.getD b' (0,0)).2 * error p) +
            (b.getD b' (0,0)).1 * ((b.getD a (0,0)).2 * error p) :=
          add_le_add (mul_le_mul hsize hF (abs_nonneg _) (by positivity))
            (mul_le_mul hB hE (abs_nonneg _) (by positivity))
        _ = _ := by ring
  · constructor
    · simpa only [abs_neg] using hA
    · simpa only [Rat.cast_neg, neg_sub_neg, abs_sub_comm] using hE
  · have hh := hv rfl
    have hpos : (0 : ℝ) < ((b' + 1 : ℕ) : ℝ)⁻¹ := by positivity
    constructor
    · rw [abs_inv, abs_of_pos (hpos.trans_le hh)]
      have h := inv_anti₀ hpos hh
      simpa only [inv_inv] using h
    · push_cast
      have hh' := clipped_inverse_bound (q := (q.getD a 0 : ℝ)) hpos hh
      simp only [inv_inv] at hh'
      have hcast : max ((b' : ℝ) + 1)⁻¹ (q.getD a 0 : ℝ) =
          max (((b'+1 : ℕ) : ℝ)⁻¹) (q.getD a 0 : ℝ) := by norm_cast
      rw [hcast]
      calc
        _ ≤ (((b'+1 : ℕ) : ℝ) ^ 2) * |(q.getD a 0 : ℝ) - s.getD a 0| := hh'
        _ ≤ (((b'+1 : ℕ) : ℝ) ^ 2) * ((b.getD a (0,0)).2 * error p) :=
          mul_le_mul_of_nonneg_left hE (sq_nonneg _)
        _ = _ := by push_cast; ring
  · constructor
    · exact rhoJet_bound_computable _ _
    · have hL := (rhoJet_lipschitz a).dist_le_mul (q.getD b' 0 : ℝ) (s.getD b' 0)
      simp only [Real.dist_eq, NNReal.coe_natCast] at hL
      calc
        _ ≤ |(rhoApprox a (q.getD b' 0) p : ℝ) - rhoJet a (q.getD b' 0 : ℝ)| +
            |rhoJet a (q.getD b' 0 : ℝ) - rhoJet a (s.getD b' 0)| := abs_sub_le _ _ _
        _ ≤ error p + (rhoBound (a + 1) 0 : ℝ) * |(q.getD b' 0 : ℝ) - s.getD b' 0| :=
          add_le_add (rhoApprox_spec _ _ _) hL
        _ ≤ error p + (rhoBound (a + 1) 0 : ℝ) * ((b.getD b' (0,0)).2 * error p) :=
          add_le_add_right (mul_le_mul_of_nonneg_left hF (Nat.cast_nonneg _)) _
        _ = _ := by push_cast; ring
  · constructor
    · rw [abs_of_pos (Real.exp_pos _), Nat.cast_pow, Nat.cast_ofNat]
      exact (Real.exp_le_exp.mpr (le_abs_self _ |>.trans hA)).trans (exp_nat_bound _)
    · have hL := exp_difference_bound (le_abs_self _ |>.trans hsize)
        ((le_abs_self _ |>.trans hA).trans (le_add_of_nonneg_right (Nat.cast_nonneg _)))
      have hL' : |Real.exp (q.getD a 0 : ℝ) - Real.exp (s.getD a 0)| ≤
          (3 : ℝ)^((b.getD a (0,0)).1 + (b.getD a (0,0)).2) *
            ((b.getD a (0,0)).2 * error p) := by
        have hh : Real.exp ((b.getD a (0,0)).1 + (b.getD a (0,0)).2) ≤
            (3 : ℝ) ^ ((b.getD a (0,0)).1 + (b.getD a (0,0)).2) := by
          simpa only [Nat.cast_add] using exp_nat_bound ((b.getD a (0,0)).1 + (b.getD a (0,0)).2)
        exact hL.trans (mul_le_mul hh hE (abs_nonneg _) (by positivity))
      calc
        _ ≤ |(expApprox (q.getD a 0) p : ℝ) - Real.exp (q.getD a 0 : ℝ)| +
            |Real.exp (q.getD a 0 : ℝ) - Real.exp (s.getD a 0)| := abs_sub_le _ _ _
        _ ≤ error p + (3 : ℝ)^((b.getD a (0,0)).1 + (b.getD a (0,0)).2) *
            ((b.getD a (0,0)).2 * error p) := add_le_add (expApprox_spec _ _) hL'
        _ = _ := by push_cast; ring
  · change (|if 0 < r then Real.log (r : ℝ) else 0| ≤ ↑(r.num.natAbs + r⁻¹.num.natAbs)) ∧
      (|(logApprox r p : ℝ) - (if 0 < r then Real.log (r : ℝ) else 0)| ≤ ((1 : ℕ) : ℝ) * error p)
    by_cases hr : 0 < r
    · rw [ite_eq_left hr]
      exact ⟨log_abs_bound hr, by simpa using logApprox_spec hr p⟩
    · rw [ite_eq_right hr]
      exact ⟨by simpa only [abs_zero] using
        (Nat.cast_nonneg (r.num.natAbs + r⁻¹.num.natAbs) (α := ℝ)),
        by simp [logApprox, hr, error_nonneg]⟩

end BalancedTransport.Effectivity.NumericOp
end

end OAI

import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SumIntegralError

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset

namespace OrdinaryLogIntegral

noncomputable def tent (a H x : ℝ) : ℝ := max 0 (1 - |x-(a+H)|/H)

lemma tent_nonneg (a H x : ℝ) : 0 ≤ tent a H x := le_max_left _ _

lemma tent_le_one (a H x : ℝ) (hH : 0 < H) : tent a H x ≤ 1 := by
  unfold tent
  exact max_le (by norm_num) (by have := div_nonneg (abs_nonneg (x-(a+H))) hH.le; linarith)

lemma tent_zero_left (a H x : ℝ) (hH : 0 < H) (hx : x ≤ a) : tent a H x = 0 := by
  unfold tent
  rw [max_eq_left]
  rw [abs_of_nonpos (by linarith)]
  apply sub_nonpos.mpr
  exact (le_div_iff₀ hH).mpr (by linarith)

lemma tent_zero_right (a H x : ℝ) (hH : 0 < H) (hx : a+2*H ≤ x) : tent a H x = 0 := by
  unfold tent
  rw [max_eq_left]
  rw [abs_of_nonneg (by linarith)]
  apply sub_nonpos.mpr
  exact (le_div_iff₀ hH).mpr (by linarith)

lemma tent_rising (a H x : ℝ) (hH : 0 < H) (hx : x ∈ Set.Icc a (a+H)) :
    tent a H x = (x-a)/H := by
  unfold tent
  rw [abs_of_nonpos (by linarith [hx.2])]
  have he : 1 - -(x-(a+H))/H = (x-a)/H := by field_simp; ring
  rw [he, max_eq_right (div_nonneg (by linarith [hx.1]) hH.le)]

lemma tent_falling (a H x : ℝ) (hH : 0 < H) (hx : x ∈ Set.Icc (a+H) (a+2*H)) :
    tent a H x = (a+2*H-x)/H := by
  unfold tent
  rw [abs_of_nonneg (by linarith [hx.1])]
  have he : 1 - (x-(a+H))/H = (a+2*H-x)/H := by field_simp; ring
  rw [he, max_eq_right (div_nonneg (by linarith [hx.2]) hH.le)]

lemma tent_lipschitz (a H x y : ℝ) (hH : 0 < H) :
    |tent a H x - tent a H y| ≤ |x-y|/H := by
  have hm := abs_max_sub_max_le_abs (1-|x-(a+H)|/H) (1-|y-(a+H)|/H) 0
  rw [max_comm _ 0, max_comm _ 0] at hm
  change |tent a H x - tent a H y| ≤ _ at hm
  have he : |(1-|x-(a+H)|/H) - (1-|y-(a+H)|/H)| =
      abs (|x-(a+H)|-|y-(a+H)|)/H := by
    rw [show (1-|x-(a+H)|/H) - (1-|y-(a+H)|/H) =
      -((|x-(a+H)|-|y-(a+H)|)/H) by ring, abs_neg, abs_div, abs_of_pos hH]
  rw [he] at hm
  exact hm.trans (div_le_div_of_nonneg_right
    (by simpa using (abs_abs_sub_abs_le_abs_sub (x-(a+H)) (y-(a+H)))) hH.le)

lemma logPhase_lipschitz {a : ℝ} (ha : 0 < a) (t x y : ℝ) (hx : a ≤ x) (hy : a ≤ y) :
    ‖logPhase t x - logPhase t y‖ ≤ (|t|/a)*|x-y| := by
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := logPhase t) (f' := fun u => logPhase t u * (Complex.I * (t/u : ℝ)))
    (s := Set.Ici a)
    (fun u hu => (hasDerivAt_logPhase t (ne_of_gt (lt_of_lt_of_le ha hu))).hasDerivWithinAt)
    (fun u hu => show ‖logPhase t u * (Complex.I * (t/u : ℝ))‖ ≤ |t|/a from by
      rw [norm_mul, norm_logPhase, one_mul, norm_mul, Complex.norm_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (show 0 < u from lt_of_lt_of_le ha hu)]
      exact div_le_div_of_nonneg_left (abs_nonneg t) ha hu)
    (convex_Ici a) hy hx
  simpa only [Real.norm_eq_abs] using hmv

noncomputable def tentPhase (t a H x : ℝ) : ℂ :=
  (tent a H x : ℂ) * logPhase t (max a x)

lemma tentPhase_norm (t a H x : ℝ) : ‖tentPhase t a H x‖ = tent a H x := by
  simp only [tentPhase, norm_mul, norm_logPhase, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (tent_nonneg a H x)]

lemma tentPhase_zero_left (t a H x : ℝ) (hH : 0 < H) (hx : x ≤ a) :
    tentPhase t a H x = 0 := by simp only [tentPhase, tent_zero_left a H x hH hx, Complex.ofReal_zero, zero_mul]

lemma tentPhase_zero_right (t a H x : ℝ) (hH : 0 < H) (hx : a+2*H ≤ x) :
    tentPhase t a H x = 0 := by simp only [tentPhase, tent_zero_right a H x hH hx, Complex.ofReal_zero, zero_mul]

lemma tentPhase_lipschitz (t a H x y : ℝ) (ha : 0 < a) (hH : 0 < H) :
    ‖tentPhase t a H x - tentPhase t a H y‖ ≤ (H⁻¹+|t|/a)*|x-y| := by
  have he : tentPhase t a H x - tentPhase t a H y =
      ((tent a H x : ℂ)-(tent a H y : ℂ))*logPhase t (max a x) +
      (tent a H y : ℂ)*(logPhase t (max a x)-logPhase t (max a y)) := by
    unfold tentPhase
    ring
  rw [he]
  have hp : ‖logPhase t (max a x)-logPhase t (max a y)‖ ≤ |t|/a*|x-y| := by
    apply (logPhase_lipschitz ha t _ _ (le_max_left _ _) (le_max_left _ _)).trans
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (abs_nonneg t) ha.le)
    simpa only [max_comm a] using abs_max_sub_max_le_abs x y a
  calc
    _ ≤ ‖((tent a H x : ℂ)-(tent a H y : ℂ))*logPhase t (max a x)‖ +
       ‖(tent a H y : ℂ)*(logPhase t (max a x)-logPhase t (max a y))‖ := norm_add_le _ _
    _ = |tent a H x-tent a H y| + tent a H y * ‖logPhase t (max a x)-logPhase t (max a y)‖ := by
      simp only [norm_mul, norm_logPhase, mul_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (tent_nonneg a H y)]
    _ ≤ |x-y|/H + |t|/a*|x-y| := by
      apply add_le_add (tent_lipschitz a H x y hH)
      exact (mul_le_mul_of_nonneg_left hp (tent_nonneg a H y)).trans
        (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right (tent_le_one a H y hH)
          (mul_nonneg (div_nonneg (abs_nonneg t) ha.le) (abs_nonneg (x-y)))))
    _ = _ := by ring

lemma tentPhase_continuous (t a H : ℝ) (ha : 0 < a) (hH : 0 < H) :
    Continuous (tentPhase t a H) := by
  have hL : 0 ≤ H⁻¹+|t|/a := by positivity
  have hl : LipschitzWith ⟨H⁻¹+|t|/a, hL⟩ (tentPhase t a H) :=
    LipschitzWith.of_dist_le_mul (fun x y => by
      rw [dist_eq_norm, Real.dist_eq]
      exact tentPhase_lipschitz t a H x y ha hH)
  exact hl.continuous

end OrdinaryLogIntegral

end

end OAI

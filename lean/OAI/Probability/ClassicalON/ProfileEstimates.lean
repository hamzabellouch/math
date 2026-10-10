import OAI.Probability.ClassicalON.SmoothBounds

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff BigOperators
namespace ClassicalON

def squareStep (m : Bool) (ε : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  if m then (z.1,z.2+ε) else (z.1+ε,z.2)

@[simp] theorem squareStep_distance (m : Bool) (ε : ℝ) (z : ℝ × ℝ) :
    ‖squareStep m ε z-z‖ = |ε| := by
  cases m <;> simp [squareStep, Prod.norm_def, Real.norm_eq_abs, abs_nonneg]

theorem profiles_uniform_bound : ∃ C : ℝ, 1 ≤ C ∧
    (∀ m s z, |squareProfile m s z| ≤ C) ∧
    (∀ m s z w, |squareProfile m s w-squareProfile m s z| ≤ C*‖w-z‖) := by
  have he (m s : Bool) := smooth_compact_lipschitz_bound
    (squareProfile_compact m s) (squareProfile_contDiff m s)
  choose C hC hval hLip using he
  let M : ℝ := 1+∑ m, ∑ s, C m s
  have hsum : 0 ≤ ∑ m : Bool, ∑ s : Bool, C m s :=
    Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun s _ => hC m s
  have hCM (m s : Bool) : C m s ≤ M := by
    have hs := Finset.single_le_sum (fun t _ => hC m t) (Finset.mem_univ s)
    have hm : (∑ t : Bool, C m t) ≤ ∑ u : Bool, ∑ t : Bool, C u t := Finset.single_le_sum (fun t _ => Finset.sum_nonneg fun t' _ => hC t t') (Finset.mem_univ m)
    dsimp only [M]
    linarith
  refine ⟨M, by dsimp only [M]; linarith, fun m s z => (hval m s z).trans (hCM m s), ?_⟩
  intro m s z w
  exact (hLip m s z w).trans (mul_le_mul_of_nonneg_right (hCM m s) (norm_nonneg _))

theorem theta_trapezoid_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ,
    |thetaBump y-thetaBump x-(y-x)/2*(deriv thetaBump x+deriv thetaBump y)| ≤
      C*|y-x|^3 := by
  have hd : ContDiff ℝ ∞ (deriv thetaBump) :=
    (contDiff_infty_iff_deriv.mp (thetaBump.contDiff : ContDiff ℝ ∞ thetaBump)).2
  have hdd : ContDiff ℝ ∞ (deriv (deriv thetaBump)) := (contDiff_infty_iff_deriv.mp hd).2
  obtain ⟨C,hC,_hval,hL⟩ := smooth_compact_lipschitz_bound
    (thetaBump.hasCompactSupport.deriv.deriv) hdd
  refine ⟨2*C, by positivity, fun x y => ?_⟩
  exact trapezoid_error_bound thetaBump (deriv thetaBump) (deriv (deriv thetaBump)) C hC
    (fun t => ((thetaBump.contDiff : ContDiff ℝ ∞ thetaBump).differentiable (by simp) t).hasDerivAt)
    (fun t => (hd.differentiable (by simp) t).hasDerivAt) hL x y

theorem squareCutoff_near_gradient (m : Bool) (z w : ℝ × ℝ)
    (h1 : |w.1-z.1| ≤ 1/16) (h2 : |w.2-z.2| ≤ 1/16)
    (hg : squareGradient m z ≠ 0) : squareCutoff w = 1 := by
  have ha1 : |w.1| ≤ |w.1-z.1|+|z.1| := by simpa only [sub_add_cancel] using (abs_add_le (w.1-z.1) z.1)
  have ha2 : |w.2| ≤ |w.2-z.2|+|z.2| := by simpa only [sub_add_cancel] using (abs_add_le (w.2-z.2) z.2)
  have hb1 : |z.1| ≤ |w.1-z.1|+|w.1| := by
    simpa only [sub_add_cancel, abs_sub_comm] using (abs_add_le (z.1-w.1) w.1)
  have hb2 : |z.2| ≤ |w.2-z.2|+|w.2| := by
    simpa only [sub_add_cancel, abs_sub_comm] using (abs_add_le (z.2-w.2) w.2)
  cases m
  · have hd : deriv thetaBump z.1 ≠ 0 := by intro h; apply hg; simp [squareGradient, h]
    have ht : thetaBump z.2 ≠ 0 := by intro h; apply hg; simp [squareGradient, h]
    have hx : 4/3 < |z.1| ∧ |z.1| < 5/3 := ⟨
      lt_of_not_ge (fun h => hd (thetaBump_deriv_zero_inner h)),
      lt_of_not_ge (fun h => hd (thetaBump_deriv_zero_outer h))⟩
    have hy : |z.2| < 5/3 := lt_of_not_ge (fun h => ht (thetaBump_zero h))
    simp [squareCutoff, outerBump_one (by linarith : |w.1| ≤ 7/4),
      outerBump_one (by linarith : |w.2| ≤ 7/4), innerBump_zero (by linarith : 5/4 ≤ |w.1|)]
  · have hd : deriv thetaBump z.2 ≠ 0 := by intro h; apply hg; simp [squareGradient, h]
    have ht : thetaBump z.1 ≠ 0 := by intro h; apply hg; simp [squareGradient, h]
    have hy : 4/3 < |z.2| ∧ |z.2| < 5/3 := ⟨
      lt_of_not_ge (fun h => hd (thetaBump_deriv_zero_inner h)),
      lt_of_not_ge (fun h => hd (thetaBump_deriv_zero_outer h))⟩
    have hx : |z.1| < 5/3 := lt_of_not_ge (fun h => ht (thetaBump_zero h))
    simp [squareCutoff, outerBump_one (by linarith : |w.1| ≤ 7/4),
      outerBump_one (by linarith : |w.2| ≤ 7/4), innerBump_zero (by linarith : 5/4 ≤ |w.2|)]

theorem squareProfile_product_difference (m : Bool) (z w : ℝ × ℝ)
    (h1 : |w.1-z.1| ≤ 1/16) (h2 : |w.2-z.2| ≤ 1/16) :
    squareProfile m false z*squareProfile m false w-
      squareProfile m true z*squareProfile m true w =
      (squareGradient m z+squareGradient m w)/2 := by
  have hzw : squareGradient m z*squareCutoff w = squareGradient m z := by
    by_cases hg : squareGradient m z=0
    · simp [hg]
    · rw [squareCutoff_near_gradient m z w h1 h2 hg, mul_one]
  have hwz : squareCutoff z*squareGradient m w = squareGradient m w := by
    by_cases hg : squareGradient m w=0
    · simp [hg]
    · rw [squareCutoff_near_gradient m w z (by simpa only [abs_sub_comm] using h1)
        (by simpa only [abs_sub_comm] using h2) hg, one_mul]
  simp only [squareProfile, Bool.false_eq_true, ↓reduceIte]
  nlinarith

theorem squareTheta_step_error : ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : Bool) (z : ℝ × ℝ) (ε : ℝ),
    |ε| ≤ 1/16 →
    |squareTheta (squareStep m ε z)-squareTheta z-
      ε*(squareProfile m false z*squareProfile m false (squareStep m ε z)-
           squareProfile m true z*squareProfile m true (squareStep m ε z))| ≤ C*|ε|^3 := by
  obtain ⟨C,hC,hT⟩ := theta_trapezoid_bound
  refine ⟨C,hC,?_⟩
  intro m z ε hε
  have hp := squareProfile_product_difference m z (squareStep m ε z)
    (by cases m
        · simpa only [squareStep, Bool.false_eq_true, ↓reduceIte, add_sub_cancel_left] using hε
        · simp [squareStep])
    (by cases m
        · simp [squareStep]
        · simpa only [squareStep, ↓reduceIte, add_sub_cancel_left] using hε)
  rw [hp]
  have hb (x : ℝ) : |thetaBump x| ≤ 1 := by rw [abs_of_nonneg thetaBump.nonneg]; exact thetaBump.le_one
  cases m
  · have h := hT z.1 (z.1+ε)
    simp only [add_sub_cancel_left] at h
    have he : squareTheta (squareStep false ε z)-squareTheta z-
        ε*((squareGradient false z+squareGradient false (squareStep false ε z))/2) =
        thetaBump z.2*(thetaBump (z.1+ε)-thetaBump z.1-ε/2*(deriv thetaBump z.1+deriv thetaBump (z.1+ε))) := by
      simp only [squareTheta, squareStep, squareGradient, Bool.false_eq_true, ↓reduceIte]
      ring
    rw [he, abs_mul]
    calc _ ≤ 1*(C*|ε|^3) := mul_le_mul (hb z.2) h (abs_nonneg _) (by norm_num)
         _ = _ := one_mul _
  · have h := hT z.2 (z.2+ε)
    simp only [add_sub_cancel_left] at h
    have he : squareTheta (squareStep true ε z)-squareTheta z-
        ε*((squareGradient true z+squareGradient true (squareStep true ε z))/2) =
        thetaBump z.1*(thetaBump (z.2+ε)-thetaBump z.2-ε/2*(deriv thetaBump z.2+deriv thetaBump (z.2+ε))) := by
      simp only [squareTheta, squareStep, squareGradient, ↓reduceIte]
      ring
    rw [he, abs_mul]
    calc _ ≤ 1*(C*|ε|^3) := mul_le_mul (hb z.1) h (abs_nonneg _) (by norm_num)
         _ = _ := one_mul _

end ClassicalON

end

end OAI

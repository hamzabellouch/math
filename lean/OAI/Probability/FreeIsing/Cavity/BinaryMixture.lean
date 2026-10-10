import OAI.Probability.FreeIsing.Cavity.Homeomorph
import OAI.Probability.FreeIsing.Estimates.InhomogeneousSpinChain

namespace OAI

noncomputable section

namespace Problem367.PosteriorChain

private theorem tanh_add_ratio (x y : ℝ) :
    Real.tanh (x + y) =
      (Real.tanh x + Real.tanh y) / (1 + Real.tanh x * Real.tanh y) := by
  have hm := cavityMessage_argument_mem (Real.tanh_sq_lt_one x).le y
  have hd : 1 + Real.tanh x * Real.tanh y ≠ 0 := by linarith [hm.1]
  apply (eq_div_iff hd).2
  simp only [Real.tanh_eq_sinh_div_cosh]
  field_simp
  rw [Real.sinh_add, Real.cosh_add]
  ring

private theorem tanh_sub_ratio (x y : ℝ) :
    Real.tanh (x - y) =
      (Real.tanh x - Real.tanh y) / (1 - Real.tanh x * Real.tanh y) := by
  simpa only [sub_eq_add_neg, Real.tanh_neg, mul_neg] using tanh_add_ratio x (-y)

theorem affine_mean_eq_cavity_mean (beta z H : ℝ) :
    intercept beta z + slope beta z * Real.tanh H =
      Real.tanh (z + cavityMessage (Real.tanh beta)
        (H - cavityMessage (Real.tanh beta) z)) := by
  have htheta : Real.tanh beta ^ 2 ≤ 1 := (Real.tanh_sq_lt_one beta).le
  have hinner : Real.tanh (cavityMessage (Real.tanh beta) z) =
      Real.tanh beta * Real.tanh z :=
    Real.tanh_artanh (cavityMessage_argument_mem htheta z)
  have houter : Real.tanh (cavityMessage (Real.tanh beta)
      (H - cavityMessage (Real.tanh beta) z)) =
      Real.tanh beta * Real.tanh (H - cavityMessage (Real.tanh beta) z) :=
    Real.tanh_artanh (cavityMessage_argument_mem htheta _)
  rw [tanh_add_ratio, houter, tanh_sub_ratio H, hinner]
  unfold intercept slope
  rw [tanh_add_ratio, tanh_sub_ratio]
  have hz := cavityMessage_argument_mem (Real.tanh_sq_lt_one z).le beta
  have hh := cavityMessage_argument_mem (Real.tanh_sq_lt_one H).le
    (cavityMessage (Real.tanh beta) z)
  rw [hinner] at hh
  have hdplus : 1 + Real.tanh z * Real.tanh beta ≠ 0 := by linarith [hz.1]
  have hdminus : 1 - Real.tanh z * Real.tanh beta ≠ 0 := by linarith [hz.2]
  have hdinner : 1 - Real.tanh H * (Real.tanh beta * Real.tanh z) ≠ 0 := by
    linarith [hh.2]
  have hout := cavityMessage_argument_mem (Real.tanh_sq_lt_one z).le
    (cavityMessage (Real.tanh beta) (H - cavityMessage (Real.tanh beta) z))
  rw [houter, tanh_sub_ratio H, hinner] at hout
  have hdouter : 1 + Real.tanh z * (Real.tanh beta *
      ((Real.tanh H - Real.tanh beta * Real.tanh z) /
        (1 - Real.tanh H * (Real.tanh beta * Real.tanh z)))) ≠ 0 := by
    linarith [hout.1]
  apply (eq_div_iff hdouter).2
  have hdinner' : 1 - Real.tanh z * Real.tanh beta * Real.tanh H ≠ 0 := by
    convert hdinner using 1
    ring
  field_simp [hdplus, hdminus, hdinner, hdinner']
  ring

theorem cavityFromSites_affine_mean {beta : ℝ} (hbeta : 0 ≤ beta) (z H : ℝ) :
    cavityFromSites (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
      (H, Real.artanh (intercept beta z + slope beta z * Real.tanh H)) =
        (H - cavityMessage (Real.tanh beta) z, z) := by
  apply cavityFromSites_eq
  constructor
  · ring
  · simp only [affine_mean_eq_cavity_mean, Real.artanh_tanh]

theorem cavityFromSites_affine_mean_snd {beta : ℝ} (hbeta : 0 ≤ beta) (z H : ℝ) :
    (cavityFromSites (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
      (H, Real.artanh (intercept beta z + slope beta z * Real.tanh H))).2 = z := by
  rw [cavityFromSites_affine_mean hbeta]

end Problem367.PosteriorChain

end

end OAI

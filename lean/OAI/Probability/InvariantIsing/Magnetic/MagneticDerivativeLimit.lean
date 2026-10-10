import OAI.Probability.InvariantIsing.Magnetic.MagneticParabolicNegative

namespace OAI

/-! Bounded second derivatives turn convergence of the scalar continuation
into vanishing first derivatives. Applied twice, this gives the endpoint
regularity of the weighted inverse-coordinate continuation curvature. -/

noncomputable section
open Filter Set
open scoped Topology

namespace InvariantIsing

lemma magnetic_derivative_increment_bound {F G D : ℝ → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hF : ∀ x, HasDerivAt F (G x) x)
    (hG : ∀ x, HasDerivAt G (D x) x) (hD : ∀ x, |D x| ≤ L)
    (x : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    |F (x + h) - F x - h * G x| ≤ L * h ^ 2 := by
  have hLip (y : ℝ) : |G y - G x| ≤ L * |y - x| := by
    have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z (_ : z ∈ (univ : Set ℝ)) => (hG z).hasDerivWithinAt)
      (fun z _ => by simpa only [Real.norm_eq_abs] using hD z)
      convex_univ (mem_univ x) (mem_univ y)
    simpa only [Real.norm_eq_abs] using he
  let R := fun z => F z - (z - x) * G x
  have hR (z : ℝ) : HasDerivAt R (G z - G x) z := by
    convert (hF z).sub (((hasDerivAt_id z).sub_const x).mul_const (G x)) using 1 <;>
      first | rfl | simp
  have hB (z : ℝ) (hz : z ∈ Icc x (x + h)) : |G z - G x| ≤ L * h := by
    have hb : |z - x| ≤ h := by rw [abs_of_nonneg (sub_nonneg.mpr hz.1)]; linarith [hz.2]
    exact (hLip z).trans (mul_le_mul_of_nonneg_left hb hL)
  have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ Icc x (x + h)) => (hR z).hasDerivWithinAt)
    (fun z hz => by simpa only [Real.norm_eq_abs] using hB z hz)
    (convex_Icc x (x + h)) (left_mem_Icc.mpr (by linarith : x ≤ x + h))
    (right_mem_Icc.mpr (by linarith : x ≤ x + h))
  have hdist : |x + h - x| = h := by rw [add_sub_cancel_left, abs_of_nonneg hh]
  have hRe : R (x + h) - R x = F (x + h) - F x - h * G x := by dsimp only [R]; ring
  simp only [Real.norm_eq_abs, hdist] at he
  rw [hRe] at he
  simpa only [pow_two, mul_assoc] using he

lemma magnetic_derivative_tendsto_zero {F G D : ℝ → ℝ} {c L : ℝ}
    (hL : 0 ≤ L) (hF : ∀ x, HasDerivAt F (G x) x)
    (hG : ∀ x, HasDerivAt G (D x) x) (hD : ∀ x, |D x| ≤ L)
    (hlimit : Tendsto F atTop (𝓝 c)) : Tendsto G atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let h := ε / (2 * (L + 1))
  have hden : 0 < 2 * (L + 1) := by positivity
  have hh : 0 < h := div_pos hε hden
  have hheq : 2 * (L + 1) * h = ε := by
    dsimp only [h]
    field_simp [hden.ne']
  have hLh : L * h ^ 2 < ε * h / 2 := by
    have hh2 : 0 < h ^ 2 := sq_pos_of_pos hh
    nlinarith
  have hinc : Tendsto (fun x => F (x + h) - F x) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, sub_self] using
      (hlimit.comp (tendsto_atTop_add_const_right atTop h tendsto_id)).sub hlimit
  have hevent := (Metric.tendsto_nhds.mp hinc) (ε * h / 2) (by positivity)
  filter_upwards [hevent] with x hx
  rw [Real.dist_eq, sub_zero] at hx ⊢
  have hr := magnetic_derivative_increment_bound hL hF hG hD x hh.le
  have hg : |h * G x| ≤ |F (x + h) - F x| + L * h ^ 2 := by
    calc
      _ = |(F (x + h) - F x) - (F (x + h) - F x - h * G x)| := by congr 1; ring
      _ ≤ |F (x + h) - F x| + |F (x + h) - F x - h * G x| := abs_sub _ _
      _ ≤ _ := add_le_add_right hr _
  rw [abs_mul, abs_of_pos hh] at hg
  nlinarith

end InvariantIsing

end

end OAI

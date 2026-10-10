import OAI.Analysis.FourierLLogL.Fourier.Kappa
/-! # Translation averaging -/

open MeasureTheory Filter Set Function
open scoped ENNReal BigOperators Topology Real

namespace OAI

namespace FourierLLogL.Period
noncomputable section

def window : Set ℝ := Ico (-1) 1
def origins : Set ℝ := Ico (-2) 2

private lemma flip_dilate (g : ℝ → ℂ) (d c : ℝ) (hc : 0 < c) :
    (∫ x : ℝ, g (d-c*x)) = c⁻¹ • ∫ x : ℝ, g x := by
  have h := Measure.integral_comp_mul_left (fun x => g (d+x)) (-c)
  simp_rw [neg_mul, ← sub_eq_add_neg] at h
  rw [integral_add_left_eq_self] at h
  simpa [abs_of_pos (inv_pos.mpr hc)] using h

/-- Translation average over origins for a single length. -/
lemma jump_average_all (F : ℝ → ℂ) (hf : Measurable F) (B : ℝ) (hb : ∀ x, ‖F x‖ ≤ B)
    (x r b : ℝ) (hr : 0 < r) (hr' : r ≤ 1) :
    (∫ a : ℝ, jump F (a+b) r x) =
      ∫ t in window, kappa (t/r) • F (x-t) := by
  let J (a : ℝ) := jump F (a+b) r x
  let f (v : ℝ) := haarG v • ∫ w, haarH w • F (x-r*(v-w)) ∂μ₁
  have heq (v : ℝ) : J (x-b-r*v) = f v := by
    have H : (x - (x-b-r*v+b))/r = v := by field_simp; ring
    unfold J f jump coeffH
    rw [H]
    simp_rw [show ∀ w, x-b-r*v+b+r*w = x-r*(v-w) by intro w; ring]
  have hA : (∫ a : ℝ, J a) = r • ∫ v, f v ∂μ₁ := by
    have HH := flip_dilate J (x-b) r hr
    simp_rw [heq] at HH
    have Hsupport : (∫ v, f v ∂μ₁) = ∫ v : ℝ, f v := by
      exact setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun v hv => by unfold f; rw [G_outside hv, zero_smul])
    rw [Hsupport, HH, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  let W (v t : ℝ) := haarG v • (haarH (v-t) • F (x-r*t))
  have hw (v : ℝ) (hv : v ∈ unitInt) :
      f v = ∫ t in window, W v t := by
    have HH := flip_dilate (fun w => haarH w • F (x-r*(v-w))) v 1 (by norm_num)
    simp only [one_mul, sub_sub_cancel, inv_one, one_smul] at HH
    have Hs : (∫ w, haarH w • F (x-r*(v-w)) ∂μ₁) =
        ∫ w, haarH w • F (x-r*(v-w)) := by
      exact setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun w hw => by rw [H_outside hw, zero_smul])
    have Hs' : (∫ t in window, haarH (v-t) • F (x-r*t)) =
        ∫ t, haarH (v-t) • F (x-r*t) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      rw [H_outside, zero_smul]
      rintro ⟨h1,h2⟩
      exact ht ⟨by linarith [hv.1], by linarith [hv.2]⟩
    change haarG v • _ = ∫ t in window, haarG v • (haarH (v-t) • F (x-r*t))
    rw [integral_smul, Hs, Hs', HH]
  have hWm : Measurable (uncurry W) :=
    (measurableG.comp measurable_fst).smul
      ((measurableH.comp (measurable_fst.sub measurable_snd)).smul
        (hf.comp (measurable_const.sub (measurable_const.mul measurable_snd))))
  have : IsFiniteMeasure (volume.restrict window) :=
    show IsFiniteMeasure (volume.restrict (Ico (-1:ℝ) 1)) from inferInstance
  have hWi : Integrable (uncurry W) (μ₁.prod (volume.restrict window)) := by
    apply Integrable.of_bound hWm.aestronglyMeasurable B
    refine ae_of_all _ fun ⟨v,t⟩ => ?_
    simp only [W, uncurry_apply_pair, norm_smul, Real.norm_eq_abs]
    refine (mul_le_of_le_one_left (mul_nonneg (abs_nonneg _) (norm_nonneg _))
      (G_bound _)).trans ?_
    exact (mul_le_of_le_one_left (norm_nonneg _) (H_bound _)).trans (hb _)
  have hK (t : ℝ) : (∫ v, W v t ∂μ₁) = kappa t • F (x-r*t) := by
    dsimp only [W]; simp_rw [smul_smul]
    rw [integral_smul_const, kappa_eq_mean]
  have hB : (∫ v, f v ∂μ₁) = ∫ t in window, kappa t • F (x-r*t) := by
    rw [show (∫ v, f v ∂μ₁) = ∫ v, (∫ t in window, W v t) ∂μ₁ from
      setIntegral_congr_fun measurable_unitInt hw, integral_integral_swap hWi]
    simp_rw [hK]
  let q (t : ℝ) := kappa (t/r) • F (x-t)
  have Q : ∀ t, q (r*t) = kappa t • F (x-r*t) := fun t => by
    unfold q; rw [mul_div_cancel_left₀ t hr.ne']
  have hg : ∀ t ∉ window, 1 ≤ |t| := by
    unfold window; grind
  have hq : (∫ t in window, q t) = ∫ t, q t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    unfold q
    rw [kappa_outside, zero_smul]
    rw [abs_div, abs_of_pos hr]
    exact (le_div_iff₀ hr).mpr (by linarith [hg t ht])
  have hq' : (∫ t in window, q (r*t)) = ∫ t, q (r*t) := by
    exact setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun t ht => by rw [Q, kappa_outside t (hg t ht), zero_smul])
  have htrans : (∫ t in window, kappa t • F (x-r*t)) = r⁻¹ • ∫ t in window, q t := by
    simp_rw [← Q]
    rw [hq, hq', Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr hr)]
  change (∫ a : ℝ, J a) = ∫ t in window, q t
  rw [hA, hB, htrans, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]

lemma jump_average (F : ℝ → ℂ) (hf : Measurable F) (B : ℝ) (hb : ∀ x, ‖F x‖ ≤ B)
    {x s : ℝ} (n k : ℕ) (hk : k < 2^n) (hx : x ∈ unitInt) (hs : 0 < s) (hs' : s ≤ 1) :
    (∫ a in origins, jump F (lft a s n k) (s*side n) x) =
      ∫ t in window, kappa (t/(s*side n)) • F (x-t) := by
  have hr : 0 < s*side n := mul_pos hs (side_pos _)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact jump_average_all F hf B hb x _ _ hr
      ((mul_le_mul_of_nonneg_right hs' (side_pos n).le).trans
        (by simpa using side_le n))
  · intro a ha
    apply jump_outside hr
    intro ht
    obtain ⟨h1,h2⟩ := cell_in_top a hs hk ht
    exact ha ⟨by linarith [hx.1], by linarith [hx.2]⟩

lemma haarLayer_average (F : ℝ → ℂ) (hf : Measurable F) (B : ℝ) (hb : ∀ x, ‖F x‖ ≤ B)
    {x s : ℝ} (n : ℕ) (hx : x ∈ unitInt) (hs : 0 < s) (hs' : s ≤ 1) :
    (∫ a in origins, haarLayer F a s n x) =
      (2:ℝ)^n • ∫ t in window, kappa (t/(s*side n)) • F (x-t) := by
  unfold haarLayer
  rw [integral_finsetSum]
  · calc
      _ = ∑ _ ∈ Finset.range (2^n), ∫ t in window, kappa (t/(s*side n)) • F (x-t) :=
        Finset.sum_congr rfl fun k hk => jump_average F hf B hb n k (Finset.mem_range.mp hk) hx hs hs'
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ]
                  norm_cast
  · intro k hk
    refine seg_integrable _ (measurable_jump_comp hf ?_ measurable_const measurable_const) B _ _
      (fun a _ => bounded_jump hf B hb _ _ _)
    exact measurable_id.add_const _

end
end FourierLLogL.Period

end OAI

import OAI.Probability.SLE.Gauge.RibbonPassageScaling
import OAI.Probability.SLE.Loewner.ScaleTraceLaw

namespace OAI

/-! Exact whole-sausage scaling at the one common physical mesh. The
capacity time change does not change the trace's range. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open RibbonPassageScaling ScaleTraceLaw

lemma wholeSausageSet_surjective_clock (γ : ℝ≥0 → ℂ) (e : ℝ≥0 → ℝ≥0)
    (he : Function.Surjective e) (v : ℝ) :
    wholeSausageSet (γ ∘ e) v = wholeSausageSet γ v := by
  ext z
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨e t, ht⟩
  · rintro ⟨t, ht⟩
    obtain ⟨u, rfl⟩ := he t
    exact ⟨u, ht⟩

lemma wholeSausageSet_affine (a : ℂ) {ell : ℝ} (hell : 0 < ell)
    (γ : ℝ≥0 → ℂ) (v : ℝ) :
    wholeSausageSet (fun t => affine a ell (γ t)) (ell * v) =
      affine a ell '' wholeSausageSet γ v := by
  ext z
  obtain ⟨w, rfl⟩ := (affine_bijective a hell).2 z
  constructor
  · rintro ⟨t, ht⟩
    rw [affine_dist a hell.le] at ht
    exact ⟨w, ⟨t, (mul_lt_mul_iff_right₀ hell).mp ht⟩, rfl⟩
  · rintro ⟨w', ⟨t, ht⟩, he⟩
    have hw : w' = w := (affine_bijective a hell).1 he
    subst w'
    exact ⟨t, by rw [affine_dist a hell.le]; exact mul_lt_mul_of_pos_left ht hell⟩

theorem wholeSausageCharge_affine (κ : ℝ) (a : ℂ) {ell : ℝ} (hell : 0 < ell)
    (γ : ℝ≥0 → ℂ) {v : ℝ} (hv : 0 < v) (R : Set ℂ) :
    wholeSausageCharge κ (fun t => affine a ell (γ t)) (ell * v) (affine a ell '' R) =
      ENNReal.ofReal (ell ^ dimension κ) * wholeSausageCharge κ γ v R := by
  have he : (ell * v) ^ (-codimension κ) * ell ^ 2 =
      ell ^ dimension κ * v ^ (-codimension κ) := by
    rw [Real.mul_rpow hell.le hv.le]
    calc
      _ = (ell ^ (-codimension κ) * ell ^ (2 : ℝ)) * v ^ (-codimension κ) := by
        rw [Real.rpow_two]
        ring
      _ = ell ^ (-codimension κ + 2) * v ^ (-codimension κ) := by rw [Real.rpow_add hell]
      _ = _ := by congr 2; unfold codimension; ring
  simp only [wholeSausageCharge, wholeSausageSet_affine a hell]
  rw [← image_inter (affine_bijective a hell).1, affine_volume a hell.le]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg (mul_pos hell hv).le _), he,
    ENNReal.ofReal_mul (Real.rpow_nonneg hell.le _), mul_assoc]

theorem wholeSausageCharge_scalePath (κ : ℝ) (c : ℝ≥0) (hc : 0 < c)
    (p : C(ℝ≥0, ℂ)) {v : ℝ} (hv : 0 < v) (R : Set ℂ) :
    wholeSausageCharge κ (scalePath c p) ((c : ℝ) * v) (affine 0 c '' R) =
      ENNReal.ofReal ((c : ℝ) ^ dimension κ) * wholeSausageCharge κ p v R := by
  have he : Function.Surjective (fun t : ℝ≥0 => t / c ^ 2) := by
    intro t
    exact ⟨t * c ^ 2, mul_div_cancel_right₀ t (pow_ne_zero 2 hc.ne')⟩
  have hp : (scalePath c p : ℝ≥0 → ℂ) =
      (fun t => affine 0 c (p t)) ∘ (fun t => t / c ^ 2) := by
    funext t
    change (c : ℂ) * p (t / c ^ 2) = 0 + (c : ℂ) * p (t / c ^ 2)
    exact (zero_add _).symm
  simp only [wholeSausageCharge, hp, wholeSausageSet_surjective_clock _ _ he]
  exact wholeSausageCharge_affine κ 0 (show 0 < (c : ℝ) from hc) p hv R

end SLEExactGauge

end

end OAI

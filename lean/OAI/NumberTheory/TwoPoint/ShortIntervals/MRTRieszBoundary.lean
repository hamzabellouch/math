import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTZetaRectangle

namespace OAI

/-! Boundary bounds for the actual shifted zeta integrand. The pole is
kept separate, so bounded heights are included in the same rectangle. -/

namespace TwoPointCorrelations

open Complex Filter Set
open scoped Topology

lemma mrt_zeta_logderiv_of_correction {s : ℂ} {B D : ℝ}
    (hc : ‖mrtZetaPoleCorrection s‖ ≤ B) (hi : ‖(s - 1)⁻¹‖ ≤ D) :
    ‖-deriv riemannZeta s / riemannZeta s‖ ≤ B + D := by
  have hh := norm_add_le (mrtZetaPoleCorrection s) ((s - 1)⁻¹)
  have he : mrtZetaPoleCorrection s + (s - 1)⁻¹ =
      -deriv riemannZeta s / riemannZeta s := by
    unfold mrtZetaPoleCorrection
    ring
  rw [he] at hh
  exact hh.trans (add_le_add hc hi)

theorem MRTWeakHurwitzGrowthInput.riesz_boundary (h : MRTWeakHurwitzGrowthInput) :
    ∃ K L₀ : ℝ, 0 < K ∧ ∀ L : ℝ, L₀ ≤ L → 1 ≤ L →
      L ^ (-(3 / 4 : ℝ)) ≤ 1 / 2 → ∀ b T u : ℝ,
      1 < b → b ≤ 2 → 2 ≤ T → T ≤ 2 * Real.exp (2 * L) → |u| ≤ T / 2 →
      (∀ s ∈ Rectangle
        (((1 - L ^ (-(3 / 4 : ℝ)) : ℝ) : ℂ) - Complex.I * (T : ℂ))
        ((b : ℂ) + Complex.I * (T : ℂ)),
        s + (u : ℂ) * Complex.I ≠ 1 → riemannZeta (s + (u : ℂ) * Complex.I) ≠ 0) ∧
      (∀ t ∈ Icc (-T) T,
        ‖-deriv riemannZeta
            (((1 - L ^ (-(3 / 4 : ℝ)) : ℝ) : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I) /
          riemannZeta
            (((1 - L ^ (-(3 / 4 : ℝ)) : ℝ) : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I)‖ ≤
          K * L ^ 2) ∧
      (∀ σ ∈ Icc (1 - L ^ (-(3 / 4 : ℝ))) b, ∀ t : ℝ, |t| = T →
        ‖-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I) /
          riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I)‖ ≤ K * L ^ 2) := by
  obtain ⟨C, L₀, hC, hr⟩ := h.zeta_sparse_rectangle
  refine ⟨C + 1, L₀, by positivity, ?_⟩
  intro L hL₀ hL hδ b T u hb hb2 hT hTup hu
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hδ0 : 0 < L ^ (-(3 / 4 : ℝ)) := Real.rpow_pos_of_pos hL0 _
  have hLsq : 1 ≤ L ^ 2 := by nlinarith
  have hheight {t : ℝ} (ht : |t| ≤ T) :
      |t + u| ≤ 4 * Real.exp (2 * L) := by
    have hh := abs_add_le t u
    linarith [Real.exp_pos (2 * L)]
  have happ {σ t : ℝ} (hσ : 1 - L ^ (-(3 / 4 : ℝ)) ≤ σ)
      (hσ2 : σ ≤ 2) (ht : |t| ≤ T)
      (hne : (σ : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I ≠ 1) :=
    hr L hL₀ ((σ : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I)
      (by simpa using hσ) (by simpa using hσ2) (by simpa using hheight ht) hne
  refine ⟨?_, ?_, ?_⟩
  · intro s hs hs1
    have hab : 1 - L ^ (-(3 / 4 : ℝ)) ≤ b := by linarith
    have hm : s.re ∈ Icc (1 - L ^ (-(3 / 4 : ℝ))) b ∧ s.im ∈ Icc (-T) T := by
      simpa [Rectangle, Complex.mem_reProdIm, uIcc_of_le hab,
        uIcc_of_le (show -T ≤ T by linarith)] using hs
    exact (hr L hL₀ (s + (u : ℂ) * Complex.I) (by simpa using hm.1.1)
      (by simpa using hm.1.2.trans hb2)
      (by simpa using hheight (abs_le.mpr hm.2)) hs1).1
  · intro t ht
    let s : ℂ := ((1 - L ^ (-(3 / 4 : ℝ)) : ℝ) : ℂ) +
      (t : ℂ) * Complex.I + (u : ℂ) * Complex.I
    have hn : L ^ (-(3 / 4 : ℝ)) ≤ ‖s - 1‖ := by
      have hh := Complex.abs_re_le_norm (s - 1)
      have he : (s - 1).re = -L ^ (-(3 / 4 : ℝ)) := by simp [s]
      rw [he, abs_neg, abs_of_nonneg hδ0.le] at hh
      exact hh
    have hs1 : s ≠ 1 := by intro he; simp [he] at hn; linarith
    have hi : ‖(s - 1)⁻¹‖ ≤ L ^ 2 := by
      rw [norm_inv]
      have hi := one_div_le_one_div_of_le hδ0 hn
      simp only [one_div] at hi
      apply hi.trans
      rw [← Real.rpow_neg hL0.le, neg_neg, ← Real.rpow_two]
      exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
    have hc := (happ le_rfl (by linarith) (abs_le.mpr ht) hs1).2
    exact (mrt_zeta_logderiv_of_correction hc hi).trans_eq (by ring)
  · intro σ hσ t ht
    let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I
    have hn : 1 ≤ ‖s - 1‖ := by
      have hh := Complex.abs_im_le_norm (s - 1)
      have ha := abs_add_le (t + u) (-u)
      rw [add_neg_cancel_right, abs_neg, ht] at ha
      have he : (s - 1).im = t + u := by simp [s]
      rw [he] at hh
      linarith
    have hs1 : s ≠ 1 := by intro he; norm_num [he] at hn
    have hi : ‖(s - 1)⁻¹‖ ≤ L ^ 2 := by
      rw [norm_inv]
      have hi : ‖s - 1‖⁻¹ ≤ 1 := by
        simpa only [one_div, inv_one] using
          one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hn
      exact hi.trans hLsq
    have hc := (happ hσ.1 (hσ.2.trans hb2) ht.le hs1).2
    exact (mrt_zeta_logderiv_of_correction hc hi).trans_eq (by ring)

end TwoPointCorrelations

end OAI

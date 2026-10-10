import OAI.NumberTheory.Ostmann.ZeroDensity.ZetaLocalFactorBound

namespace OAI

/-! # A near-one zeta zero contributes its full reciprocal gap -/

namespace Ostmann

open Complex Metric Set
open scoped BigOperators

theorem zetaAtHeight_logDeriv_translate (t : ℝ) (w : ℂ) :
    logDeriv (zetaAtHeight t) w = logDeriv regularizedZeta (w + characterZeroCenter t) := by
  change logDeriv (regularizedZeta ∘ (fun z : ℂ => z + characterZeroCenter t)) w = _
  rw [logDeriv_comp (g := fun z : ℂ => z + characterZeroCenter t)
    (regularizedZeta_analytic _).differentiableAt (differentiableAt_id.add_const _)]
  simp

theorem regularizedZeta_zero_re_lt_one (ρ : ℂ) (hρ : regularizedZeta ρ = 0) : ρ.re < 1 := by
  by_contra h
  exact regularizedZeta_ne_zero_right ρ (le_of_not_gt h) hρ

theorem zeta_near_zero_gap_bound : ∃ C : ℝ, 0 < C ∧ ∀ (ρ : ℂ),
    regularizedZeta ρ = 0 → 1 / 2 ≤ ρ.re → ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      1 / (σ - ρ.re) ≤
        (logDeriv regularizedZeta ((σ : ℂ) + (ρ.im : ℂ) * I)).re +
          C * Real.log (|ρ.im| + 2) := by
  obtain ⟨C, hC, hbound⟩ := zeta_local_factor_bound
  refine ⟨C, hC, ?_⟩
  intro ρ hρ hρhalf σ hσ hσ2
  have hρ1 := regularizedZeta_zero_re_lt_one ρ hρ
  let t := ρ.im
  let w : ℂ := ((σ - 2 : ℝ) : ℂ)
  let z : ℂ := ρ - characterZeroCenter t
  have hzval : z = ((ρ.re - 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [z, t, characterZeroCenter]
  have hz : z ∈ zetaDiskZeros t := by
    apply (mem_zetaDiskZeros t z).mpr
    refine ⟨?_, ?_⟩
    · rw [hzval, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      linarith
    · simpa only [zetaAtHeight, z, sub_add_cancel] using hρ
  have hw : ‖w‖ ≤ 5 / 4 := by
    rw [show w = ((σ - 2 : ℝ) : ℂ) from rfl, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    linarith
  have hwne : zetaAtHeight t w ≠ 0 := by
    apply regularizedZeta_ne_zero_right
    simp only [w, Complex.add_re, Complex.ofReal_re, characterZeroCenter_re]
    linarith
  have hb := hbound t w hw hwne
  have hnonneg (v : ℂ) (hv : v ∈ zetaDiskZeros t) :
      0 ≤ ((analyticOrderNatAt (zetaAtHeight t) v : ℂ) / (w - v)).re := by
    have hvre := zetaAtHeight_zero_left t v ((mem_zetaDiskZeros t v).mp hv).2
    rw [div_eq_mul_inv, Complex.mul_re]
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    apply mul_nonneg (Nat.cast_nonneg _)
    rw [Complex.inv_re]
    apply div_nonneg _ (Complex.normSq_nonneg _)
    simp only [Complex.sub_re, w, Complex.ofReal_re]
    linarith
  have hsingle := Finset.single_le_sum hnonneg hz
  have hord : 1 ≤ analyticOrderNatAt (zetaAtHeight t) z := by
    have he := (zetaAtHeight_analytic t z).analyticOrderAt_ne_zero.mpr
      ((mem_zetaDiskZeros t z).mp hz).2
    rw [← Nat.cast_analyticOrderNatAt (zetaAtHeight_order_ne_top t z)] at he
    have hn : analyticOrderNatAt (zetaAtHeight t) z ≠ 0 := by simpa using he
    omega
  have hdiff : w - z = ((σ - ρ.re : ℝ) : ℂ) := by
    rw [hzval]
    simp only [w]
    push_cast
    ring
  have hterm : ((analyticOrderNatAt (zetaAtHeight t) z : ℂ) / (w - z)).re =
      (analyticOrderNatAt (zetaAtHeight t) z : ℝ) / (σ - ρ.re) := by
    rw [hdiff]
    exact (Complex.ofReal_div _ _).symm ▸ rfl
  rw [hterm] at hsingle
  have hone : 1 / (σ - ρ.re) ≤ (analyticOrderNatAt (zetaAtHeight t) z : ℝ) / (σ - ρ.re) := by
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact_mod_cast hord
  have herr := Complex.re_le_norm
    (-(logDeriv (zetaAtHeight t) w -
      ∑ v ∈ zetaDiskZeros t, (analyticOrderNatAt (zetaAtHeight t) v : ℂ) / (w - v)))
  rw [norm_neg, Complex.neg_re, Complex.sub_re, Complex.re_sum] at herr
  have htranslate : w + characterZeroCenter t = (σ : ℂ) + (ρ.im : ℂ) * I := by
    apply Complex.ext <;> simp [w, t, characterZeroCenter]
  rw [zetaAtHeight_logDeriv_translate, htranslate] at herr
  rw [zetaAtHeight_logDeriv_translate, htranslate] at hb
  dsimp only [t] at hb herr hsingle
  linarith

end Ostmann

end OAI

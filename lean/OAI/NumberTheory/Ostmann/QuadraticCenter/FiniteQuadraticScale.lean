import OAI.NumberTheory.Ostmann.Quadratic.QuadraticScaleContinuity
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCommonCutoff

namespace OAI

/-! # A polynomial continuity bound for the scale parameter -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem quadraticDensitySum_scale_sub_bound {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (B : ℝ) (hg : ∀ x, ‖g x‖ ≤ B)
    (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R R' v : ℝ) (s W : ℕ)
    (hR : 1 ≤ R) (hR' : 1 ≤ R') (hv : 0 ≤ v) :
    ‖quadraticDensitySum g (Finset.Ioc 0 W) a θ Φ R v s -
      quadraticDensitySum g (Finset.Ioc 0 W) a θ Φ R' v s‖ ≤
      Real.sqrt ((s : ℝ) * v / q) * W * B *
        (SchwartzMap.seminorm ℝ 0 0 Φ +
          SchwartzMap.seminorm ℝ 0 1 Φ * ((s : ℝ) * v / q) * W ^ 2) * |R - R'| := by
  let D := Real.sqrt ((s : ℝ) * v / q)
  let c := fun x : ℝ => D * (Real.sqrt x)⁻¹
  let F := fun x : ℝ => ∑ w ∈ Finset.Ioc 0 W, quadraticDensityTerm g a θ Φ x v s w
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hB : 0 ≤ B := (norm_nonneg (g 0)).trans (hg 0)
  have hS0 : 0 ≤ SchwartzMap.seminorm ℝ 0 0 Φ := by positivity
  have hS1 : 0 ≤ SchwartzMap.seminorm ℝ 0 1 Φ := by positivity
  have hn (x : ℝ) (hx : 1 ≤ x) :
      quadraticDensitySum g (Finset.Ioc 0 W) a θ Φ x v s = (c x : ℂ) * F x := by
    unfold quadraticDensitySum
    rw [← Complex.ofReal_inv, quadratic_normalizer_factor q s x v (by linarith)]
  have hF : ‖F R‖ ≤ (W : ℝ) * (B * SchwartzMap.seminorm ℝ 0 0 Φ) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _w ∈ Finset.Ioc 0 W, B * SchwartzMap.seminorm ℝ 0 0 Φ := by
        apply Finset.sum_le_sum
        intro w _
        simp only [quadraticDensityTerm, norm_mul, norm_pow, norm_realAdditivePhase,
          one_pow, mul_one]
        exact mul_le_mul (hg _) (Φ.norm_le_seminorm ℝ _) (norm_nonneg _) hB
      _ = _ := by simp
  have hFdiff : ‖F R - F R'‖ ≤ (W : ℝ) *
      (B * SchwartzMap.seminorm ℝ 0 1 Φ * ((s : ℝ) * v / q) * W ^ 2 * |R - R'|) := by
    dsimp [F]
    rw [← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _w ∈ Finset.Ioc 0 W,
          B * SchwartzMap.seminorm ℝ 0 1 Φ * ((s : ℝ) * v / q) * W ^ 2 * |R - R'| := by
        apply Finset.sum_le_sum
        intro w hw
        exact quadraticDensityTerm_scale_sub_bound g B hg a θ Φ R R' v s w W hR hR' hv
          (Finset.mem_Ioc.mp hw).2
      _ = _ := by simp
  have hc' : ‖(c R' : ℂ)‖ ≤ D := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by dsimp [c]; positivity)]
    exact mul_le_of_le_one_right hD (inv_le_one_of_one_le₀
      (Real.le_sqrt_of_sq_le (by simpa using hR')))
  have hcdiff : ‖(c R : ℂ) - (c R' : ℂ)‖ ≤ D * |R - R'| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have he : c R - c R' = D * ((Real.sqrt R)⁻¹ - (Real.sqrt R')⁻¹) := by dsimp [c]; ring
    rw [he, abs_mul, abs_of_nonneg hD]
    exact mul_le_mul_of_nonneg_left (inv_sqrt_sub_abs_le_of_one_le R R' hR hR') hD
  rw [hn R hR, hn R' hR']
  have he : (c R : ℂ) * F R - (c R' : ℂ) * F R' =
      ((c R : ℂ) - (c R' : ℂ)) * F R + (c R' : ℂ) * (F R - F R') := by ring
  rw [he]
  calc
    _ ≤ ‖((c R : ℂ) - (c R' : ℂ)) * F R‖ + ‖(c R' : ℂ) * (F R - F R')‖ := norm_add_le _ _
    _ = ‖(c R : ℂ) - (c R' : ℂ)‖ * ‖F R‖ + ‖(c R' : ℂ)‖ * ‖F R - F R'‖ := by rw [norm_mul, norm_mul]
    _ ≤ (D * |R - R'|) * ((W : ℝ) * (B * SchwartzMap.seminorm ℝ 0 0 Φ)) +
        D * ((W : ℝ) * (B * SchwartzMap.seminorm ℝ 0 1 Φ * ((s : ℝ) * v / q) * W ^ 2 * |R - R'|)) := by
      gcongr
    _ = _ := by dsimp [D]; ring

/-- Both original infinite series are replaced by the same support at
`Rmax`; the finite scale estimate then applies without a cutoff error. -/
theorem positiveQuadraticSum_scale_sub_bound {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (B : ℝ) (hg : ∀ x, ‖g x‖ ≤ B)
    (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R R' Rmax v H : ℝ) (s : ℕ)
    (hR : 1 ≤ R) (hR' : 1 ≤ R') (hRR : R ≤ Rmax) (hR'R : R' ≤ Rmax)
    (hv : 0 < v) (hH : 0 ≤ H) (hs : 0 < s)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    let W := ⌊Real.sqrt (H * Rmax * q / ((s : ℝ) * v))⌋₊
    ‖positiveQuadraticSum g a θ Φ R v s - positiveQuadraticSum g a θ Φ R' v s‖ ≤
      Real.sqrt ((s : ℝ) * v / q) * W * B *
        (SchwartzMap.seminorm ℝ 0 0 Φ +
          SchwartzMap.seminorm ℝ 0 1 Φ * ((s : ℝ) * v / q) * W ^ 2) * |R - R'| := by
  dsimp only
  rw [positiveQuadraticSum_eq_upper_cutoff g a θ Φ R Rmax v H s (by linarith) hRR hv hH hs hΦ,
    positiveQuadraticSum_eq_upper_cutoff g a θ Φ R' Rmax v H s (by linarith) hR'R hv hH hs hΦ]
  exact quadraticDensitySum_scale_sub_bound g B hg a θ Φ R R' v s _ hR hR' hv.le

end Ostmann

end OAI

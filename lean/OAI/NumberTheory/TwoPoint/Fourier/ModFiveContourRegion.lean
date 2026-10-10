import OAI.NumberTheory.TwoPoint.Fourier.ModFiveStripBound
import OAI.NumberTheory.TwoPoint.Fourier.ModFiveContourKernel

namespace OAI

/-! A common closed zero-free rectangle and its uniform logarithmic-
derivative bound. This prepares the finite contour shift without a
height-dependent analyticity assumption.
-/

namespace TwoPointCorrelations

open Complex Set

theorem modFive_logderiv_rectangles : ∃ a C : ℝ,
    0 < a ∧ a ≤ 1 / 4 ∧ 0 < C ∧
    ∀ (χ : DirichletCharacter ℂ 5), χ ≠ 1 → ∀ T : ℝ, 2 ≤ T →
      ∀ s : ℂ, 1 - a / Real.log (T + 2) ≤ s.re → s.re ≤ 2 → |s.im| ≤ T →
        DirichletCharacter.LFunction χ s ≠ 0 ∧
        ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
          C * Real.log (T + 2) ^ 2 := by
  obtain ⟨c, C, hc, hC, hbound⟩ := modFive_logderiv_strip_bound
  let a := min c (1 / 4)
  have ha : 0 < a := lt_min hc (by norm_num)
  have hac : a ≤ c := min_le_left _ _
  refine ⟨a, C, ha, min_le_right _ _, hC, ?_⟩
  intro χ hχ T hT s hs hs2 ht
  have hH : 0 < Real.log (T + 2) := Real.log_pos (by linarith)
  have hh := modFive_log_height_pos s.im
  have hlog : Real.log (|s.im| + 2) ≤ Real.log (T + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hdiv : a / Real.log (T + 2) ≤ c / Real.log (|s.im| + 2) :=
    (div_le_div_of_nonneg_left ha.le hh hlog).trans
      (div_le_div_of_nonneg_right hac hh.le)
  have hs' : 1 - c / Real.log (|s.im| + 2) ≤ s.re := by linarith
  have he : (s.re : ℂ) + Complex.I * (s.im : ℂ) = s := by
    apply Complex.ext <;> simp
  have hb := hbound χ hχ s.im s.re hs' hs2
  rw [he] at hb
  refine ⟨hb.1, hb.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh.le hlog 2) hC.le

lemma modFive_logderiv_differentiableAt (χ : DirichletCharacter ℂ 5)
    (hχ : χ ≠ 1) {s : ℂ} (hs : DirichletCharacter.LFunction χ s ≠ 0) :
    DifferentiableAt ℂ (fun z =>
      -deriv (DirichletCharacter.LFunction χ) z / DirichletCharacter.LFunction χ z) s := by
  have hf := DirichletCharacter.differentiable_LFunction hχ
  exact ((hf.analyticAt s).deriv.differentiableAt.neg).div (hf s) hs

lemma modFive_perron_integrand_differentiableAt (χ : DirichletCharacter ℂ 5)
    (hχ : χ ≠ 1) {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hs : DirichletCharacter.LFunction χ s ≠ 0) (hs0 : s ≠ 0) (hs1 : s + 1 ≠ 0) :
    DifferentiableAt ℂ (fun z =>
      (-deriv (DirichletCharacter.LFunction χ) z / DirichletCharacter.LFunction χ z) *
        modFivePerronKernel x z) s := by
  apply (modFive_logderiv_differentiableAt χ hχ hs).mul
  unfold modFivePerronKernel
  apply DifferentiableAt.div
  · exact differentiableAt_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  · fun_prop
  · exact mul_ne_zero hs0 hs1

end TwoPointCorrelations

end OAI

import Mathlib.Analysis.InnerProductSpace.l2Space

namespace OAI

/-! # Uniformly bounded operators on a countable Hilbert sum -/

namespace KadisonKastler

noncomputable section

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace ℂ (E n)]
  (F : ∀ n, E n →L[ℂ] E n) (C : ℝ) (hC : 0 ≤ C) (hF : ∀ n, ‖F n‖ ≤ C)

include hC hF in
theorem hilbertSumOperator_memLp (f : lp E 2) : Memℓp (fun n => F n (f n)) 2 := by
  apply ((lp.memℓp f).const_smul (C : ℂ)).mono'
  intro n
  simpa only [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hC] using
    ((F n).le_opNorm (f n)).trans (mul_le_mul_of_nonneg_right (hF n) (norm_nonneg _))

def hilbertSumOperatorLinear : lp E 2 →ₗ[ℂ] lp E 2 where
  toFun f := ⟨fun n => F n (f n), hilbertSumOperator_memLp F C hC hF f⟩
  map_add' f g := by
    apply lp.ext
    funext n
    exact (F n).map_add (f n) (g n)
  map_smul' c f := by
    apply lp.ext
    funext n
    exact (F n).map_smul c (f n)

theorem hilbertSumOperatorLinear_norm_le (f : lp E 2) :
    ‖hilbertSumOperatorLinear F C hC hF f‖ ≤ C * ‖f‖ := by
  calc
    _ ≤ ‖(C : ℂ) • f‖ := by
      apply lp.norm_mono (by norm_num)
      intro n
      change ‖F n (f n)‖ ≤ ‖((C : ℂ) • f) n‖
      simpa only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hC] using
        ((F n).le_opNorm (f n)).trans (mul_le_mul_of_nonneg_right (hF n) (norm_nonneg _))
    _ = _ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]

def hilbertSumOperator : lp E 2 →L[ℂ] lp E 2 :=
  (hilbertSumOperatorLinear F C hC hF).mkContinuous C
    (hilbertSumOperatorLinear_norm_le F C hC hF)

@[simp] theorem hilbertSumOperator_apply (f : lp E 2) (n : ℕ) :
    hilbertSumOperator F C hC hF f n = F n (f n) := rfl

theorem hilbertSumOperator_norm_le : ‖hilbertSumOperator F C hC hF‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

theorem hilbertSumOperator_single (n : ℕ) (v : E n) :
    hilbertSumOperator F C hC hF (lp.single 2 n v) = lp.single 2 n (F n v) := by
  apply lp.ext
  funext i
  by_cases hi : i = n
  · subst i
    simp only [hilbertSumOperator_apply, lp.single_apply_self]
  · simp [hilbertSumOperator_apply, lp.single_apply, hi]

end

end KadisonKastler

end OAI

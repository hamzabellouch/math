import OAI.NumberTheory.Ostmann.Construction.GiantReciprocalFactor
import OAI.NumberTheory.Ostmann.Characters.PolynomialWeightPair

namespace OAI

/-! # The literal two outer cutoff priors and the diagonal reciprocal factor -/

namespace Ostmann
open scoped BigOperators Classical

private noncomputable def onePolynomialFactor : ClippedPolynomialFactor where
  polynomial := 0
  profile := fun _ => 1
  lo := 0
  hi := 0
  bound := 1
  lip := 0
  lo_le_hi := le_rfl
  bound_nonneg := zero_le_one
  lip_nonneg := le_rfl
  norm_le := by intro _ _; simp
  lipschitz := by intro _ _ _ _; simp

@[simp] private theorem onePolynomialFactor_polynomial : onePolynomialFactor.polynomial = 0 := rfl

noncomputable def giantOuterFactors (L R : Polynomial ℝ) (φ : ℝ → ℝ)
    (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (diagonal : Bool) : Fin 3 → ClippedPolynomialFactor :=
  ![logCutoffPolynomialFactor L φ Jleft B D hB hD hφ hlip,
    logCutoffPolynomialFactor R φ Jright B D hB hD hφ hlip,
    if diagonal then giantReciprocalFactor R Jright else onePolynomialFactor]

noncomputable def giantOuterScalar (diagonal : Bool) : ℝ := if diagonal then Real.exp 1 else 1

/-- Both actual cutoff priors are retained. In the diagonal environment the
remaining factor is precisely exp(G_R)/R, including all off-support zeros. -/
theorem giantOuterFactors_value (L R : Polynomial ℝ) (φ : ℝ → ℝ)
    (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (x : ℝ) :
    (giantOuterScalar diagonal : ℂ) *
      smoothPolynomialWeight (giantOuterFactors L R φ Jleft Jright B D hB hD hφ hlip diagonal) x =
        (positiveLogCutoff φ Jleft (L.eval x) : ℂ) * (positiveLogCutoff φ Jright (R.eval x) : ℂ) *
          (if diagonal then ((Real.exp Jright / R.eval x : ℝ) : ℂ) else 1) := by
  have hL := logCutoffPolynomialFactor_value L φ Jleft B D hB hD hφ hlip hout x
  have hR := logCutoffPolynomialFactor_value R φ Jright B D hB hD hφ hlip hout x
  have hone : onePolynomialFactor.value x = 1 := rfl
  have hrec := giantReciprocalFactor_cutoff R φ Jright B D hB hD hφ hlip hout x
  cases diagonal
  · simp only [giantOuterScalar, Bool.false_eq_true, ite_false, Complex.ofReal_one,
      giantOuterFactors, smoothPolynomialWeight, Fin.prod_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Fin.prod_univ_zero, mul_one, one_mul, hL, hR, hone]
  · simp only [giantOuterScalar, ite_true, giantOuterFactors, smoothPolynomialWeight,
      Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Fin.prod_univ_zero, mul_one]
    calc
      _ = (logCutoffPolynomialFactor L φ Jleft B D hB hD hφ hlip).value x *
          ((logCutoffPolynomialFactor R φ Jright B D hB hD hφ hlip).value x *
            ((Real.exp 1 : ℂ) * (giantReciprocalFactor R Jright).value x)) := by ring
      _ = _ := by rw [hL, hrec]; ring

theorem giantOuterFactors_budget (L R : Polynomial ℝ) (φ : ℝ → ℝ)
    (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (diagonal : Bool) :
    smoothPolynomialBudget (giantOuterFactors L R φ Jleft Jright B D hB hD hφ hlip diagonal) =
      (2 * B + D * (Real.exp 2 - 1)) ^ 2 * (if diagonal then 1 + Real.exp 2 else 2) := by
  have hL := logCutoffPolynomialFactor_budget L φ Jleft B D hB hD hφ hlip
  have hR := logCutoffPolynomialFactor_budget R φ Jright B D hB hD hφ hlip
  cases diagonal
  · simp only [giantOuterFactors, Bool.false_eq_true, ite_false, smoothPolynomialBudget,
      Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Fin.prod_univ_zero, mul_one, onePolynomialFactor]
    rw [hL, hR]
    ring
  · simp only [giantOuterFactors, ite_true, smoothPolynomialBudget,
      Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Fin.prod_univ_zero, mul_one]
    rw [hL, hR, giantReciprocalFactor_budget]
    ring

end Ostmann

end OAI

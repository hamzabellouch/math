import OAI.Probability.FreeIsing.Trees.WordAction

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.TreeKoopman

def centeredGenerator {d : ℕ} (c : Fin d) :
    centeredL2 (labelMeasure d) →L[ℝ] centeredL2 (labelMeasure d) :=
  (generatorOperator c).restrict
    (koopmanL2_preserves_centered (reflection c) (reflection_measurePreserving c)
      (reflection_involutive c))

@[simp] theorem centeredGenerator_apply_coe {d : ℕ} (c : Fin d)
    (f : centeredL2 (labelMeasure d)) :
    (centeredGenerator c f : Lp ℝ 2 (labelMeasure d)) =
      generatorOperator c (f : Lp ℝ 2 (labelMeasure d)) := rfl

@[simp] theorem centeredGenerator_sq {d : ℕ} (c : Fin d) :
    centeredGenerator c * centeredGenerator c = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  change generatorOperator c (generatorOperator c (f : Lp ℝ 2 (labelMeasure d))) = f
  have h := congrArg (fun A : Lp ℝ 2 (labelMeasure d) →L[ℝ] Lp ℝ 2 (labelMeasure d) =>
    A (f : Lp ℝ 2 (labelMeasure d))) (generatorOperator_sq c)
  exact h

theorem centered_listProduct_apply_coe {d : ℕ} (w : List (Fin d))
    (f : centeredL2 (labelMeasure d)) :
    ((w.map centeredGenerator).prod f : Lp ℝ 2 (labelMeasure d)) =
      (w.map generatorOperator).prod (f : Lp ℝ 2 (labelMeasure d)) := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp]
    rw [centeredGenerator_apply_coe, ih]

theorem centered_wordOperator_apply_coe {d : ℕ} (v : TreeVertex d)
    (f : centeredL2 (labelMeasure d)) :
    (RadialWalk.wordOperator centeredGenerator v f : Lp ℝ 2 (labelMeasure d)) =
      RadialWalk.wordOperator generatorOperator v (f : Lp ℝ 2 (labelMeasure d)) :=
  centered_listProduct_apply_coe v.1 f

theorem centered_operatorAverage_eq {d : ℕ} :
    RadialWalk.operatorAverage (centeredGenerator (d := d)) = centeredAverage d := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  rw [centeredAverage_apply_coe]
  simp only [RadialWalk.operatorAverage, smul_apply, sum_apply,
    Submodule.coe_smul, Submodule.coe_sum, centeredGenerator_apply_coe]
  rw [← operatorAverage_eq, RadialWalk.operatorAverage_apply]

theorem centered_wordOperator_inner {d : ℕ} (v : TreeVertex d)
    (f : centeredL2 (labelMeasure d)) :
    inner ℝ f (RadialWalk.wordOperator centeredGenerator v f) =
      inner ℝ (f : Lp ℝ 2 (labelMeasure d))
        (RadialWalk.wordOperator generatorOperator v (f : Lp ℝ 2 (labelMeasure d))) := by
  change inner ℝ (f : Lp ℝ 2 (labelMeasure d))
    ((RadialWalk.wordOperator centeredGenerator v f : centeredL2 (labelMeasure d)) :
      Lp ℝ 2 (labelMeasure d)) = _
  rw [centered_wordOperator_apply_coe]

end Problem367.TreeKoopman

end

end OAI

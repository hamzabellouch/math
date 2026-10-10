import Mathlib
import OAI.Probability.BinarySweep.Conditional.Placement

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

structure PathExtension {b h h' : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (H' : PathFamily bits h') where
  labels : Fin h ↪ Fin h'
  position_eq : ∀ t i, H'.position t (labels i) = H.position t i

namespace PathExtension
variable {b h h' : ℕ} {bits : Fin b → ℕ}
  {H : PathFamily bits h} {H' : PathFamily bits h'}

def lineEmbedding (E : PathExtension H H') (j : Fin b) (y : GridOutside bits j) :
    LinePaths H j y ↪ LinePaths H' j y where
  toFun i := ⟨E.labels i.val, by
    change (fun a : {a : Fin b // a ≠ j} => H'.position j.castSucc (E.labels i.val) a) = y
    rw [E.position_eq]
    exact i.property⟩
  inj' i k hik := Subtype.ext (E.labels.injective (congrArg Subtype.val hik))

lemma lineInput_eq (E : PathExtension H H') (j : Fin b) (y : GridOutside bits j)
    (i : LinePaths H j y) :
    lineInput H' j y (E.lineEmbedding j y i) = lineInput H j y i := by
  change H'.position j.castSucc (E.labels i.val) j = H.position j.castSucc i.val j
  rw [E.position_eq]

lemma lineOutput_eq (E : PathExtension H H') (j : Fin b) (y : GridOutside bits j)
    (i : LinePaths H j y) :
    lineOutput H' j y (E.lineEmbedding j y i) = lineOutput H j y i := by
  change H'.position j.succ (E.labels i.val) j = H.position j.succ i.val j
  rw [E.position_eq]

lemma pathEvent_mono (E : PathExtension H H') {g : GridChoices bits}
    (hg : pathEvent H' g) : pathEvent H g := by
  intro j i
  simpa only [E.position_eq] using hg j (E.labels i)

lemma card_le (E : PathExtension H H') : h ≤ h' := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective E.labels E.labels.injective

end PathExtension

lemma localPathWeight_pos_comparison {b h r : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (hd : ∀ j, bits j ≤ 2*r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r)
    (j : Fin b) (y : GridOutside bits j) : 0 < localPathWeight H z j y := by
  unfold localPathWeight
  have hw := @assignmentWeight_comparison (Slot (bits j)) (LinePaths H j y) _ _
    (lineLaw (bits j) z) ?_ ?_ (lineInput H j y) (lineOutput H j y)
  · have hm : 0 < (Nat.descFactorial (Fintype.card (Slot (bits j)))
        (Fintype.card (LinePaths H j y)) : ℝ) := by
      exact_mod_cast Nat.descFactorial_pos.mpr
        (Fintype.card_le_of_injective (lineInput H j y) (lineInput H j y).injective)
    exact lt_of_lt_of_le (by positivity) hw.1
  · intro σ
    simpa only [uniformLaw, Fintype.card_perm] using
      (lineLaw_comparison r (bits j) (hd j) hz hzr σ).1
  · intro σ
    simpa only [uniformLaw, Fintype.card_perm] using
      (lineLaw_comparison r (bits j) (hd j) hz hzr σ).2

lemma lineExtension_log_bound {b h h' r : ℕ} {bits : Fin b → ℕ}
    {H : PathFamily bits h} {H' : PathFamily bits h'} (E : PathExtension H H')
    (hd : ∀ j, bits j ≤ 2*r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r)
    (j : Fin b) (y : GridOutside bits j) :
    Real.log (localPathWeight H' z j y / localPathWeight H z j y) ≤
      fallingCost (2^bits j) (lineHoles H' j y) - fallingCost (2^bits j) (lineHoles H j y) -
      ((lineHoles H' j y : ℝ) - lineHoles H j y) * Real.log (2^bits j : ℕ) +
      Real.log 4 * ((lineHoles H' j y : ℝ) - lineHoles H j y) := by
  have he := @assignmentWeight_log_ratio_le (Slot (bits j)) (LinePaths H j y)
    (LinePaths H' j y) _ _ _ Fintype.card_pos (lineLaw (bits j) z)
    ?_ ?_ (lineInput H j y) (lineOutput H j y) (lineInput H' j y) (lineOutput H' j y)
      (E.lineEmbedding j y) (E.lineInput_eq j y) (E.lineOutput_eq j y)
  · simpa only [localPathWeight, lineHoles, Slot, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_bool] using he
  · intro σ
    simpa only [uniformLaw, Fintype.card_perm] using
      (lineLaw_comparison r (bits j) (hd j) hz hzr σ).1
  · intro σ
    simpa only [uniformLaw, Fintype.card_perm] using
      (lineLaw_comparison r (bits j) (hd j) hz hzr σ).2

lemma log_gridSize {b : ℕ} (bits : Fin b → ℕ) :
    Real.log (gridSize bits : ℝ) = ∑ j, Real.log (2^bits j : ℕ) := by
  unfold gridSize
  rw [Nat.cast_prod, Real.log_prod]
  intro j _
  positivity

lemma sum_lineHoles_sub {b h h' : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (H' : PathFamily bits h') (j : Fin b) :
    ∑ y : GridOutside bits j, ((lineHoles H' j y : ℝ) - lineHoles H j y) = (h' : ℝ) - h := by
  rw [Finset.sum_sub_distrib, ← Nat.cast_sum, ← Nat.cast_sum, sum_lineHoles, sum_lineHoles]

lemma pathCost_eq_sum {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) :
    pathCost H = ∑ j, ∑ y, fallingCost (2^bits j) (lineHoles H j y) := rfl

theorem pathExtension_log_ratio {b h h' r : ℕ} {bits : Fin b → ℕ}
    {H : PathFamily bits h} {H' : PathFamily bits h'} (E : PathExtension H H')
    (hd : ∀ j, bits j ≤ 2*r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r) :
    Real.log (conditionalNormalizer H' z / conditionalNormalizer H z) ≤
      pathCost H' - pathCost H - ((h' : ℝ) - h) * Real.log (gridSize bits) +
        Real.log 4 * ((h' : ℝ) - h) * b := by
  have hposH := localPathWeight_pos_comparison H hd hz hzr
  have hposH' := localPathWeight_pos_comparison H' hd hz hzr
  rw [conditionalNormalizer_eq_prod, conditionalNormalizer_eq_prod]
  rw [← Finset.prod_div_distrib]
  simp_rw [← Finset.prod_div_distrib]
  rw [Real.log_prod (fun j _ => Finset.prod_ne_zero_iff.mpr (fun y _ =>
    (div_pos (hposH' j y) (hposH j y)).ne'))]
  simp_rw [Real.log_prod (fun y _ => (div_pos (hposH' _ y) (hposH _ y)).ne')]
  calc
    _ ≤ ∑ j, ∑ y,
        (fallingCost (2^bits j) (lineHoles H' j y) - fallingCost (2^bits j) (lineHoles H j y) -
        ((lineHoles H' j y : ℝ) - lineHoles H j y) * Real.log (2^bits j : ℕ) +
        Real.log 4 * ((lineHoles H' j y : ℝ) - lineHoles H j y)) := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_le_sum (fun y _ => lineExtension_log_bound E hd hz hzr j y)
    _ = _ := by
      simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_mul, ← Finset.mul_sum]
      simp_rw [sum_lineHoles_sub]
      rw [pathCost_eq_sum, pathCost_eq_sum, log_gridSize]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      ring

def conditionalEventWeight {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) (P : GridChoices bits → Prop) : ℝ :=
  ∑ g : ConditionalChoices H, if P g.val then conditionalChoiceWeight H z g else 0

lemma pathExtension_event_ratio {b h h' : ℕ} {bits : Fin b → ℕ}
    {H : PathFamily bits h} {H' : PathFamily bits h'} (E : PathExtension H H') (z : ℝ) :
    conditionalEventWeight H z (pathEvent H') =
      conditionalNormalizer H' z / conditionalNormalizer H z := by
  unfold conditionalEventWeight conditionalChoiceWeight
  have hdiv (g : ConditionalChoices H) :
      (if pathEvent H' g.val then gridWeight bits z g.val / conditionalNormalizer H z else 0) =
      (if pathEvent H' g.val then gridWeight bits z g.val else 0) / conditionalNormalizer H z := by
    split_ifs <;> simp only [zero_div]
  simp_rw [hdiv]
  rw [← Finset.sum_div]
  congr 1
  rw [← Finset.sum_subtype (Finset.univ.filter (pathEvent H)) (by simp)
    (fun g => if pathEvent H' g then gridWeight bits z g else 0)]
  rw [Finset.sum_filter]
  unfold conditionalNormalizer
  apply Finset.sum_congr rfl
  intro g _
  by_cases hg : pathEvent H' g
  · simp only [hg, E.pathEvent_mono hg, ite_true]
  · simp only [hg, ite_false, ite_self]

lemma gridSize_pos {b : ℕ} (bits : Fin b → ℕ) : 0 < gridSize bits := by
  unfold gridSize
  exact Finset.prod_pos (fun j _ => Nat.pow_pos (by norm_num))

theorem pathExtension_probability_bound {b h k r : ℕ} {bits : Fin b → ℕ}
    {H : PathFamily bits h} {H' : PathFamily bits (h+k)} (E : PathExtension H H')
    (hd : ∀ j, bits j ≤ 2*r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r) :
    conditionalEventWeight H z (pathEvent H') ≤
      (gridSize bits : ℝ) ^ (-(k : ℝ)) *
        Real.exp (pathCost H' - pathCost H + Real.log 4 * k * b) := by
  rw [pathExtension_event_ratio E]
  have hp : 0 < conditionalNormalizer H' z / conditionalNormalizer H z := by
    rw [conditionalNormalizer_eq_prod, conditionalNormalizer_eq_prod]
    apply div_pos <;> apply Finset.prod_pos <;> intro j _ <;>
      apply Finset.prod_pos <;> intro y _
    · exact localPathWeight_pos_comparison H' hd hz hzr j y
    · exact localPathWeight_pos_comparison H hd hz hzr j y
  have hs : (0 : ℝ) < gridSize bits := by exact_mod_cast gridSize_pos bits
  have he := pathExtension_log_ratio E hd hz hzr
  simp only [Nat.cast_add, add_sub_cancel_left] at he
  calc
    _ ≤ Real.exp (pathCost H' - pathCost H - (k : ℝ) * Real.log (gridSize bits) +
        Real.log 4 * k * b) := (Real.log_le_iff_le_exp hp).mp he
    _ = _ := by
      rw [Real.rpow_def_of_pos hs, ← Real.exp_add]
      congr 1
      ring

end BinaryCoordinateSweeps

end

end OAI

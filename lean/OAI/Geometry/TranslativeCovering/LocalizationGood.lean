import OAI.Geometry.TranslativeCovering.LocalizationRounding

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace LocalizationGood
open Set MeasureTheory Metric LatticeAveraging
open scoped BigOperators ENNReal

noncomputable def countFn {n : ℕ} (B : Set (Space n)) : Space n → ℝ≥0∞ := B.indicator (fun _ => 1)
noncomputable def weightedFn {n : ℕ} (a β : ℝ) : Space n → ℝ≥0∞ :=
  (closedBall (0 : Space n) β).indicator (fun x => ENNReal.ofReal (LocalizationRounding.weight n a ‖x‖))
lemma measurable_weightedFn {n : ℕ} (a β : ℝ) : Measurable (weightedFn (n := n) a β) := by
  apply Measurable.indicator _ measurableSet_closedBall
  apply Measurable.ennreal_ofReal
  exact (continuous_const.add (continuous_const.mul
    ((continuous_const.sub (continuous_norm.pow 2 |>.div_const (a^2))).max continuous_const))).measurable

lemma term_le_field {n : ℕ} {I : Type u_1} [Fintype I] (Λ : Submodule ℤ (Space n))
    (p : I → Space n) (f : Space n → ℝ≥0∞) (y : Space n) (i : I) (l : Λ) :
    f (y-p i-l.val) ≤ field Λ p f y := by
  calc
    _ ≤ ∑' l : Λ,f (y-p i-l.val) := ENNReal.le_tsum l
    _ ≤ ∑ j,∑' l : Λ,f (y-p j-l.val) := Finset.single_le_sum (f := fun j : I => ∑' l : Λ,f (y-p j-l.val)) (fun _ _ => bot_le) (Finset.mem_univ i)

lemma inner_zero {n : ℕ} {I : Type u_2} [Fintype I] (Λ : Submodule ℤ (Space n))
    (p : I → Space n) (r : ℝ) (y : Space n) :
    field Λ p (countFn (ball (0 : Space n) r)) y = 0 ↔ ∀ (i : I) (l : Λ),r ≤ ‖y-p i-l.val‖ := by
  constructor
  · intro h i l
    by_contra hr
    have hmem : y-p i-l.val ∈ ball (0 : Space n) r := by simpa using lt_of_not_ge hr
    have hh := term_le_field Λ p (countFn (ball (0 : Space n) r)) y i l
    have he : countFn (ball (0 : Space n) r) (y-p i-l.val) = 1 := by simp [countFn,hmem]
    rw [he,h] at hh
    exact (by norm_num at hh)
  · intro h
    unfold field
    apply Finset.sum_eq_zero
    intro i _
    apply ENNReal.tsum_eq_zero.mpr
    intro l
    have hnot : y-p i-l.val ∉ ball (0 : Space n) r := by simpa using not_lt.mpr (h i l)
    simp [countFn,hnot]

noncomputable def good {n : ℕ} {I : Type u_3} [Fintype I] (Λ : Submodule ℤ (Space n))
    (p : I → Space n) (a r β : ℝ) (C : ℝ≥0∞) : Set (Space n) :=
  {y | field Λ p (countFn (ball (0 : Space n) r)) y = 0 ∧
    field Λ p (countFn (closedBall (0 : Space n) β)) y ≤ C ∧ field Λ p (weightedFn a β) y ≤ C}

lemma measurable_good {n : ℕ} {I : Type u_4} [Fintype I] (Λ : Submodule ℤ (Space n))
    [DiscreteTopology Λ] (p : I → Space n) (a r β : ℝ) (C : ℝ≥0∞) :
    MeasurableSet (good Λ p a r β C) := by
  exact (measurableSet_eq_fun (measurable_field Λ p (measurable_const.indicator measurableSet_ball)) measurable_const).inter
    ((measurableSet_le (measurable_field Λ p (measurable_const.indicator measurableSet_closedBall)) measurable_const).inter
      (measurableSet_le (measurable_field Λ p (measurable_weightedFn a β)) measurable_const))

lemma periodic_good {n : ℕ} {I : Type u_5} [Fintype I] (Λ : Submodule ℤ (Space n))
    (p : I → Space n) (a r β : ℝ) (C : ℝ≥0∞) (y : Space n) (l : Λ) :
    y+l.val ∈ good Λ p a r β C ↔ y ∈ good Λ p a r β C := by
  simp only [good,mem_ofPred_eq,periodic]

lemma bad_bound {n : ℕ} {I : Type u_6} [Fintype I] (Λ : Submodule ℤ (Space n))
    [DiscreteTopology Λ] (p : I → Space n) (a r β : ℝ) (C : ℝ≥0∞)
    (hC : C ≠ 0) (hCtop : C ≠ ∞) (P : Measure (Space n)) [IsProbabilityMeasure P]
    (hinner : ∫⁻ y,field Λ p (countFn (ball (0 : Space n) r)) y ∂P ≤ 1/200)
    (houter : ∫⁻ y,field Λ p (countFn (closedBall (0 : Space n) β)) y ∂P ≤ C*(3/2000))
    (hweight : ∫⁻ y,field Λ p (weightedFn a β) y ∂P ≤ C*(5/2000)) :
    P (good Λ p a r β C)ᶜ ≤ 1/100 := by
  let A := field Λ p (countFn (ball (0 : Space n) r))
  let B := field Λ p (countFn (closedBall (0 : Space n) β))
  let W := field Λ p (weightedFn a β)
  have hA : Measurable A := measurable_field Λ p (measurable_const.indicator measurableSet_ball)
  have hB : Measurable B := measurable_field Λ p (measurable_const.indicator measurableSet_closedBall)
  have hW : Measurable W := measurable_field Λ p (measurable_weightedFn a β)
  have hsub : (good Λ p a r β C)ᶜ ⊆ {y | 1 ≤ A y} ∪ {y | C ≤ B y} ∪ {y | C ≤ W y} := by
    intro y hy
    by_cases hb : B y ≤ C
    · by_cases hw : W y ≤ C
      · have ha : A y ≠ 0 := fun hz => hy ⟨hz,hb,hw⟩
        have hnot : ¬∀ (i : I) (l : Λ),r ≤ ‖y-p i-l.val‖ := by
          intro hall; exact ha ((inner_zero Λ p r y).mpr hall)
        push Not at hnot
        obtain ⟨i,l,hl⟩ := hnot
        have hm : y-p i-l.val ∈ ball (0 : Space n) r := by simpa using hl
        have he := term_le_field Λ p (countFn (ball (0 : Space n) r)) y i l
        exact Or.inl (Or.inl (by
          change 1 ≤ field Λ p (countFn (ball (0 : Space n) r)) y
          convert he using 1
          simp [countFn,hm]))
      · exact Or.inr (le_of_not_ge hw)
    · exact Or.inl (Or.inr (le_of_not_ge hb))
  have ha := meas_ge_le_lintegral_div (μ := P) hA.aemeasurable (by norm_num : (1:ℝ≥0∞) ≠ 0) (by norm_num : (1:ℝ≥0∞) ≠ ∞)
  have hb := meas_ge_le_lintegral_div (μ := P) hB.aemeasurable hC hCtop
  have hw := meas_ge_le_lintegral_div (μ := P) hW.aemeasurable hC hCtop
  have hbb : P {y | C ≤ B y} ≤ 3/2000 := by
    apply hb.trans
    apply (ENNReal.div_le_div_right houter C).trans_eq
    rw [mul_comm,ENNReal.mul_div_cancel_right hC hCtop]
  have hww : P {y | C ≤ W y} ≤ 5/2000 := by
    apply hw.trans
    apply (ENNReal.div_le_div_right hweight C).trans_eq
    rw [mul_comm,ENNReal.mul_div_cancel_right hC hCtop]
  have haa : P {y | 1 ≤ A y} ≤ 1/200 := by simpa using ha.trans (ENNReal.div_le_div_right hinner 1)
  calc
    _ ≤ P ({y | 1 ≤ A y} ∪ {y | C ≤ B y} ∪ {y | C ≤ W y}) := measure_mono hsub
    _ ≤ (P {y | 1 ≤ A y}+P {y | C ≤ B y})+P {y | C ≤ W y} :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ (1/200+3/2000)+5/2000 := add_le_add (add_le_add haa hbb) hww
    _ ≤ 1/100 := by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      rw [ENNReal.toReal_add (by finiteness) (by finiteness),ENNReal.toReal_add (by finiteness) (by finiteness)]
      norm_num [ENNReal.toReal_div]

end LocalizationGood

end OAI

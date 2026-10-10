import OAI.Probability.InvariantIsing.Fields.FieldHeightSupport
import OAI.Probability.InvariantIsing.Fields.FieldVaryingContinuity

namespace OAI

/-! A bounded strict-height approximation of an arbitrary finite field.
Every variance increment is increased by the same small scalar. -/

noncomputable section
open IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

def fieldHeightEpsilon (t : ℝ) : ℝ := max 0 (min t 1)

lemma fieldHeightEpsilon_nonneg (t : ℝ) : 0 ≤ fieldHeightEpsilon t := le_max_left _ _

lemma fieldHeightEpsilon_le_one (t : ℝ) : fieldHeightEpsilon t ≤ 1 :=
  max_le zero_le_one (min_le_right _ _)

lemma continuous_fieldHeightEpsilon : Continuous fieldHeightEpsilon := by
  unfold fieldHeightEpsilon
  fun_prop

lemma fieldHeightEpsilon_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : fieldHeightEpsilon t = t := by
  exact (congrArg (max 0) (min_eq_left ht.2)).trans (max_eq_right ht.1)

def fieldRegularizedHeight (h : FieldStep) (t : ℝ) (i : Fin (h.depth + 1)) : ℝ :=
  h.height i + fieldHeightEpsilon t * (i.val + 1 : ℕ)

def fieldRegularized (h : FieldStep) (t : ℝ) : FieldStep :=
  fieldWithHeights h (fieldRegularizedHeight h t)
    (fun i => add_nonneg (h.nonneg i) (mul_nonneg (fieldHeightEpsilon_nonneg t) (Nat.cast_nonneg _)))
    (fun i j hij => add_le_add (h.ordered_height hij)
      (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.add_le_add_right hij 1)
        (fieldHeightEpsilon_nonneg t)))

lemma fieldRegularized_increment (h : FieldStep) (t : ℝ) (i : Fin (h.depth + 1)) :
    (fieldIncrement (fieldRegularized h t) i).2 =
      (fieldIncrement h i).2 + fieldHeightEpsilon t := by
  change fieldHeightIncrement (fieldRegularizedHeight h t) i =
    fieldHeightIncrement h.height i + fieldHeightEpsilon t
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [fieldHeightIncrement, fieldRegularizedHeight]
  · rw [fieldHeightIncrement_succ, fieldHeightIncrement_succ]
    simp only [fieldRegularizedHeight, Fin.val_succ, Fin.val_castSucc, Nat.cast_add,
      Nat.cast_one]
    ring

lemma fieldRegularized_strict (h : FieldStep) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1)
    (i : Fin (h.depth + 1)) : 0 < (fieldIncrement (fieldRegularized h t) i).2 := by
  rw [fieldRegularized_increment, fieldHeightEpsilon_eq ⟨ht.1.le, ht.2⟩]
  exact add_pos_of_nonneg_of_pos (fieldIncrement_nonneg h i) ht.1

lemma fieldRegularized_zero (h : FieldStep) : fieldRegularized h 0 = h := by
  have he : fieldRegularizedHeight h 0 = h.height := by
    funext i
    simp [fieldRegularizedHeight, fieldHeightEpsilon]
  unfold fieldRegularized fieldWithHeights
  congr 1

lemma fieldIncrement_le_last (h : FieldStep) (i : Fin (h.depth + 1)) :
    (fieldIncrement h i).2 ≤ h.height (Fin.last h.depth) := by
  have hh := h.ordered_height (Fin.le_last i)
  change h.height i - (if hi : i.val = 0 then 0 else h.height ⟨i.val - 1, by omega⟩) ≤ _
  split_ifs with hi
  · simpa only [sub_zero] using hh
  · exact (sub_le_self _ (h.nonneg _)).trans hh

def fieldRegularizedIncrements (h : FieldStep) : List (ℝ × (ℝ → ℝ≥0)) :=
  List.ofFn (fun i : Fin h.depth => ((fieldIncrement h i.succ).1,
    fun t => NNReal.mk ((fieldIncrement h i.succ).2 + fieldHeightEpsilon t)
      (add_nonneg (fieldIncrement_nonneg h i.succ) (fieldHeightEpsilon_nonneg t))))

lemma fieldRegularizedIncrements_positive (h : FieldStep) :
    ∀ av ∈ fieldRegularizedIncrements h, 0 < av.1 := by
  intro av hav
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hav
  exact fieldIncrement_tail_positive h i

lemma fieldRegularizedIncrements_continuous (h : FieldStep) :
    ∀ av ∈ fieldRegularizedIncrements h, Continuous av.2 := by
  intro av hav
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hav
  exact (continuous_const.add continuous_fieldHeightEpsilon).subtype_mk _

lemma fieldRegularizedIncrements_bound (h : FieldStep) :
    ∀ av ∈ fieldRegularizedIncrements h, ∀ t, (av.2 t : ℝ) ≤ h.height (Fin.last h.depth) + 1 := by
  intro av hav t
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hav
  exact add_le_add (fieldIncrement_le_last h i.succ) (fieldHeightEpsilon_le_one t)

lemma fieldRegularizedIncrements_eval (h : FieldStep) (t : ℝ) :
    (fieldRegularizedIncrements h).map (fun av => (av.1, av.2 t)) =
      scalarFieldIncrements (fieldRegularized h t) := by
  rw [fieldRegularizedIncrements, List.map_ofFn, scalarFieldIncrements]
  apply congrArg List.ofFn
  funext i
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact (fieldRegularized_increment h t i.succ).symm

end InvariantIsing

end

end OAI

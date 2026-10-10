import OAI.LinearAlgebra.MatrixMultiplication.FieldParameters.Weights

namespace OAI

/-! Fixed rational distributions and their entropy and capacity formulas. -/

namespace MatrixMultiplication.AllFieldParameters

open scoped BigOperators

theorem assigned_mem_or_zero {α : Type} [BEq α] (keys : List α) (data : List ℤ) (key : α) :
    assigned keys data key = 0 ∨ assigned keys data key ∈ data := by
  unfold assigned
  cases h : (keys.zip data).find? (fun e => e.1 == key) with
  | none => simp
  | some pair =>
    right
    exact (List.of_mem_zip (List.mem_of_find?_eq_some h)).2

theorem assigned_argument_bound {α : Type} [BEq α] (keys : List α) (data : List ℤ)
    (hd : ∀ n ∈ data, |n| ≤ 160000) (key : α) : |assigned keys data key| ≤ 160000 := by
  rcases assigned_mem_or_zero keys data key with h | h
  · rw [h]; norm_num
  · exact hd _ h

theorem splitWeight_positive (parents : List Shape) (data : List ℤ)
    (hd : ∀ n ∈ data, |n| ≤ 160000) (s u : Shape) :
    0 < splitWeight parents data s u := by
  apply Finset.prod_pos
  intro i _
  apply weight_positive_of_argument_bound
  exact assigned_argument_bound _ data hd _

theorem list_sum_map_nonnegative {α : Type} (xs : List α) (f : α → ℚ)
    (hf : ∀ x ∈ xs, 0 ≤ f x) : 0 ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_nonneg (hf x (by simp)) (ih (fun y hy => hf y (by simp [hy])))

theorem list_sum_map_positive {α : Type} (xs : List α) (f : α → ℚ)
    (hne : xs ≠ []) (hf : ∀ x ∈ xs, 0 < f x) : 0 < (xs.map f).sum := by
  cases xs with
  | nil => contradiction
  | cons x xs =>
    simp only [List.map_cons, List.sum_cons]
    exact add_pos_of_pos_of_nonneg (hf x (by simp))
      (list_sum_map_nonnegative xs f (fun y hy => (hf y (by simp [hy])).le))

theorem list_sum_map_div {α : Type} (xs : List α) (f : α → ℚ) (d : ℚ) :
    (xs.map (fun x => f x / d)).sum = (xs.map f).sum / d := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, add_div]

theorem splitLaw_positive (parents : List Shape) (data : List ℤ)
    (hd : ∀ n ∈ data, |n| ≤ 160000) (s u : Shape) (hu : u ∈ below s) :
    0 < splitLaw parents data s u := by
  rw [splitLaw, ite_eq_left hu]
  apply div_pos (splitWeight_positive parents data hd s u)
  apply list_sum_map_positive
  · intro he
    simp only [he, List.not_mem_nil] at hu
  · intro v _
    exact splitWeight_positive parents data hd s v

theorem splitLaw_normalized (parents : List Shape) (data : List ℤ)
    (hd : ∀ n ∈ data, |n| ≤ 160000) (s : Shape) (hne : below s ≠ []) :
    ((below s).map (splitLaw parents data s)).sum = 1 := by
  have he : (below s).map (splitLaw parents data s) =
      (below s).map (fun u => splitWeight parents data s u /
        ((below s).map (splitWeight parents data s)).sum) := by
    apply List.map_congr_left
    intro u hu
    simp only [splitLaw, hu, ite_true]
  rw [he, list_sum_map_div, div_self]
  exact ne_of_gt (list_sum_map_positive (below s) _ hne
    (fun u _ => splitWeight_positive parents data hd s u))

theorem stageA_table_arguments_bounded : ∀ n ∈ tableP, |n| ≤ 160000 := by decide +kernel

theorem stageB_table_arguments_bounded : ∀ n ∈ tablep, |n| ≤ 160000 := by decide +kernel

theorem zero_table_arguments_bounded : ∀ n ∈ tablez, |n| ≤ 160000 := by decide +kernel

theorem stageA_support_nonempty : ∀ s ∈ positiveInitial, below s ≠ [] := by decide +kernel

theorem stageB_support_nonempty : ∀ s ∈ positiveSecond, below s ≠ [] := by decide +kernel

theorem stageA_support_complement : ∀ s ∈ positiveInitial, ∀ u ∈ below s,
    complement s u ∈ below s ∧ ∀ i, u i ≤ s i := by decide +kernel

theorem stageB_support_complement : ∀ s ∈ positiveSecond, ∀ u ∈ below s,
    complement s u ∈ below s ∧ ∀ i, u i ≤ s i := by decide +kernel

theorem stageALaw_positive (s u : Shape) (hu : u ∈ below s) : 0 < stageALaw s u :=
  splitLaw_positive _ _ stageA_table_arguments_bounded s u hu

theorem stageBLaw_positive (s u : Shape) (hu : u ∈ below s) : 0 < stageBLaw s u :=
  splitLaw_positive _ _ stageB_table_arguments_bounded s u hu

theorem stageALaw_normalized (s : Shape) (hs : s ∈ positiveInitial) :
    ((below s).map (stageALaw s)).sum = 1 :=
  splitLaw_normalized _ _ stageA_table_arguments_bounded s (stageA_support_nonempty s hs)

theorem stageBLaw_normalized (s : Shape) (hs : s ∈ positiveSecond) :
    ((below s).map (stageBLaw s)).sum = 1 :=
  splitLaw_normalized _ _ stageB_table_arguments_bounded s (stageB_support_nonempty s hs)

theorem stageALaw_complement (s u : Shape) (hs : s ∈ positiveInitial) (hu : u ∈ below s) :
    stageALaw s (complement s u) = stageALaw s u := by
  obtain ⟨hc, hb⟩ := stageA_support_complement s hs u hu
  exact splitLaw_complement _ _ s u hb hu hc

theorem stageBLaw_complement (s u : Shape) (hs : s ∈ positiveSecond) (hu : u ∈ below s) :
    stageBLaw s (complement s u) = stageBLaw s u := by
  obtain ⟨hc, hb⟩ := stageB_support_complement s hs u hu
  exact splitLaw_complement _ _ s u hb hu hc

end MatrixMultiplication.AllFieldParameters

end OAI

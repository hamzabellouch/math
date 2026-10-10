import Mathlib
import OAI.LinearAlgebra.MatrixFields.Parameters.ParametersWeights

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

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

def initialMultiplicity (s : Shape) : ℕ :=
  if s 0 = s 1 ∧ s 1 = s 2 then 1 else if s 0 = s 1 ∨ s 1 = s 2 ∨ s 0 = s 2 then 3 else 6

def initialInteger (i : ℕ) : ℤ := assigned (List.range 17) tablea i

def initialWeight (s : Shape) : ℚ :=
  initialMultiplicity s * ∏ i : Fin 3, weight (initialInteger (s i))

def initialLaw (s : Shape) : ℚ :=
  if s ∈ sortedInitial then initialWeight s / (sortedInitial.map initialWeight).sum else 0

theorem initial_table_arguments_bounded : ∀ n ∈ tablea, |n| ≤ 160000 := by decide +kernel

theorem initialWeight_positive (s : Shape) : 0 < initialWeight s := by
  apply mul_pos
  · unfold initialMultiplicity
    split_ifs <;> norm_num
  · apply Finset.prod_pos
    intro i _
    apply weight_positive_of_argument_bound
    exact assigned_argument_bound _ tablea initial_table_arguments_bounded _

theorem initialLaw_positive (s : Shape) (hs : s ∈ sortedInitial) : 0 < initialLaw s := by
  rw [initialLaw, ite_eq_left hs]
  apply div_pos (initialWeight_positive s)
  exact list_sum_map_positive _ _ (by decide +kernel) (fun t _ => initialWeight_positive t)

theorem initialLaw_normalized : (sortedInitial.map initialLaw).sum = 1 := by
  have he : sortedInitial.map initialLaw = sortedInitial.map
      (fun s => initialWeight s / (sortedInitial.map initialWeight).sum) := by
    apply List.map_congr_left
    intro s hs
    simp only [initialLaw, hs, ite_true]
  rw [he, list_sum_map_div, div_self]
  exact ne_of_gt (list_sum_map_positive _ _ (by decide +kernel)
    (fun s _ => initialWeight_positive s))

theorem binary_table_bounds : ∀ n ∈ tabled, 0 ≤ n ∧ n ≤ 110106 := by decide +kernel

theorem binaryInteger_bounds (t u : Shape) :
    0 ≤ binaryInteger t u ∧ binaryInteger t u ≤ 110106 := by
  rcases assigned_mem_or_zero binaryKeys tabled (t, u) with h | h
  · change 0 ≤ assigned binaryKeys tabled (t, u) ∧ assigned binaryKeys tabled (t, u) ≤ 110106
    rw [h]
    norm_num
  · exact binary_table_bounds _ h

theorem binaryParameter_bounds (t u : Shape) :
    0 ≤ binaryParameter t u ∧ binaryParameter t u ≤ (110106 : ℚ) / 1000000 := by
  obtain ⟨hlo, hhi⟩ := binaryInteger_bounds t u
  have hl : (0 : ℚ) ≤ binaryInteger t u := by exact_mod_cast hlo
  have hh : (binaryInteger t u : ℚ) ≤ 110106 := by exact_mod_cast hhi
  unfold binaryParameter
  constructor
  · exact div_nonneg hl (by norm_num)
  · exact div_le_div_of_nonneg_right hh (by norm_num)

def singletonSlot (k : ℕ) : Fin 6 :=
  match k with
  | 0 => 0
  | 1 => 1
  | 3 => 4
  | 4 => 5
  | _ => 0

def littleLaw (t u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - binaryParameter t u else if i = 3 then binaryParameter t u else 0
  else if i = singletonSlot (u w) then 1 else 0

theorem littleLaw_nonnegative (t u : Shape) (w : Fin 3) (i : Fin 6) :
    0 ≤ littleLaw t u w i := by
  obtain ⟨hl, hh⟩ := binaryParameter_bounds t u
  unfold littleLaw
  split_ifs <;> linarith

theorem littleLaw_normalized (t u : Shape) (w : Fin 3) :
    ∑ i : Fin 6, littleLaw t u w i = 1 := by
  by_cases h : u w = 2
  · simp only [littleLaw, h, ite_true]
    calc
      _ = ∑ i : Fin 6, ((if i = 2 then 1 - binaryParameter t u else 0) +
          (if i = 3 then binaryParameter t u else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i = 2
        · subst i
          simp [show (2 : Fin 6) ≠ 3 by decide]
        · simp [hi]
      _ = 1 := by simp [Finset.sum_add_distrib]
  · simp [littleLaw, h]

theorem orderedPairWeight_positive (t : Shape) (i j : Fin 6) :
    0 < weight (orderedPairInteger t i j) := by
  apply weight_positive_of_argument_bound
  exact assigned_argument_bound _ tablez zero_table_arguments_bounded _

theorem orderedPairs_nonempty : ∀ t ∈ zeroSecond, orderedPairs t ≠ [] := by decide +kernel

theorem orderedPairs_support (t : Shape) (ij : PairSlot) (h : ij ∈ orderedPairs t) :
    statisticWeight ij.1 + statisticWeight ij.2 = shapeMax t := by
  simp only [orderedPairs, List.mem_flatMap, List.mem_filterMap] at h
  obtain ⟨i, _, j, _, he⟩ := h
  split_ifs at he with hs
  · cases Option.some.inj he
    exact hs

theorem zeroPairLaw_positive (t : Shape) (ht : t ∈ zeroSecond) (ij : PairSlot)
    (hij : ij ∈ orderedPairs t) : 0 < zeroPairLaw t ij.1 ij.2 := by
  rw [zeroPairLaw, ite_eq_left (orderedPairs_support t ij hij)]
  exact div_pos (orderedPairWeight_positive _ _ _)
    (list_sum_map_positive _ _ (orderedPairs_nonempty t ht)
      (fun p _ => orderedPairWeight_positive t p.1 p.2))

theorem zeroPairLaw_normalized (t : Shape) (ht : t ∈ zeroSecond) :
    ((orderedPairs t).map (fun ij => zeroPairLaw t ij.1 ij.2)).sum = 1 := by
  have he : (orderedPairs t).map (fun ij => zeroPairLaw t ij.1 ij.2) =
      (orderedPairs t).map (fun ij => weight (orderedPairInteger t ij.1 ij.2) /
        ((orderedPairs t).map (fun p => weight (orderedPairInteger t p.1 p.2))).sum) := by
    apply List.map_congr_left
    intro ij hij
    simp only [zeroPairLaw, orderedPairs_support t ij hij, ite_true]
  rw [he, list_sum_map_div, div_self]
  exact ne_of_gt (list_sum_map_positive _ _ (orderedPairs_nonempty t ht)
    (fun p _ => orderedPairWeight_positive t p.1 p.2))

end MatrixMultiplication.AllFieldParameters

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators

def stageCDistinguished (u : Shape) : Fin 3 :=
  if u 0 = 2 then 0 else if u 1 = 2 then 1 else 2

def stageCCanonicalAtom : Fin 4 → Shape :=
  (Matrix.vecCons (shape 1 1 0) (Matrix.vecCons (shape 0 0 2) (Matrix.vecCons (shape 1 0 1) (Matrix.vecCons (shape 0 1 1) Matrix.vecEmpty))))

def stageCAtom (u : Shape) (i : Fin 4) : Shape :=
  if stageCDistinguished u = 0 then
    shape (stageCCanonicalAtom i 2) (stageCCanonicalAtom i 1) (stageCCanonicalAtom i 0)
  else if stageCDistinguished u = 1 then
    shape (stageCCanonicalAtom i 0) (stageCCanonicalAtom i 2) (stageCCanonicalAtom i 1)
  else stageCCanonicalAtom i

def stageCWeight (t u : Shape) (i : Fin 4) : ℚ :=
  if i.val < 2 then binaryParameter t u / 2 else (1 - binaryParameter t u) / 2

theorem positive_four_shapes : ∀ u ∈ shapes 4, positive u = true →
    u = shape 1 1 2 ∨ u = shape 1 2 1 ∨ u = shape 2 1 1 := by
  decide +kernel

theorem stageCDistinguished_spec : ∀ u ∈ shapes 4, positive u = true →
    u (stageCDistinguished u) = 2 ∧
      ∀ i, u i = 2 → i = stageCDistinguished u := by
  decide +kernel

theorem stageC_children_length : ∀ u ∈ shapes 4, positive u = true →
    (below u).length = 4 := by
  decide +kernel

theorem stageC_children_geometry : ∀ u ∈ shapes 4, positive u = true →
    ∀ v ∈ below u,
      complement u v ∈ below u ∧
      (∀ i, v i ≤ u i) ∧
      (∃ i, v i = 0) ∧ (∃ i, complement u v i = 0) := by
  decide +kernel

theorem stageC_middle_complement : ∀ u ∈ shapes 4, positive u = true →
    ∀ v ∈ below u,
      (complement u v (stageCDistinguished u) = 1 ↔
        v (stageCDistinguished u) = 1) := by
  decide +kernel

theorem stageCAtom_injective : ∀ u ∈ shapes 4, positive u = true →
    Function.Injective (stageCAtom u) := by
  decide +kernel

theorem stageCAtom_mem : ∀ u ∈ shapes 4, positive u = true →
    ∀ i, stageCAtom u i ∈ below u := by
  decide +kernel

theorem stageCAtom_exhaustive : ∀ u ∈ shapes 4, positive u = true →
    ∀ v ∈ below u, ∃ i, stageCAtom u i = v := by
  decide +kernel

theorem stageCAtom_middle : ∀ u ∈ shapes 4, positive u = true →
    ∀ i, stageCAtom u i (stageCDistinguished u) = 1 ↔ ¬i.val < 2 := by
  decide +kernel

def stageCShapeWeight (d : ℚ) (u v : Shape) : ℚ :=
  if v ∈ below u then
    if v (stageCDistinguished u) = 1 then (1 - d) / 2 else d / 2
  else 0

def stageCLaw (t u v : Shape) : ℚ := stageCShapeWeight (binaryParameter t u) u v

theorem stageCLaw_source (t u v : Shape) :
    stageCLaw t u v =
      if v ∈ below u then
        if v (stageCDistinguished u) = 1 then
          (1 - binaryParameter t u) / 2 else binaryParameter t u / 2
      else 0 := rfl

theorem stageCLaw_nonnegative (t u v : Shape) : 0 ≤ stageCLaw t u v := by
  obtain ⟨hlo, hhi⟩ := binaryParameter_bounds t u
  unfold stageCLaw stageCShapeWeight
  split_ifs <;> linarith

theorem stageCWeight_nonnegative (t u : Shape) (i : Fin 4) :
    0 ≤ stageCWeight t u i := by
  obtain ⟨hlo, hhi⟩ := binaryParameter_bounds t u
  unfold stageCWeight
  split_ifs <;> linarith

theorem stageCWeight_normalized (t u : Shape) : ∑ i, stageCWeight t u i = 1 := by
  norm_num [stageCWeight, Fin.sum_univ_succ]; ring

theorem stageCWeight_single (t u : Shape) :
    stageCWeight t u 0 + stageCWeight t u 1 = binaryParameter t u := by
  change binaryParameter t u / 2 + binaryParameter t u / 2 = binaryParameter t u
  ring

theorem stageCWeight_cross (t u : Shape) :
    stageCWeight t u 2 + stageCWeight t u 3 = 1 - binaryParameter t u := by
  change (1 - binaryParameter t u) / 2 + (1 - binaryParameter t u) / 2 =
    1 - binaryParameter t u
  ring

theorem stageCLaw_atom (t u : Shape) (hu : u ∈ shapes 4)
    (hpos : positive u = true) (i : Fin 4) :
    stageCLaw t u (stageCAtom u i) = stageCWeight t u i := by
  simp only [stageCLaw, stageCShapeWeight, stageCAtom_mem u hu hpos i, ite_true,
    stageCAtom_middle u hu hpos i, ite_not, stageCWeight]

private theorem stageCShapeWeight_normalized (d : ℚ) (u : Shape)
    (hu : u ∈ shapes 4) (hpos : positive u = true) :
    ((shapes 2).map (stageCShapeWeight d u)).sum = 1 := by
  rcases positive_four_shapes u hu hpos with rfl | rfl | rfl <;>
    norm_num [stageCShapeWeight, stageCDistinguished, below, shapes, shape, List.range_succ,
      Matrix.cons_val_two, funext_iff, Fin.forall_fin_succ] <;> ring

private theorem stageCShapeWeight_normalized_below (d : ℚ) (u : Shape)
    (hu : u ∈ shapes 4) (hpos : positive u = true) :
    ((below u).map (stageCShapeWeight d u)).sum = 1 := by
  rcases positive_four_shapes u hu hpos with rfl | rfl | rfl <;>
    norm_num [stageCShapeWeight, stageCDistinguished, below, shapes, shape, List.range_succ,
      Matrix.cons_val_two, funext_iff, Fin.forall_fin_succ] <;> ring

theorem stageCLaw_normalized (t u : Shape)
    (hu : u ∈ shapes 4) (hpos : positive u = true) :
    ((shapes 2).map (stageCLaw t u)).sum = 1 :=
  stageCShapeWeight_normalized (binaryParameter t u) u hu hpos

theorem stageCLaw_normalized_below (t u : Shape)
    (hu : u ∈ shapes 4) (hpos : positive u = true) :
    ((below u).map (stageCLaw t u)).sum = 1 :=
  stageCShapeWeight_normalized_below (binaryParameter t u) u hu hpos

theorem stageCLaw_outside_support (t u v : Shape) (hv : v ∉ below u) :
    stageCLaw t u v = 0 := by
  simp only [stageCLaw, stageCShapeWeight, ite_eq_right hv]

theorem stageCLaw_support (t u v : Shape) (h : stageCLaw t u v ≠ 0) :
    v ∈ below u := by
  by_contra hv
  exact h (stageCLaw_outside_support t u v hv)

theorem stageCLaw_children_zero (t u v : Shape)
    (hu : u ∈ shapes 4) (hpos : positive u = true)
    (h : stageCLaw t u v ≠ 0) :
    (∃ i, v i = 0) ∧ (∃ i, complement u v i = 0) :=
  (stageC_children_geometry u hu hpos v (stageCLaw_support t u v h)).2.2

theorem stageCLaw_complement (t u v : Shape)
    (hu : u ∈ shapes 4) (hpos : positive u = true) (hv : v ∈ below u) :
    stageCLaw t u (complement u v) = stageCLaw t u v := by
  have hc := (stageC_children_geometry u hu hpos v hv).1
  have hm := stageC_middle_complement u hu hpos v hv
  simp only [stageCLaw, stageCShapeWeight, hv, hc, ite_true, hm]

end MatrixMultiplication.AllFieldHistory

end MatrixAllFields

end OAI

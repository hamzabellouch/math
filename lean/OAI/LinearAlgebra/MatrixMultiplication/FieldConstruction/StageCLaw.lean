import OAI.LinearAlgebra.MatrixMultiplication.FieldParameters.Distributions

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators

def stageCDistinguished (u : Shape) : Fin 3 :=
  if u 0 = 2 then 0 else if u 1 = 2 then 1 else 2

def stageCCanonicalAtom : Fin 4 → Shape :=
  ![shape 1 1 0, shape 0 0 2, shape 1 0 1, shape 0 1 1]

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
  norm_num [stageCWeight, Fin.sum_univ_succ]
  ring

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

end OAI

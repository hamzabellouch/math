import OAI.Combinatorics.EditDistance.WindowRecursion

namespace OAI

/-!
# Base finite-cut embedding for short words
-/

namespace EditUpper
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset EditDistortion EditWindow EditCutModel
variable {A : Type*} [Fintype A]

noncomputable def firstKey (x : List A) : Fin (Fintype.card (Option A)) :=
  Fintype.equivFin (Option A) (x[0]?)

noncomputable def base : Model (List A) where
  Index := Fin (Fintype.card (Option A))
  finiteIndex := inferInstance
  weight _ := 1
  nonneg _ := by norm_num
  cut i x := decide (firstKey x = i)

lemma base_distance (x y : List A) :
    (base (A := A)).dist x y = 2*EditCutHash.sep (x[0]?) (y[0]?) := by
  have hcuts (i : Fin (Fintype.card (Option A))) :
      sep (decide (firstKey x = i)) (decide (firstKey y = i)) =
        |EditCutHash.hit (firstKey x) i-EditCutHash.hit (firstKey y) i| := by
    by_cases hx : firstKey x = i <;> by_cases hy : firstKey y = i <;>
      simp [sep,EditCutHash.hit,hx,hy]
  change (∑ i, 1*sep (decide (firstKey x = i)) (decide (firstKey y = i))) = _
  simp_rw [one_mul,hcuts]
  rw [EditCutHash.hit_distance]
  congr 1
  have he : firstKey x = firstKey y ↔ x[0]? = y[0]? := (Fintype.equivFin (Option A)).injective.eq_iff
  by_cases hxy : x[0]? = y[0]? <;> simp only [EditCutHash.sep,he,hxy,ite_true,ite_false]

lemma base_le_two (x y : List A) : (base (A := A)).dist x y ≤ 2 := by
  rw [base_distance]
  have h := EditCutHash.sep_le_one (x[0]?) (y[0]?)
  linarith

omit [Fintype A] in
lemma first_eq_of_small (x y : List A) (hx : x.length ≤ 1) (hy : y.length ≤ 1)
    (he : x[0]? = y[0]?) : x = y := by
  cases x with
  | nil => cases y <;> simp_all
  | cons a x =>
    have hxn : x = [] := List.eq_nil_iff_length_eq_zero.mpr (by simp only [List.length_cons] at hx; omega)
    subst x
    cases y with
    | nil => simp at he
    | cons b y =>
      have hyn : y = [] := List.eq_nil_iff_length_eq_zero.mpr (by simp only [List.length_cons] at hy; omega)
      subst y
      simpa using he

lemma base_lower (x y : List A) (hx : x.length ≤ 1) (hy : y.length ≤ 1) :
    (indel x y : ℝ) ≤ (base (A := A)).dist x y := by
  by_cases he : x[0]? = y[0]?
  · have hxy := first_eq_of_small x y hx hy he
    subst y
    rw [Model.dist_self]
    norm_cast
    exact cost_le (.nil _)
  · rw [base_distance,EditCutHash.sep_eq_one he,mul_one]
    have hlen : indel x y ≤ x.length+y.length :=
      cost_le ((Script.to_nil (s := false) x).trans (Script.to_nil y).symm)
    exact_mod_cast (show indel x y ≤ 2 by omega)

lemma base_upper (x y : List A) : (base (A := A)).dist x y ≤ 2*(indel x y : ℝ) :=
  model_indel_lipschitz base (fun p q a => base_le_two (p++q) (p++a::q)) x y

end EditUpper

end OAI

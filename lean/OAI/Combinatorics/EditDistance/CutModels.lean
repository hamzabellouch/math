import OAI.Combinatorics.EditDistance.MeanHistograms

namespace OAI

/-!
# Finite weighted cuts and histogram lifts
-/

namespace EditCutModel

universe u v

attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset

noncomputable def sep (a b : Bool) : ℝ := if a = b then 0 else 1

structure Model (X : Type u) where
  Index : Type
  finiteIndex : Fintype Index
  weight : Index → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  cut : Index → X → Bool

attribute [instance] Model.finiteIndex

noncomputable def Model.dist {X : Type u} (M : Model X) (x y : X) : ℝ :=
  ∑ i, M.weight i * sep (M.cut i x) (M.cut i y)

lemma Model.dist_nonneg {X : Type u} (M : Model X) (x y : X) : 0 ≤ M.dist x y := by
  apply sum_nonneg
  intro i _
  apply mul_nonneg (M.nonneg i)
  unfold sep
  split <;> norm_num

@[simp] lemma Model.dist_self {X : Type u} (M : Model X) (x : X) : M.dist x x = 0 := by
  simp [Model.dist,sep]

lemma Model.dist_symm {X : Type u} (M : Model X) (x y : X) : M.dist x y = M.dist y x := by
  unfold Model.dist
  apply sum_congr rfl
  intro i _
  simp [sep,eq_comm]

lemma Model.dist_triangle {X : Type u} (M : Model X) (x y z : X) :
    M.dist x z ≤ M.dist x y+M.dist y z := by
  unfold Model.dist
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro i _
  rw [←mul_add]
  apply mul_le_mul_of_nonneg_left ?_ (M.nonneg i)
  cases M.cut i x <;> cases M.cut i y <;> cases M.cut i z <;> norm_num [sep]

noncomputable def Model.pullback {X : Type u} {Y : Type v} (M : Model X) (f : Y → X) : Model Y where
  Index := M.Index
  finiteIndex := M.finiteIndex
  weight := M.weight
  nonneg := M.nonneg
  cut i y := M.cut i (f y)

lemma Model.pullback_dist {X : Type u} {Y : Type v} (M : Model X) (f : Y → X) (x y : Y) :
    (M.pullback f).dist x y = M.dist (f x) (f y) := rfl

noncomputable def Model.scale {X : Type u} (M : Model X) (a : ℝ) (ha : 0 ≤ a) : Model X where
  Index := M.Index
  finiteIndex := M.finiteIndex
  weight i := a*M.weight i
  nonneg i := mul_nonneg ha (M.nonneg i)
  cut := M.cut

lemma Model.scale_dist {X : Type u} (M : Model X) (a : ℝ) (ha : 0 ≤ a) (x y : X) :
    (M.scale a ha).dist x y = a*M.dist x y := by
  simp only [Model.dist,Model.scale,mul_assoc,mul_sum]
  rfl

noncomputable def Model.total {X : Type u} {J : Type} [Fintype J] (M : J → Model X) : Model X where
  Index := (j : J) × (M j).Index
  finiteIndex := inferInstance
  weight i := (M i.1).weight i.2
  nonneg i := (M i.1).nonneg i.2
  cut i x := (M i.1).cut i.2 x

lemma Model.total_dist {X : Type u} {J : Type} [Fintype J] (M : J → Model X) (x y : X) :
    (Model.total M).dist x y = ∑ j, (M j).dist x y := by
  change (∑ i : (j : J) × (M j).Index, (M i.1).weight i.2 * sep ((M i.1).cut i.2 x) ((M i.1).cut i.2 y)) = _
  rw [Fintype.sum_sigma]
  rfl

lemma initial_cut_sum {s a : ℕ} (ha : a ≤ s) :
    (∑ t : Fin s, if t.val < a then (1 : ℝ) else 0) = (a : ℝ) := by
  simp only [sum_boole,Fin.card_filter_val_lt,min_eq_right ha]

theorem threshold_sum {s a b : ℕ} (ha : a ≤ s) (hb : b ≤ s) :
    (∑ t : Fin s, sep (decide (t.val < a)) (decide (t.val < b))) = |(a : ℝ)-(b : ℝ)| := by
  wlog hab : a ≤ b generalizing a b
  · rw [abs_sub_comm]
    calc
      _ = ∑ t : Fin s, sep (decide (t.val < b)) (decide (t.val < a)) := by
        apply sum_congr rfl
        intro t _
        simp only [sep,eq_comm]
      _ = _ := this hb ha (by omega)
  have he (t : Fin s) : sep (decide (t.val < a)) (decide (t.val < b)) =
      (if t.val < b then (1 : ℝ) else 0)-(if t.val < a then (1 : ℝ) else 0) := by
    by_cases hta : t.val < a <;> by_cases htb : t.val < b <;> simp [sep,hta,htb]; omega
  simp_rw [he]
  rw [sum_sub_distrib,initial_cut_sum hb,initial_cut_sum ha,abs_of_nonpos (sub_nonpos.mpr (Nat.cast_le.mpr hab))]
  ring

end EditCutModel

namespace EditCutModel
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset

noncomputable def countNat {J K : Type*} [Fintype J] (f : J → K) (z : K) : ℕ :=
  (univ.filter (fun j => f j = z)).card

lemma count_cast {J K : Type*} [Fintype J] (f : J → K) (z : K) :
    (countNat f z : ℝ) = EditCutHash.count f z := by
  simp only [countNat,EditCutHash.count,EditCutHash.hit,sum_boole]

lemma count_bound {J K : Type*} [Fintype J] (f : J → K) (z : K) :
    countNat f z ≤ Fintype.card J := card_filter_le _ _

noncomputable def Model.histogram {X : Type*} (M : Model X) (s : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    Model (Fin s → X) where
  Index := (M.Index → Bool) × (M.Index → Bool) × Fin s
  finiteIndex := inferInstance
  weight i := EditCutHash.probability M.weight a i.1
  nonneg i := EditCutHash.probability_nonneg M.nonneg ha i.1
  cut i f := decide (i.2.2.val < countNat (fun j : Fin s => EditCutHash.key M.cut i.1 (f j)) i.2.1)

lemma Model.histogram_dist {X : Type*} (M : Model X) (s : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (f g : Fin s → X) :
    (M.histogram s a ha).dist f g = EditCutHash.meanHistogram M.weight a M.cut f g := by
  change (∑ i : (M.Index → Bool) × (M.Index → Bool) × Fin s,
    EditCutHash.probability M.weight a i.1 * sep
      (decide (i.2.2.val < countNat (fun j : Fin s => EditCutHash.key M.cut i.1 (f j)) i.2.1))
      (decide (i.2.2.val < countNat (fun j : Fin s => EditCutHash.key M.cut i.1 (g j)) i.2.1))) = _
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro h _
  rw [Fintype.sum_prod_type]
  simp_rw [←mul_sum]
  congr 1
  apply sum_congr rfl
  intro z _
  rw [threshold_sum (by simpa using count_bound (fun j => EditCutHash.key M.cut h (f j)) z)
    (by simpa using count_bound (fun j => EditCutHash.key M.cut h (g j)) z),count_cast,count_cast]

lemma Model.distance_eq {X : Type*} (M : Model X) (x y : X) :
    EditCutHash.distance M.weight M.cut x y = M.dist x y := by
  unfold EditCutHash.distance Model.dist
  apply sum_congr rfl
  intro i _
  congr 1
  cases M.cut i x <;> cases M.cut i y <;> norm_num [sep,EditCutHash.sep]

end EditCutModel

end OAI

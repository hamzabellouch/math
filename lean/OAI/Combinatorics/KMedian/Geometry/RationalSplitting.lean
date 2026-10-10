import Mathlib
import OAI.Combinatorics.KMedian.Geometry.RationalIntervals

namespace OAI

section
section
namespace MetricKMedian.Preparation.RationalSplitting
open Finset RationalIntervals
variable {I J : Type} [Fintype I] [Fintype J]

def cuts (y : I → ℚ) (x : J → I → ℚ) (i : I) : Finset ℚ :=
  (insert (y i) (univ.image (fun j => x j i))).filter (fun q => 0 < q)

abbrev Piece (y : I → ℚ) (x : J → I → ℚ) := Σ i, ↥(cuts y x i)

def weight (y : I → ℚ) (x : J → I → ℚ) (a : Piece y x) : ℚ :=
  length (cuts y x a.1) a.2.val

def assignment (y : I → ℚ) (x : J → I → ℚ) (j : J) : Finset (Piece y x) :=
  univ.filter (fun a => a.2.val ≤ x j a.1)

omit [Fintype I] in
theorem cuts_pos (y : I → ℚ) (x : J → I → ℚ) (i : I) :
    ∀ q ∈ cuts y x i, 0 < q := fun _ h => (mem_filter.mp h).2

omit [Fintype I] in
theorem cuts_le (y : I → ℚ) (x : J → I → ℚ) (hx : ∀ j i, x j i ≤ y i)
    (i : I) : ∀ q ∈ cuts y x i, q ≤ y i := by
  intro q hq
  rcases mem_insert.mp (mem_filter.mp hq).1 with rfl | hq
  · exact le_rfl
  · obtain ⟨j,_,rfl⟩ := mem_image.mp hq
    exact hx j i

omit [Fintype I] in
theorem weight_pos (y : I → ℚ) (x : J → I → ℚ) (a : Piece y x) : 0 < weight y x a :=
  length_pos _ (cuts_pos y x a.1 _ a.2.property)

omit [Fintype I] in
theorem weight_le (y : I → ℚ) (x : J → I → ℚ) (hx : ∀ j i, x j i ≤ y i)
    (a : Piece y x) : weight y x a ≤ y a.1 :=
  (length_le _ _).trans (cuts_le y x hx a.1 _ a.2.property)

omit [Fintype I] in
theorem sum_fiber (y : I → ℚ) (x : J → I → ℚ) (hy : ∀ i, 0 < y i)
    (hx : ∀ j i, x j i ≤ y i) (i : I) :
    (∑ q : ↥(cuts y x i), length (cuts y x i) q.val)=y i := by
  rw [sum_coe_sort,sum_lengths _ (cuts_pos y x i)]
  exact height_eq _ (y i) (mem_filter.mpr ⟨mem_insert_self _ _,hy i⟩) (hy i).le (cuts_le y x hx i)

theorem sum_weight (y : I → ℚ) (x : J → I → ℚ) (hy : ∀ i, 0 < y i)
    (hx : ∀ j i, x j i ≤ y i) : (∑ a, weight y x a)=∑ i, y i := by
  rw [Fintype.sum_sigma]
  exact sum_congr rfl (fun i _ => sum_fiber y x hy hx i)

omit [Fintype I] in
theorem assigned_fiber (y : I → ℚ) (x : J → I → ℚ) (hx0 : ∀ j i, 0 ≤ x j i)
    (j : J) (i : I) :
    (∑ q : ↥(cuts y x i), if q.val ≤ x j i then length (cuts y x i) q.val else 0)=x j i := by
  change (∑ q : ↥(cuts y x i), (fun q : ℚ => if q ≤ x j i then length (cuts y x i) q else 0) q.val)=x j i
  rw [sum_coe_sort (cuts y x i) (fun q : ℚ => if q ≤ x j i then length (cuts y x i) q else 0),← sum_filter]
  apply prefix_sum _ (cuts_pos y x i)
  by_cases hz : x j i=0
  · exact Or.inl hz
  · exact Or.inr (mem_filter.mpr ⟨mem_insert_of_mem (mem_image.mpr ⟨j,mem_univ _,rfl⟩),
      lt_of_le_of_ne (hx0 j i) (Ne.symm hz)⟩)

theorem sum_assignment (y : I → ℚ) (x : J → I → ℚ) (hx0 : ∀ j i, 0 ≤ x j i)
    (j : J) : (∑ a ∈ assignment y x j, weight y x a)=∑ i, x j i := by
  rw [assignment,sum_filter,Fintype.sum_sigma]
  exact sum_congr rfl (fun i _ => assigned_fiber y x hx0 j i)

theorem card_pieces (y : I → ℚ) (x : J → I → ℚ) :
    Fintype.card (Piece y x) ≤ Fintype.card I*(Fintype.card J+1) := by
  have hc : ∀ i, (cuts y x i).card ≤ Fintype.card J+1 := by
    intro i
    exact (card_filter_le _ _).trans ((card_insert_le _ _).trans
      (Nat.add_le_add_right ((card_image_le).trans_eq (card_univ)) 1))
  rw [Fintype.card_sigma]
  simp only [Fintype.card_coe]
  calc
    _ ≤ ∑ _i : I, (Fintype.card J+1) := sum_le_sum (fun i _ => hc i)
    _ = _ := by simp

theorem cost_assignment (y : I → ℚ) (x : J → I → ℚ) (hx0 : ∀ j i, 0 ≤ x j i)
    (j : J) (d : I → ℝ) :
    (∑ a ∈ assignment y x j, (weight y x a:ℝ)*d a.1)=∑ i, (x j i:ℝ)*d i := by
  rw [assignment,sum_filter,Fintype.sum_sigma]
  apply sum_congr rfl
  intro i _
  have he : (∑ q : ↥(cuts y x i), if q.val ≤ x j i then (length (cuts y x i) q.val:ℝ) else 0)=(x j i:ℝ) := by
    have hh := congrArg (fun q : ℚ => (q:ℝ)) (assigned_fiber y x hx0 j i)
    push_cast at hh
    simpa only [apply_ite, Rat.cast_zero] using hh
  calc
    _ = (∑ q : ↥(cuts y x i), if q.val ≤ x j i then (length (cuts y x i) q.val:ℝ) else 0)*d i := by
      rw [sum_mul]
      apply sum_congr rfl
      intro q _
      split_ifs <;> simp only [weight,zero_mul]
    _ = _ := by rw [he]

theorem nearest_assignment (y : I → ℚ) (x : J → I → ℚ) (hx : ∀ j i, x j i ≤ y i)
    (d : J → I → ℝ)
    (horder : ∀ j i b, 0 < x j i → x j b < y b → d j i ≤ d j b)
    (j : J) (a : Piece y x) (ha : a ∈ assignment y x j)
    (b : Piece y x) (hb : b ∉ assignment y x j) : d j a.1 ≤ d j b.1 := by
  have ha' : a.2.val ≤ x j a.1 := (mem_filter.mp ha).2
  have hb' : x j b.1 < b.2.val := lt_of_not_ge (fun h => hb (mem_filter.mpr ⟨mem_univ _,h⟩))
  exact horder j a.1 b.1 ((cuts_pos y x a.1 _ a.2.property).trans_le ha')
    (hb'.trans_le (cuts_le y x hx b.1 _ b.2.property))

end MetricKMedian.Preparation.RationalSplitting
end
end

end OAI

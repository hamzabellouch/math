import OAI.MeasureTheory.Falconer.Incidence.GridCount
import Mathlib.Algebra.Order.Round

namespace OAI

/-! # Integer rectangles arising from projected tube covers -/

namespace Falconer

theorem integer_near_real_bounds (z : ℤ) (x r : ℝ) (L : ℕ)
    (hz : |(z:ℝ)-x| ≤ r) (hL : r+1/2 ≤ (L:ℝ)) :
    round x-(L:ℤ) ≤ z ∧ z ≤ round x+(L:ℤ) := by
  have hh : |(z:ℝ)-(round x:ℝ)| ≤ (L:ℝ) :=
    ((abs_sub_le (z:ℝ) x (round x:ℝ)).trans
      (add_le_add hz (abs_sub_round x))).trans hL
  have hi : |z-round x| ≤ (L:ℤ) := by exact_mod_cast hh
  have h := abs_le.mp hi
  constructor <;> omega

theorem integer_rectangle_card (T : Finset (ℤ × ℤ)) (x y r : ℝ) (L : ℕ)
    (hL : r+1/2 ≤ (L:ℝ))
    (hT : ∀ z ∈ T, |(z.1:ℝ)-x| ≤ r ∧ |(z.2:ℝ)-y| ≤ r) :
    T.card ≤ (2*L+1)^2 := by
  have hsub : T ⊆
      (Finset.Icc (round x-(L:ℤ)) (round x+(L:ℤ))).product
        (Finset.Icc (round y-(L:ℤ)) (round y+(L:ℤ))) := by
    intro z hz
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr (integer_near_real_bounds z.1 x r L (hT z hz).1 hL),
        Finset.mem_Icc.mpr (integer_near_real_bounds z.2 y r L (hT z hz).2 hL)⟩
  have hx : (Finset.Icc (round x-(L:ℤ)) (round x+(L:ℤ))).card = 2*L+1 := by
    rw [Int.card_Icc]
    omega
  have hy : (Finset.Icc (round y-(L:ℤ)) (round y+(L:ℤ))).card = 2*L+1 := by
    rw [Int.card_Icc]
    omega
  exact (Finset.card_le_card hsub).trans_eq (by
    rw [Finset.product_eq_sprod,Finset.card_product,hx,hy,pow_two])

theorem integer_rectangle_cover_card {ι : Type*} [DecidableEq ι]
    (T : Finset (ℤ × ℤ)) (A : Finset ι) (x y : ι → ℝ) (r : ℝ) (L : ℕ)
    (hL : r+1/2 ≤ (L:ℝ))
    (hcover : ∀ z ∈ T, ∃ a ∈ A, |(z.1:ℝ)-x a| ≤ r ∧ |(z.2:ℝ)-y a| ≤ r) :
    T.card ≤ A.card*(2*L+1)^2 := by
  classical
  let F : ι → Finset (ℤ × ℤ) := fun a =>
    T.filter (fun z => |(z.1:ℝ)-x a| ≤ r ∧ |(z.2:ℝ)-y a| ≤ r)
  have hsub : T ⊆ A.biUnion F := by
    intro z hz
    obtain ⟨a,ha,hza⟩ := hcover z hz
    exact Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_filter.mpr ⟨hz,hza⟩⟩
  calc
    _ ≤ (A.biUnion F).card := Finset.card_le_card hsub
    _ ≤ ∑ a ∈ A, (F a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ A, (2*L+1)^2 := Finset.sum_le_sum (fun a _ =>
      integer_rectangle_card (F a) (x a) (y a) r L hL
        (fun z hz => (Finset.mem_filter.mp hz).2))
    _ = _ := by simp

end Falconer

end OAI

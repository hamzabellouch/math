import OAI.MeasureTheory.Falconer.Geometry.ProjectionCells
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace OAI

/-! Finite collision energy of the actual quantized projections. The
Cauchy--Schwarz lower bound and its geometric interpretation are used in
the scalar projection argument. -/
namespace Falconer

noncomputable def cellCollisions {α : Type*} (S : Finset α) (f : α → ℤ) : Finset (α × α) :=
  (S ×ˢ S).filter fun p => f p.1 = f p.2

theorem cellCollisions_card {α : Type*} (S : Finset α) (f : α → ℤ) :
    (cellCollisions S f).card = ∑ k ∈ S.image f, ((S.filter fun x => f x = k).card)^2 := by
  have hmap : Set.MapsTo (fun p : α × α => f p.1)
      (cellCollisions S f : Set (α × α)) (S.image f : Set ℤ) := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p.1,(Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1,rfl⟩
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro k _
  have he : ((cellCollisions S f).filter fun p => f p.1 = k) =
      (S.filter fun x => f x = k) ×ˢ (S.filter fun x => f x = k) := by
    ext ⟨x,y⟩
    simp only [cellCollisions,Finset.mem_filter,Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨hx,hy⟩,hxy⟩,hxk⟩
      exact ⟨⟨hx,hxk⟩,hy,hxy.symm.trans hxk⟩
    · rintro ⟨⟨hx,hxk⟩,hy,hyk⟩
      exact ⟨⟨⟨hx,hy⟩,hxk.trans hyk.symm⟩,hxk⟩
  rw [he,Finset.card_product,pow_two]

theorem finite_cell_energy_lower {α : Type*} (S : Finset α) (f : α → ℤ) :
    (S.card : ℝ)^2 ≤ ((S.image f).card : ℝ)*(cellCollisions S f).card := by
  have hc : (S.card : ℝ) = ∑ k ∈ S.image f, ((S.filter fun x => f x = k).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image f S
  rw [hc]
  have hb := Finset.sum_mul_sq_le_sq_mul_sq (S.image f)
    (fun _ => (1 : ℝ)) (fun k => ((S.filter fun x => f x = k).card : ℝ))
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hb
  have he : ((cellCollisions S f).card : ℝ) =
      ∑ k ∈ S.image f, ((S.filter fun x => f x = k).card : ℝ)^2 := by
    exact_mod_cast cellCollisions_card S f
  rw [he]
  exact hb

theorem same_projection_cell_near {δ y : ℝ} (hδ : 0 < δ) {l m : Space 2}
    (hcell : ⌊lineParameterProjection y l/δ⌋ = ⌊lineParameterProjection y m/δ⌋) :
    |lineParameterProjection y l-lineParameterProjection y m| ≤ δ := by
  have hl0 := Int.floor_le (lineParameterProjection y l/δ)
  have hl1 := Int.lt_floor_add_one (lineParameterProjection y l/δ)
  have hm0 := Int.floor_le (lineParameterProjection y m/δ)
  have hm1 := Int.lt_floor_add_one (lineParameterProjection y m/δ)
  rw [hcell] at hl0 hl1
  have hd : |lineParameterProjection y l/δ-lineParameterProjection y m/δ| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  rw [← sub_div,abs_div,abs_of_pos hδ] at hd
  exact (div_le_one hδ).1 hd

theorem projection_energy_lower {δ y : ℝ} (hδ : 0 < δ) (S : Finset (Space 2)) :
    (S.card : ℝ)^2 ≤ ((projectionCells δ y S).card : ℝ)*
      (((S ×ˢ S).filter fun p =>
        |lineParameterProjection y p.1-lineParameterProjection y p.2| ≤ δ).card : ℝ) := by
  classical
  have hb := finite_cell_energy_lower S (fun l => ⌊lineParameterProjection y l/δ⌋)
  have hsub : cellCollisions S (fun l => ⌊lineParameterProjection y l/δ⌋) ⊆
      (S ×ˢ S).filter (fun p =>
        |lineParameterProjection y p.1-lineParameterProjection y p.2| ≤ δ) := by
    intro p hp
    obtain ⟨hpS,hpc⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hpS,same_projection_cell_near hδ hpc⟩
  exact hb.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_le_card hsub))
    (Nat.cast_nonneg _))

end Falconer

end OAI

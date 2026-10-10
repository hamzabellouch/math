import OAI.MeasureTheory.Falconer.Graphs.NearGraph
import OAI.MeasureTheory.Falconer.Estimates.RegularizedCellCounts
import OAI.MeasureTheory.Falconer.Geometry.FarCellGeometry

namespace OAI

/-! # Only a dimensional number of partners at a comparable far depth -/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

private theorem card_filtered_pairs_le {α : Type*} [DecidableEq α]
    (S : Finset α) (G : α → α → Prop) [DecidableRel G] (D : ℕ)
    (hD : ∀ x ∈ S, (S.filter (G x)).card ≤ D) :
    ((S ×ˢ S).filter (fun z => G z.1 z.2)).card ≤ S.card*D := by
  have hsub : (S ×ˢ S).filter (fun z => G z.1 z.2) ⊆
      S.biUnion (fun x => (S.filter (G x)).image (fun y => (x,y))) := by
    intro z hz
    obtain ⟨hz,hG⟩ := Finset.mem_filter.mp hz
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hz
    exact Finset.mem_biUnion.mpr ⟨z.1,hx,Finset.mem_image.mpr
      ⟨z.2,Finset.mem_filter.mpr ⟨hy,hG⟩,rfl⟩⟩
  calc
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ x ∈ S, ((S.filter (G x)).image (fun y => (x,y))).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ S, D := Finset.sum_le_sum (fun x hx =>
      Finset.card_image_le.trans (hD x hx))
    _ = _ := by simp

noncomputable def farCellPartners {d : ℕ} (P : DyadicCube d) (ρ : Measure (Space d))
    (n : ℕ) : Finset (List (Fin d → Bool) × List (Fin d → Bool)) :=
  (P.occupiedPaths ρ n ×ˢ P.occupiedPaths ρ n).filter (fun z =>
    125*((d:ℝ)+1)*P.side/(2:ℝ)^n ≤ ‖(P.descendant z.2).center-(P.descendant z.1).center‖ ∧
    ‖(P.descendant z.2).center-(P.descendant z.1).center‖ ≤
      1100*((d:ℝ)+1)*P.side/(2:ℝ)^n)

theorem farCellPartners_card {d : ℕ} (P : DyadicCube d) (hP : 0 < P.side)
    (ρ : Measure (Space d)) (n : ℕ) :
    (farCellPartners P ρ n).card ≤
      (P.occupiedPaths ρ n).card*(2*(1100*(d+1))+1)^d := by
  let S := P.occupiedPaths ρ n
  have hsub : farCellPartners P ρ n ⊆ (S ×ˢ S).filter (fun z =>
      ‖(P.descendant z.2).center-(P.descendant z.1).center‖ ≤
        1100*((d:ℝ)+1)*P.side/(2:ℝ)^n) := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,(Finset.mem_filter.mp hz).2.2⟩
  apply (Finset.card_le_card hsub).trans
  apply card_filtered_pairs_le (P.occupiedPaths ρ n) (fun x y =>
    ‖(P.descendant y).center-(P.descendant x).center‖ ≤
      1100*((d:ℝ)+1)*P.side/(2:ℝ)^n)
  intro x hx
  apply P.neighbor_card hP _
    (fun p hp => (mem_cubePaths d n p).mp (Finset.mem_filter.mp hp).1) x
    ((mem_cubePaths d n x).mp (Finset.mem_filter.mp hx).1)
  have he : (1100*((d:ℝ)+1)*P.side/(2:ℝ)^n)*((2:ℝ)^n/P.side) =
      (1100*(d+1):ℕ) := by
    push_cast
    field_simp
  exact he.le

theorem farCellPartners_pair_card {d : ℕ} (P Q : DyadicCube d)
    (hP : 0 < P.side) (hQ : 0 < Q.side) (μ ν : Measure (Space d)) (n : ℕ) :
    ((farCellPartners P μ n) ×ˢ (farCellPartners Q ν n)).card ≤
      (2*(1100*(d+1))+1)^(2*d)*
        (P.occupiedPaths μ n ×ˢ Q.occupiedPaths ν n).card := by
  rw [Finset.card_product,Finset.card_product]
  apply (Nat.mul_le_mul (farCellPartners_card P hP μ n) (farCellPartners_card Q hQ ν n)).trans_eq
  rw [Nat.mul_comm 2 d, pow_mul, pow_two]
  ring

theorem farCellPartners_of_comparable_points {d : ℕ} (P : DyadicCube d)
    (hP : 0 < P.side) (ρ : Measure (Space d)) (n : ℕ)
    (u : List (Fin d → Bool) × List (Fin d → Bool))
    (hu : u ∈ P.occupiedPaths ρ n ×ˢ P.occupiedPaths ρ n)
    {x y : Space d} (hx : x ∈ (P.descendant u.1).carrier)
    (hy : y ∈ (P.descendant u.2).carrier)
    (hlo : 256*((d:ℝ)+1)*(P.side/(2:ℝ)^n) < dist x y)
    (hhi : dist x y ≤ 1024*((d:ℝ)+1)*(P.side/(2:ℝ)^n)) :
    u ∈ farCellPartners P ρ n := by
  have hu₁ := (mem_cubePaths d n u.1).mp
    (Finset.mem_filter.mp (Finset.mem_product.mp hu).1).1
  have hu₂ := (mem_cubePaths d n u.2).mp
    (Finset.mem_filter.mp (Finset.mem_product.mp hu).2).1
  have hs₁ : (P.descendant u.1).side = P.side/(2:ℝ)^n := by
    rw [P.descendant_side,hu₁]
  have hs₂ : (P.descendant u.2).side = P.side/(2:ℝ)^n := by
    rw [P.descendant_side,hu₂]
  have hb := ((P.descendant u.1).comparable_points_separate_cells (P.descendant u.2)
    (P.descendant_side_pos hP _) (P.descendant_side_pos hP _) hs₁.le hs₂.le hx hy hlo hhi)
  apply Finset.mem_filter.mpr
  refine ⟨hu,?_,?_⟩
  · have hs : 0 < P.side/(2:ℝ)^n := by positivity
    rw [dist_eq_norm,norm_sub_rev] at hb
    have hdim : 0 < ((d:ℝ)+1)*(P.side/(2:ℝ)^n) := by positivity
    calc
      _ = 125*((d:ℝ)+1)*(P.side/(2:ℝ)^n) := by ring
      _ ≤ _ := by nlinarith [hb.1]
  · rw [dist_eq_norm,norm_sub_rev] at hb
    exact hb.2.trans_eq (by ring)

end Falconer

end OAI

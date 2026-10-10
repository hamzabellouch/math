import OAI.MeasureTheory.Falconer.Geometry.PointBallCounts
import OAI.MeasureTheory.Falconer.Estimates.CoarsePlanarRounding

namespace OAI

/-! Original dyadic prefix counts bound the common coarse-grid cover.
Each occupied prefix cell contributes at most 49 rounded grid points. -/
namespace Falconer
open Set Regularization
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem finite_prefix_coarse_cover {N n : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (Q : DyadicCube 2) (hQ : 0 < Q.side)
    (P : Finset (Space 2)) (l : Space 2 → CellPath 2)
    (hleaf : ∀ x ∈ P, l x ∈ cubePaths 2 N ∧ x ∈ (Q.descendant (l x)).carrier)
    (hn : n ≤ N) (hscale : Q.side/(2:ℝ)^n ≤ ρ) :
    ((P.image (coarsePlanarRound ρ)).card:ℝ) ≤
      49*(((P.image l).image (List.take n)).card:ℝ) := by
  let C := (P.image l).image (List.take n)
  let S := fun p => (pointPrefixFiber P l n p).image (coarsePlanarRound ρ)
  have hsqrt : Real.sqrt (2:ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg (2:ℝ)]
  have hS (p : CellPath 2) (hp : p ∈ C) : ((S p).card:ℝ) ≤ 49 := by
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp hp
    obtain ⟨x,hx,hbx⟩ := Finset.mem_image.mp hb
    have hlen : p.length = n := by
      rw [← he,← hbx,List.length_take,(mem_cubePaths _ _ _).mp (hleaf x hx).1,Nat.min_eq_left hn]
    have hside : (Q.descendant p).side = Q.side/(2:ℝ)^n := by rw [Q.descendant_side,hlen]
    have hwithin : ∀ z ∈ S p, dist z (Q.descendant p).center ≤ 3*ρ := by
      intro z hz
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hyP,hyp⟩ := Finset.mem_filter.mp hy
      have hycell := descendant_subset_take Q hQ (l y) n (hleaf y hyP).2
      rw [hyp] at hycell
      have hd := (Q.descendant p).dist_le (Q.descendant_side_pos hQ p).le hycell
        ((Q.descendant p).center_mem (Q.descendant_side_pos hQ p))
      rw [hside] at hd
      have hd' : dist y (Q.descendant p).center ≤ 2*ρ := hd.trans
        ((mul_le_mul_of_nonneg_right hsqrt (by positivity)).trans
          (mul_le_mul_of_nonneg_left hscale (by norm_num)))
      exact (dist_triangle (coarsePlanarRound ρ y) y (Q.descendant p).center).trans
        ((add_le_add (by simpa only [dist_comm] using coarsePlanarRound_near hρ y) hd').trans_eq (by ring))
    have hsep : FiniteSeparatedAt ρ (S p) := finiteSeparatedAt_subset
      (Finset.image_subset_image (Finset.filter_subset _ _)) (coarsePlanarRound_separated hρ P)
    have hh := separated_ball_card (S p) (Q.descendant p).center hρ
      (r := 3*ρ) (by positivity) hsep hwithin
    have heq : (2*(3*ρ)/ρ+1)^2 = (49:ℝ) := by field_simp; ring
    rwa [heq] at hh
  have hcover : P.image (coarsePlanarRound ρ) ⊆ C.biUnion S := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    refine Finset.mem_biUnion.mpr ⟨(l x).take n,?_,?_⟩
    · exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hx)
    · exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hx,rfl⟩)
  calc
    _ ≤ ((C.biUnion S).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hcover)
    _ ≤ ∑ p ∈ C, ((S p).card:ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ C, (49:ℝ) := Finset.sum_le_sum hS
    _ = _ := by simp; ring

end Falconer

end OAI

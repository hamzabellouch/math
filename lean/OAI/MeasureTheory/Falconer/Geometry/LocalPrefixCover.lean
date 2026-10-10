import OAI.MeasureTheory.Falconer.Geometry.FinitePrefixCover
import OAI.MeasureTheory.Falconer.Estimates.LocalPacketRegularity

namespace OAI

/-! Prefix covers in the exact local chart used by scale combination. -/
namespace Falconer
open Set Regularization
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem finite_local_prefix_coarse_cover {N n : ℕ} {ρ Δ : ℝ}
    (hρ : 0 < ρ) (hΔ : 0 < Δ) (y a : ℝ)
    (Q : DyadicCube 2) (hQ : 0 < Q.side)
    (P : Finset (Space 2)) (l : Space 2 → CellPath 2)
    (hleaf : ∀ x ∈ P, l x ∈ cubePaths 2 N ∧ x ∈ (Q.descendant (l x)).carrier)
    (hn : n ≤ N) (hscale : (Q.side/(2:ℝ)^n)/Δ ≤ ρ) :
    (((P.image (localPacketPoint Δ y a)).image (coarsePlanarRound ρ)).card:ℝ) ≤
      49*(((P.image l).image (List.take n)).card:ℝ) := by
  let F := localPacketPoint Δ y a
  let R := fun x => coarsePlanarRound ρ (F x)
  let C := (P.image l).image (List.take n)
  let S := fun p => (pointPrefixFiber P l n p).image R
  have hsqrt : Real.sqrt (2:ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg (2:ℝ)]
  have hS (p : CellPath 2) (hp : p ∈ C) : ((S p).card:ℝ) ≤ 49 := by
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp hp
    obtain ⟨x,hx,hbx⟩ := Finset.mem_image.mp hb
    have hlen : p.length = n := by
      rw [← he,← hbx,List.length_take,(mem_cubePaths _ _ _).mp (hleaf x hx).1,Nat.min_eq_left hn]
    have hside : (Q.descendant p).side = Q.side/(2:ℝ)^n := by rw [Q.descendant_side,hlen]
    have hwithin : ∀ z ∈ S p, dist z (F (Q.descendant p).center) ≤ 3*ρ := by
      intro z hz
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hvP,hvp⟩ := Finset.mem_filter.mp hv
      have hvcell := descendant_subset_take Q hQ (l v) n (hleaf v hvP).2
      rw [hvp] at hvcell
      have hd := (Q.descendant p).dist_le (Q.descendant_side_pos hQ p).le hvcell
        ((Q.descendant p).center_mem (Q.descendant_side_pos hQ p))
      rw [hside] at hd
      have hdf : dist (F v) (F (Q.descendant p).center) ≤ 2*ρ := by
        rw [localPacketPoint_dist hΔ]
        calc
          _ ≤ (Real.sqrt 2*(Q.side/(2:ℝ)^n))/Δ := (div_le_div_iff_of_pos_right hΔ).2 hd
          _ = Real.sqrt 2*((Q.side/(2:ℝ)^n)/Δ) := by ring
          _ ≤ 2*ρ := mul_le_mul hsqrt hscale (by positivity) (by norm_num)
      exact (dist_triangle (R v) (F v) (F (Q.descendant p).center)).trans
        ((add_le_add (by simpa only [dist_comm] using coarsePlanarRound_near hρ (F v)) hdf).trans_eq (by ring))
    have hsep : FiniteSeparatedAt ρ (S p) := by
      have hh := coarsePlanarRound_separated hρ (P.image F)
      apply finiteSeparatedAt_subset (P := (P.image F).image (coarsePlanarRound ρ)) _ hh
      intro z hz
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem F (Finset.mem_filter.mp hv).1)
    have hh := separated_ball_card (S p) (F (Q.descendant p).center) hρ
      (r := 3*ρ) (by positivity) hsep hwithin
    have heq : (2*(3*ρ)/ρ+1)^2 = (49:ℝ) := by field_simp; ring
    rwa [heq] at hh
  have hcover : P.image R ⊆ C.biUnion S := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_biUnion.mpr ⟨(l x).take n,
      Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hx),
      Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hx,rfl⟩)⟩
  change (((P.image F).image (coarsePlanarRound ρ)).card:ℝ) ≤ _
  rw [Finset.image_image]
  calc
    _ ≤ ((C.biUnion S).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hcover)
    _ ≤ ∑ p ∈ C, ((S p).card:ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ C, (49:ℝ) := Finset.sum_le_sum hS
    _ = _ := by simp; ring

theorem pointPrefixFiber_image_children (P : Finset (Space 2)) (l : Space 2 → CellPath 2)
    (a b : ℕ) (p : CellPath 2) :
    ((pointPrefixFiber P l a p).image l).image (List.take b) =
      prefixChildren (P.image l) a b p := by
  rw [prefixChildren,leaf_image_prefixFiber]
  rfl

end Falconer

end OAI

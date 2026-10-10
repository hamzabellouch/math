import OAI.MeasureTheory.Falconer.Geometry.PointBallCounts
import OAI.MeasureTheory.Falconer.Recursion.LocalProfileRegularity

namespace OAI

/-! Local closed-ball bounds for the retained finite point set, derived
from the exact descendant ratios of its block class. -/
namespace Falconer
open Set Regularization

theorem finite_local_point_ball_count {d N a n : ℕ} (Q : DyadicCube d)
    (hQ : 0 < Q.side) {P : Finset (Space d)} {l : Space d → CellPath d}
    (hleaf : ∀ x ∈ P, l x ∈ cubePaths d N ∧ x ∈ (Q.descendant (l x)).carrier)
    (hn : n ≤ N) (p : CellPath d) {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hscale : 2*r ≤ Q.side/(2 : ℝ)^n)
    (hfiber : ∀ q ∈ (P.image l).image (List.take n),
      ((pointPrefixFiber P l n q).card : ℝ) ≤ M*(pointPrefixFiber P l a p).card)
    (z : Space d) :
    (((pointPrefixFiber P l a p).filter fun x => dist x z ≤ r).card : ℝ) ≤
      (7^d : ℕ)*M*(pointPrefixFiber P l a p).card := by
  classical
  have hsub : pointPrefixFiber P l a p ⊆ P := Finset.filter_subset _ _
  have hb := finite_point_ball_count Q hQ
    (fun x hx => hleaf x (hsub hx)) hn hr
    (mul_nonneg hM (Nat.cast_nonneg _)) hscale (M := M*(pointPrefixFiber P l a p).card)
    (fun q hq => ?_) z
  · simpa only [mul_assoc] using hb
  · have hq' : q ∈ (P.image l).image (List.take n) :=
      Finset.image_subset_image (Finset.image_subset_image hsub) hq
    have hsub' : pointPrefixFiber (pointPrefixFiber P l a p) l n q ⊆
        pointPrefixFiber P l n q := by
      intro x hx
      obtain ⟨hxp,hxq⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hsub hxp,hxq⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub')).trans (hfiber q hq')

theorem blockClass_point_ball_count {N : ℕ} (hN : 0 < N) {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (B : ℕ) (f : CellPath 2 → List ℕ) (K : ℕ)
    (p : CellPath 2) (Q : DyadicCube 2) (hQ : 0 < Q.side)
    {P : Finset (Space 2)} {l : Space 2 → CellPath 2}
    (hl : Set.InjOn l (P : Set (Space 2)))
    (hleaf : ∀ x ∈ P, l x ∈ cubePaths 2 N ∧ x ∈ (Q.descendant (l x)).carrier)
    (himage : P.image l = classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p))
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) {p₀ : CellPath 2}
    (hp₀ : p₀ ∈ (P.image l).image (List.take (blockDepth N B i)))
    {s A r : ℝ} (hr : 0 < r) (hscale : 2*r ≤ Q.side/(2 : ℝ)^(blockDepth N B j))
    (hprofile : let F := blockLabel L N B f K
      s*((blockDepth N B j : ℝ)-(blockDepth N B i : ℝ))-A ≤
        (N : ℝ)*(regularizedProfile L F N B K p (blockDepth N B j)-
          regularizedProfile L F N B K p (blockDepth N B i))) (z : Space 2) :
    (((pointPrefixFiber P l (blockDepth N B i) p₀).filter fun x => dist x z ≤ r).card : ℝ) ≤
      49*((2 : ℝ)^j*(2 : ℝ)^(A-s*((blockDepth N B j : ℝ)-(blockDepth N B i : ℝ))))*
        (pointPrefixFiber P l (blockDepth N B i) p₀).card := by
  classical
  have hp₀' := hp₀
  rw [himage] at hp₀'
  have hparent : 0 < ((pointPrefixFiber P l (blockDepth N B i) p₀).card : ℝ) := by
    rw [pointPrefixFiber_card_eq hl,himage]
    exact Nat.cast_pos.mpr (Finset.card_pos.mpr (prefixFiber_nonempty hp₀'))
  have hfiber (q : CellPath 2) (hq : q ∈ (P.image l).image (List.take (blockDepth N B j))) :
      ((pointPrefixFiber P l (blockDepth N B j) q).card : ℝ) ≤
      ((2 : ℝ)^j*(2 : ℝ)^(A-s*((blockDepth N B j : ℝ)-(blockDepth N B i : ℝ))))*
        (pointPrefixFiber P l (blockDepth N B i) p₀).card := by
    have hq' := hq
    rw [himage] at hq'
    have hb := blockClass_local_frostman hN hL B f K p hji hi hp₀' hq' hprofile
    dsimp only at hb
    rw [← himage,← pointPrefixFiber_card_eq hl,← pointPrefixFiber_card_eq hl] at hb
    exact (div_le_iff₀ hparent).1 hb
  have hb := finite_local_point_ball_count Q hQ hleaf (Nat.sub_le _ _)
    p₀ hr (by positivity) hscale hfiber z
  norm_num only [Nat.reducePow,Nat.cast_ofNat] at hb
  exact hb

end Falconer

end OAI

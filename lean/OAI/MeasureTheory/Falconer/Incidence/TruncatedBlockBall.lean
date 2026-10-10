import OAI.MeasureTheory.Falconer.Incidence.TruncatedBlockRatio
import OAI.MeasureTheory.Falconer.Estimates.PlanarPathCenters
import OAI.MeasureTheory.Falconer.Incidence.BlockProfileBallBound

namespace OAI

/-! Endpoint cells of a profile interval form an actual separated planar
set with the full local Frostman bound, including intermediate radii. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem blockClass_truncated_local_ball {N : ℕ} (hN : 0 < N) {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (B : ℕ) (f : CellPath 2 → List ℕ) (K : ℕ)
    (p : CellPath 2) (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) {p₀ : CellPath 2}
    (hp₀ : p₀ ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B i)))
    {s A : ℝ} (hs : 0 ≤ s) (hA : 0 ≤ A)
    (hprofile : ∀ k, j ≤ k → k ≤ i → let F := blockLabel L N B f K
      s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))-A ≤
        (N:ℝ)*(regularizedProfile L F N B K p (blockDepth N B k)-
          regularizedProfile L F N B K p (blockDepth N B i))) (y c : ℝ) :
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    let D := prefixChildren C (blockDepth N B i) (blockDepth N B j) p₀
    let P := D.image (fun q => (Q.descendant q).center)
    P.Nonempty ∧ FiniteSeparatedAt (1/(2:ℝ)^(blockDepth N B j)) P ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^(blockDepth N B j-blockDepth N B i)) s
        (49*(((2:ℝ)^(i+j)*(2:ℝ)^A)*((2:ℝ)^B)^s)*4^s)
        (P.image (localPacketPoint (1/(2:ℝ)^(blockDepth N B i)) y c)) := by
  let F := blockLabel L N B f K
  let C := classLeaves L F (F p)
  let D := prefixChildren C (blockDepth N B i) (blockDepth N B j) p₀
  let P := D.image (fun q => (Q.descendant q).center)
  have hCsub : C ⊆ cubePaths 2 N := fun q hq => hL (Finset.mem_filter.mp hq).1
  have hDsub : D ⊆ cubePaths 2 (blockDepth N B j) :=
    (Finset.image_subset_image (Finset.filter_subset _ _)).trans
      (planar_prefix_image_take_cubePaths hCsub (Nat.sub_le _ _))
  obtain ⟨l,hleaf,hl,himage,hsep⟩ := planar_path_center_realization Q (by rw [hQ]; norm_num) D hDsub
  have hDlow := (blockClass_descendant_count hL B f K p hji hi hp₀).1
  have hDn : D.Nonempty := by
    apply Finset.card_pos.mp
    have hp : 0 < (blockProduct L F N B i p:ℝ) := Nat.cast_pos.mpr (blockProduct_pos _ _ _ _ _ _)
    have hq : 0 < (blockProduct L F N B j p:ℝ) := Nat.cast_pos.mpr (blockProduct_pos _ _ _ _ _ _)
    have hpos : 0 < (D.card:ℝ) := (by positivity : 0 <
      ((blockProduct L F N B i p:ℝ)/(blockProduct L F N B j p:ℝ))/(2:ℝ)^j).trans_le hDlow
    exact Nat.cast_pos.mp hpos
  have hP : P.Nonempty := hDn.image _
  have hcard : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hP.card_pos
  refine ⟨hP,by simpa only [hQ] using hsep,?_⟩
  have hconst : 1 ≤ (2:ℝ)^(i+j)*(2:ℝ)^A :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (Real.one_le_rpow (by norm_num) hA)
  apply finite_relative_block_ball_bound le_rfl (blockDepth_antitone N B hji) hs hconst Q hQ P l hleaf
  intro n han hnb
  obtain ⟨k,hjk,hki,hkn,hgap⟩ := blockDepth_bracket hji han hnb
  refine ⟨blockDepth N B k,blockDepth_antitone N B hki,hkn,hgap,?_⟩
  intro q hq
  have hq' := hq
  rw [himage] at hq'
  have hb := blockClass_truncated_frostman hN hL B f K p hjk hki hi hp₀ hq'
    (hprofile k hjk hki)
  dsimp only at hb
  change (prefixFiber D (blockDepth N B k) q).card / (D.card:ℝ) ≤
    (2:ℝ)^(k+j)*(2:ℝ)^(A-s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))) at hb
  rw [← himage,← pointPrefixFiber_card_eq hl,Finset.card_image_iff.mpr hl] at hb
  have hpow : (2:ℝ)^(k+j)*(2:ℝ)^(A-s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))) ≤
      ((2:ℝ)^(i+j)*(2:ℝ)^A)*(1/(2:ℝ)^(blockDepth N B k-blockDepth N B i))^s := by
    rw [dyadic_inverse_power_eq,Nat.cast_sub (blockDepth_antitone N B hki),mul_assoc,
      ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    have he : A+-s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ)) =
        A-s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ)) := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
  exact ((div_le_iff₀ hcard).1 hb).trans (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _))

end Falconer

end OAI

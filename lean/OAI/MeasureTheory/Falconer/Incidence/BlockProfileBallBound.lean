import OAI.MeasureTheory.Falconer.Incidence.RelativeBlockBallBound
import OAI.MeasureTheory.Falconer.Incidence.BlockDepthBracket
import OAI.MeasureTheory.Falconer.Geometry.LocalPointBalls

namespace OAI

/-! The actual block-profile lower chords imply all-radius finite ball
bounds for each original parent fiber, after rescaling its chart. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem dyadic_inverse_power_eq (n : ℕ) (s : ℝ) :
    (1/(2:ℝ)^n)^s = (2:ℝ)^(-s*(n:ℝ)) := by
  rw [one_div,Real.inv_rpow (by positivity),← Real.rpow_natCast_mul (by norm_num),
    ← Real.rpow_neg (by norm_num)]
  congr 1
  ring

theorem blockClass_local_ball_bound {N : ℕ} (hN : 0 < N) {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (B : ℕ) (f : CellPath 2 → List ℕ) (K : ℕ)
    (p : CellPath 2) (Q : DyadicCube 2) (hQ : Q.side = 1)
    {P : Finset (Space 2)} {l : Space 2 → CellPath 2}
    (hl : Set.InjOn l (P : Set (Space 2)))
    (hleaf : ∀ x ∈ P, l x ∈ cubePaths 2 N ∧ x ∈ (Q.descendant (l x)).carrier)
    (himage : P.image l = classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p))
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) {p₀ : CellPath 2}
    (hp₀ : p₀ ∈ (P.image l).image (List.take (blockDepth N B i)))
    {s A : ℝ} (hs : 0 ≤ s) (hA : 0 ≤ A)
    (hprofile : ∀ k, j ≤ k → k ≤ i → let F := blockLabel L N B f K
      s*((blockDepth N B k : ℝ)-(blockDepth N B i : ℝ))-A ≤
        (N : ℝ)*(regularizedProfile L F N B K p (blockDepth N B k)-
          regularizedProfile L F N B K p (blockDepth N B i))) (y c : ℝ) :
    NormalizedFiniteBallBound
      (1/(2:ℝ)^(blockDepth N B j-blockDepth N B i)) s
      (49*(((2:ℝ)^i*(2:ℝ)^A)*((2:ℝ)^B)^s)*4^s)
      ((pointPrefixFiber P l (blockDepth N B i) p₀).image
        (localPacketPoint (1/(2:ℝ)^(blockDepth N B i)) y c)) := by
  let S := pointPrefixFiber P l (blockDepth N B i) p₀
  have hSP : S ⊆ P := Finset.filter_subset _ _
  have hp₀' := hp₀
  rw [himage] at hp₀'
  have hparent : 0 < (S.card:ℝ) := by
    dsimp [S]
    rw [pointPrefixFiber_card_eq hl,himage]
    exact Nat.cast_pos.mpr (Finset.card_pos.mpr (prefixFiber_nonempty hp₀'))
  have hconst : 1 ≤ (2:ℝ)^i*(2:ℝ)^A := by
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
      (Real.one_le_rpow (by norm_num) hA)
  apply finite_relative_block_ball_bound (Nat.sub_le _ _)
    (blockDepth_antitone N B hji) hs hconst Q hQ S l (fun x hx => hleaf x (hSP hx))
  intro n han hnb
  obtain ⟨k,hjk,hki,hkn,hgap⟩ := blockDepth_bracket hji han hnb
  refine ⟨blockDepth N B k,blockDepth_antitone N B hki,hkn,hgap,?_⟩
  intro q hq
  have hq' : q ∈ (P.image l).image (List.take (blockDepth N B k)) :=
    Finset.image_subset_image (Finset.image_subset_image hSP) hq
  rw [himage] at hq'
  have hb := blockClass_local_frostman hN hL B f K p hki hi hp₀' hq'
    (hprofile k hjk hki)
  dsimp only at hb
  rw [← himage,← pointPrefixFiber_card_eq hl,← pointPrefixFiber_card_eq hl] at hb
  have hsub : pointPrefixFiber S l (blockDepth N B k) q ⊆
      pointPrefixFiber P l (blockDepth N B k) q := by
    intro x hx
    obtain ⟨hx,hxq⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hSP hx,hxq⟩
  have hpow : (2:ℝ)^k*(2:ℝ)^(A-s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))) ≤
      ((2:ℝ)^i*(2:ℝ)^A)*(1/(2:ℝ)^(blockDepth N B k-blockDepth N B i))^s := by
    rw [dyadic_inverse_power_eq,Nat.cast_sub (blockDepth_antitone N B hki),mul_assoc,
      ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    have he : A+-s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ)) =
        A-s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ)) := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hki) (by positivity)
  calc
    _ ≤ ((pointPrefixFiber P l (blockDepth N B k) q).card:ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ((2:ℝ)^k*(2:ℝ)^(A-s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))))*(S.card:ℝ) :=
      (div_le_iff₀ hparent).1 hb
    _ ≤ _ := mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)

end Falconer

end OAI

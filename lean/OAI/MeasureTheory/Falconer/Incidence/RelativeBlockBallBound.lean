import OAI.MeasureTheory.Falconer.Incidence.BlockPrefixBallBound
import OAI.MeasureTheory.Falconer.Geometry.RelativePrefixBallBound

namespace OAI

/-! Relative selected-depth tests give normalized ball bounds in the
original parent chart, retaining the block interpolation loss. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem finite_relative_block_ball_bound {N M a B : ℕ}
    (hMN : M ≤ N) (ha : a ≤ M) {s K : ℝ} (hs : 0 ≤ s) (hK : 1 ≤ K)
    (Q : DyadicCube 2) (hQ : Q.side = 1)
    (P : Finset (Space 2)) (l : Space 2 → CellPath 2)
    (hleaf : ∀ x ∈ P, l x ∈ cubePaths 2 N ∧ x ∈ (Q.descendant (l x)).carrier)
    (htests : ∀ n, a ≤ n → n ≤ M → ∃ b, a ≤ b ∧ b ≤ n ∧ n ≤ b+B ∧
      ∀ p ∈ (P.image l).image (List.take b),
        ((pointPrefixFiber P l b p).card:ℝ) ≤ K*(1/(2:ℝ)^(b-a))^s*(P.card:ℝ))
    (y c : ℝ) :
    NormalizedFiniteBallBound (1/(2:ℝ)^(M-a)) s (49*(K*((2:ℝ)^B)^s)*4^s)
      (P.image (localPacketPoint (1/(2:ℝ)^a) y c)) := by
  have hKB : 1 ≤ K*((2:ℝ)^B)^s := by
    have hp : 1 ≤ ((2:ℝ)^B)^s :=
      Real.one_le_rpow (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) hs
    simpa using mul_le_mul hK hp (by norm_num : (0:ℝ) ≤ 1) (zero_le_one.trans hK)
  apply finite_relative_prefix_ball_bound_at hMN ha hs hKB Q hQ P l hleaf
  intro n han hn p hp
  obtain ⟨b,hab,hbn,hgap,hbound⟩ := htests n han hn
  have hpb : p.take b ∈ (P.image l).image (List.take b) := by
    obtain ⟨v,hv,hvp⟩ := Finset.mem_image.mp hp
    refine Finset.mem_image.mpr ⟨v,hv,?_⟩
    have hh := congrArg (List.take b) hvp
    simpa only [List.take_take,Nat.min_eq_left hbn] using hh
  calc
    _ ≤ ((pointPrefixFiber P l b (p.take b)).card:ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card (pointPrefixFiber_subset_take P l hbn p))
    _ ≤ K*(1/(2:ℝ)^(b-a))^s*(P.card:ℝ) := hbound _ hpb
    _ ≤ K*(((2:ℝ)^B)^s*(1/(2:ℝ)^(n-a))^s)*(P.card:ℝ) := by
      gcongr
      exact dyadic_prefix_gap_bound (by omega : b-a ≤ n-a) (by omega) hs
    _ = _ := by ring

end Falconer

end OAI

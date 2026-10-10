import OAI.MeasureTheory.Falconer.Geometry.RetainedEndpointGeometry
import OAI.MeasureTheory.Falconer.Incidence.TruncatedBlockCover

namespace OAI

/-! Profile estimates on the actual endpoint centers after a retained class
is regularized again. The original profile remains the reference profile. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

noncomputable def blockEndpointSet (Q : DyadicCube 2) (C : Finset (CellPath 2))
    (a b : ℕ) (p₀ : CellPath 2) : Finset (Space 2) :=
  ((prefixChildren C a b p₀).image (fun r => (Q.descendant r).center)).image
    (localPacketPoint (1/(2:ℝ)^a) ((Q.descendant p₀).center 0) ((Q.descendant p₀).center 1))

theorem normalizedFiniteBallBound_mono_constant {δ s A B : ℝ} {P : Finset (Space 2)}
    (hδ : 0 ≤ δ) (hAB : A ≤ B) (h : NormalizedFiniteBallBound δ s A P) :
    NormalizedFiniteBallBound δ s B P := by
  intro z r hr hr1
  exact (h z r hr hr1).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg (hδ.trans hr) _)) (Nat.cast_nonneg _))

section Retained
variable {N : ℕ} {L L' : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (hL' : L' ⊆ cubePaths 2 N)
    (B : ℕ) (f g : CellPath 2 → List ℕ) (K : ℕ) (p q : CellPath 2)
    (hsub : classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q) ⊆
      classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p))
    {M : ℝ} (hM : 0 ≤ M)
    (hmass : ((classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).card:ℝ) ≤
      M*((classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).card:ℝ))
    (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) {p₀ : CellPath 2}
    (hp₀ : p₀ ∈ (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).image
      (List.take (blockDepth N B i)))

include hL hL' hsub hM hmass hQ hji hi hp₀ in
theorem blockClass_retained_endpoint_ball (hN : 0 < N) {s A : ℝ}
    (hs : 0 ≤ s) (hA : 0 ≤ A)
    (hprofile : ∀ k, j ≤ k → k ≤ i → let F := blockLabel L N B f K
      s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))-A ≤
        (N:ℝ)*(regularizedProfile L F N B K p (blockDepth N B k)-
          regularizedProfile L F N B K p (blockDepth N B i))) :
    let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
    let Z := blockEndpointSet Q S (blockDepth N B i) (blockDepth N B j) p₀
    Z.Nonempty ∧ InBoundedLineChart Z ∧
      FiniteSeparatedAt (1/(2:ℝ)^(blockDepth N B j-blockDepth N B i)) Z ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^(blockDepth N B j-blockDepth N B i)) s
        ((49*(((2:ℝ)^(i+j)*(2:ℝ)^A)*((2:ℝ)^B)^s)*4^s)*(M*(2:ℝ)^(2*i+2*j))) Z := by
  have hpC := Finset.image_subset_image hsub hp₀
  obtain ⟨_,_,hball⟩ := blockClass_truncated_local_ball hN hL B f K p Q hQ hji hi hpC
    hs hA hprofile ((Q.descendant p₀).center 0) ((Q.descendant p₀).center 1)
  obtain ⟨hne,_,hchart,hsep,_,htransfer⟩ := blockClass_retained_endpoint_geometry
    hL hL' B f g K p q hsub hM hmass Q hQ hji hi hp₀
  exact ⟨hne,hchart,hsep,htransfer s _ (by positivity) hball⟩

include hL hsub hQ hi hp₀ in
theorem blockClass_retained_endpoint_cover (hN : 0 < N)
    {k : ℕ} (hjk : j ≤ k) (hki : k ≤ i) {t A ρ : ℝ} (hρ : 0 < ρ)
    (hscale : (1/(2:ℝ)^(blockDepth N B k))/(1/(2:ℝ)^(blockDepth N B i)) ≤ ρ)
    (hprofile : let F := blockLabel L N B f K
      (N:ℝ)*(regularizedProfile L F N B K p (blockDepth N B k)-
        regularizedProfile L F N B K p (blockDepth N B i)) ≤
          t*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))+A) :
    let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
    let Z := blockEndpointSet Q S (blockDepth N B i) (blockDepth N B j) p₀
    ((Z.image (coarsePlanarRound ρ)).card:ℝ) ≤
      49*((2:ℝ)^i*(2:ℝ)^(t*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))+A)) := by
  have hpC := Finset.image_subset_image hsub hp₀
  have hcover := blockClass_truncated_local_cover hN hL B f K p Q hQ hjk hki hi hpC
    hρ hscale hprofile ((Q.descendant p₀).center 0) ((Q.descendant p₀).center 1)
  apply le_trans _ hcover
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  apply Finset.image_subset_image
  apply Finset.image_subset_image
  apply Finset.image_subset_image
  exact Finset.image_subset_image (Finset.filter_subset_filter _ hsub)

end Retained
end Falconer

end OAI

import OAI.MeasureTheory.Falconer.Incidence.BlockCellNormalGain
import OAI.MeasureTheory.Falconer.Recursion.ProfileGoodBound

namespace OAI

/-! Apply the regular incidence gain directly to a linear profile cell.
One explicit geometric constant controls all the required point and cover data. -/
namespace Falconer
open Set Regularization

theorem block_cell_good_gain {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) :
    ∃ ε η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ ε ≤ 1 ∧ 0 < η ∧ 0 < N0 ∧
    ∀ n : ℕ, N0 ≤ n+3 → ∀ s t W θ : ℝ,
      κ ≤ s → s ≤ 1-8*κ → 2*κ ≤ t-s → t ≤ 2 → 1 ≤ W → 0 ≤ θ →
    ∀ N B K : ℕ, 0 < N → ∀ L : Finset (CellPath 2), L ⊆ cubePaths 2 N →
    ∀ (f : CellPath 2 → List ℕ) (p : CellPath 2) (Q : DyadicCube 2), Q.side = 1 →
    ∀ i j : ℕ, j ≤ i → i ≤ K → blockDepth N B j-blockDepth N B i = 2*n →
      (let g := regularizedProfile L (blockLabel L N B f K) N B K p;
        t = intervalSecantSlope (fun x => g ((N:ℝ)*x))
          (blockProfileCell N B (i,j)).1 (blockProfileCell N B (i,j)).2) →
      (let g := regularizedProfile L (blockLabel L N B f K) N B K p;
        ∀ x ∈ Icc (blockProfileCell N B (i,j)).1
            ((blockProfileCell N B (i,j)).1+(blockProfileCell N B (i,j)).2),
          |intervalSecantError (fun u => g ((N:ℝ)*u))
            (blockProfileCell N B (i,j)).1 (blockProfileCell N B (i,j)).2 x| ≤
              θ*(blockProfileCell N B (i,j)).2) →
      profileGeometryConstant K B W (θ*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))) ≤
        Real.exp (ε*((n+3:ℕ):ℝ)*Real.log 2) →
      ProfileEndpointBound N B K L f p Q i j s W ((1/(2:ℝ)^(2*n+2))^(-(s+η))) := by
  obtain ⟨ε,η,N0,hε,hε1,hη,hN0,hgood⟩ := profileEndpointBound_good hκ hκ1
  refine ⟨ε,η,N0,hε,hε1,hη,hN0,?_⟩
  intro n hn s t W θ hs hs1 hgap ht hW hθ N B K hN L hL f p Q hQ i j hji hi hlen
    hslope herr hbudget
  let A := θ*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))
  have hA : 0 ≤ A := mul_nonneg hθ (sub_nonneg.mpr (Nat.cast_le.mpr (blockDepth_antitone N B hji)))
  have ht0 : 0 ≤ t := by linarith only [hκ,hs,hgap]
  obtain ⟨hpoint,hcover⟩ := profile_geometry_costs (B := B) hi (hji.trans hi) ht0 ht hA hW
  have hlo := blockProfileCell_chord_lower (B := B) (i := i) (j := j) (ε := θ)
    (regularizedProfile L (blockLabel L N B f K) N B K p) hN hslope.le
    (fun x hx => by simpa only [neg_mul] using (abs_le.mp (herr x hx)).1)
  have hhi := blockProfileCell_chord_upper (B := B) (i := i) (j := j) (ε := θ)
    (regularizedProfile L (blockLabel L N B f K) N B K p) hN hslope.symm.le
    (fun x hx => (abs_le.mp (herr x hx)).2)
  have hprofile := fun k hjk hki => And.intro (hlo k hjk hki) (hhi k hjk hki)
  exact hgood n hn s t W hs hs1 hgap ht hW N B K hN L hL f p Q hQ i j hji hi hlen A hA
    hprofile (hpoint.trans hbudget) (hcover.trans hbudget)
    ((profileGeometryConstant_ge hW hA K B).trans hbudget)

end Falconer

end OAI

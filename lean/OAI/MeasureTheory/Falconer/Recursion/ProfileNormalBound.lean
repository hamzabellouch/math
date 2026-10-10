import OAI.MeasureTheory.Falconer.Recursion.ProfileEndpointBound

namespace OAI

/-! The critical second-moment estimate supplies the normal-interval base
case of the recursive profile endpoint bound. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem profileEndpointBound_normal {N B K : ℕ} (hN : 0 < N)
    {L : Finset (CellPath 2)} (hL : L ⊆ cubePaths 2 N)
    (f : CellPath 2 → List ℕ) (p : CellPath 2) (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) {s A W : ℝ}
    (hs : 0 ≤ s) (hA : 0 ≤ A) (hW : 1 ≤ W)
    (hprofile : ∀ k, j ≤ k → k ≤ i → let F := blockLabel L N B f K
      s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))-A ≤
        (N:ℝ)*(regularizedProfile L F N B K p (blockDepth N B k)-
          regularizedProfile L F N B K p (blockDepth N B i))) :
    let D := blockDepth N B j-blockDepth N B i+2
    let C := (49*(((2:ℝ)^(i+j)*(2:ℝ)^A)*((2:ℝ)^B)^s)*4^s)*(W*(2:ℝ)^(2*i+2*j))
    let H := max 1 (max W ((max 1 C)*4^s))
    ProfileEndpointBound N B K L f p Q i j s W
      ((1/(2:ℝ)^D)^(-s)/(W*H*80^s*(1+H*planarCriticalConstant D s))) := by
  let D := blockDepth N B j-blockDepth N B i+2
  let C := (49*(((2:ℝ)^(i+j)*(2:ℝ)^A)*((2:ℝ)^B)^s)*4^s)*(W*(2:ℝ)^(2*i+2*j))
  let H := max 1 (max W ((max 1 C)*4^s))
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hcrit : 0 ≤ planarCriticalConstant D s := by unfold planarCriticalConstant; positivity
  have hcost : 0 < W*H*80^s*(1+H*planarCriticalConstant D s) := by positivity
  dsimp only
  intro L' g q a₀ r₀ hL' C₀ S hsub hmass ha₀ p₀ hp₀ m hm V Z hV
  have hh := blockClass_parent_quarter_normal_ratio hN hL hL' B f g K p q r₀
    hsub (zero_le_one.trans hW) hmass Q hQ hji hi ha₀ hp₀ hs hA hprofile m W hm V
    (fun x hx => ⟨(hV x hx).1,(hV x hx).2.1,(hV x hx).2.2.1,
      (hV x hx).2.2.2.2.1,fun l hl => ((hV x hx).2.2.2.2.2 l hl).2⟩)
  apply (div_le_iff₀ hcost).2
  convert hh using 1
  ring

end Falconer

end OAI

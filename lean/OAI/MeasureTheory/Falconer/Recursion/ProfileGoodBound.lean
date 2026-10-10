import OAI.MeasureTheory.Falconer.Recursion.ProfileEndpointBound

namespace OAI

/-! The independently proved regular incidence gain supplies the good-interval
base case, on every retained reference class allowed by the induction. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem profileEndpointBound_good {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) :
    ∃ ε η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ ε ≤ 1 ∧ 0 < η ∧ 0 < N0 ∧
    ∀ n : ℕ, N0 ≤ n+3 → ∀ s t W : ℝ,
      κ ≤ s → s ≤ 1-8*κ → 2*κ ≤ t-s → t ≤ 2 → 1 ≤ W →
    ∀ N B K : ℕ, 0 < N → ∀ L : Finset (CellPath 2), L ⊆ cubePaths 2 N →
    ∀ (f : CellPath 2 → List ℕ) (p : CellPath 2) (Q : DyadicCube 2), Q.side = 1 →
    ∀ i j : ℕ, j ≤ i → i ≤ K → blockDepth N B j-blockDepth N B i = 2*n →
    ∀ A : ℝ, 0 ≤ A →
      (∀ k, j ≤ k → k ≤ i → let F := blockLabel L N B f K
        let v := (N:ℝ)*(regularizedProfile L F N B K p (blockDepth N B k)-
          regularizedProfile L F N B K p (blockDepth N B i))
        t*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))-A ≤ v ∧
          v ≤ t*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))+A) →
      let E := Real.exp (ε*((n+3:ℕ):ℝ)*Real.log 2)
      (max 1 ((49*(((2:ℝ)^(i+j)*(2:ℝ)^A)*((2:ℝ)^B)^t)*4^t)*
        (W*(2:ℝ)^(2*i+2*j))))*4^t ≤ E →
      25*(49*((2:ℝ)^i*(2:ℝ)^(t*((B:ℝ)+3)+A))) ≤ E → W ≤ E →
      ProfileEndpointBound N B K L f p Q i j s W ((1/(2:ℝ)^(2*n+2))^(-(s+η))) := by
  obtain ⟨ε,η,N0,hε,hε1,hη,hN0,hgain⟩ := blockClass_parent_quarter_good_gain hκ hκ1
  refine ⟨ε,η,N0,hε,hε1,hη,hN0,?_⟩
  intro n hn s t W hs hs1 hgap ht hW N B K hN L hL f p Q hQ i j hji hi hlen A hA hprofile
  dsimp only
  intro hpoint hcover hWE L' g q a₀ r₀ hL' C S hsub hmass ha₀ p₀ hp₀ m hm V Z hV
  have hbad := hgain n hn s t m hs hs1 hgap ht hm N a₀ hN L L' hL hL'
    B f g K p q r₀ hsub W (zero_le_one.trans hW) hmass Q hQ i j hji hi ha₀ p₀ hp₀ hlen
    A hA hprofile hpoint hcover V (by
      intro x hx
      obtain ⟨hlo,hhi,hch,hsp,hb,hinc⟩ := hV x hx
      rw [hlen] at hsp hb hinc
      exact ⟨hlo,hhi.trans (mul_le_mul_of_nonneg_right hWE hm.le),hch,hsp,
        normalizedFiniteBallBound_mono_constant (by positivity) hWE hb,
        fun l hl => (hinc l hl).2⟩)
  have hh := (lt_of_not_ge hbad).le
  apply (le_div_iff₀ hm).2
  rw [Real.rpow_neg (by positivity : 0 ≤ 1/(2:ℝ)^(2*n+2))]
  simpa only [div_eq_mul_inv,mul_comm] using hh

end Falconer

end OAI

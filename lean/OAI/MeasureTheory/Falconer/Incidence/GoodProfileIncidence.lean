import OAI.MeasureTheory.Falconer.Geometry.EndpointMidscaleCover
import OAI.MeasureTheory.Falconer.Geometry.FullChartRegularGain

namespace OAI

/-! The good-interval gain on the actual retained endpoint centers. Both
profile errors and earlier retention costs enter the explicit weak budget. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem blockClass_retained_good_gain {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) :
    ∃ ε η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ ε ≤ 1 ∧ 0 < η ∧ 0 < N0 ∧
    ∀ n : ℕ, N0 ≤ n+2 → ∀ s t m : ℝ,
      κ ≤ s → s ≤ 1-8*κ → 2*κ ≤ t-s → t ≤ 2 → 0 < m →
    ∀ N : ℕ, 0 < N → ∀ L L' : Finset (CellPath 2),
      L ⊆ cubePaths 2 N → L' ⊆ cubePaths 2 N →
    ∀ (B : ℕ) (f g : CellPath 2 → List ℕ) (K : ℕ) (p q : CellPath 2),
      classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q) ⊆
        classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p) →
    ∀ M : ℝ, 0 ≤ M →
      ((classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).card:ℝ) ≤
        M*((classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).card:ℝ) →
    ∀ Q : DyadicCube 2, Q.side = 1 → ∀ i j : ℕ, j ≤ i → i ≤ K →
    ∀ p₀ ∈ (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).image
      (List.take (blockDepth N B i)),
      blockDepth N B j-blockDepth N B i = 2*n →
    ∀ A : ℝ, 0 ≤ A →
      (∀ k, j ≤ k → k ≤ i → let F := blockLabel L N B f K
        let v := (N:ℝ)*(regularizedProfile L F N B K p (blockDepth N B k)-
          regularizedProfile L F N B K p (blockDepth N B i))
        t*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))-A ≤ v ∧
          v ≤ t*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))+A) →
      let E := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
      (49*(((2:ℝ)^(i+j)*(2:ℝ)^A)*((2:ℝ)^B)^t)*4^t)*(M*(2:ℝ)^(2*i+2*j)) ≤ E →
      49*((2:ℝ)^i*(2:ℝ)^(t*((B:ℝ)+3)+A)) ≤ E →
      let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
      let Z := blockEndpointSet Q S (blockDepth N B i) (blockDepth N B j) p₀
      let δ := 1/(2:ℝ)^(2*n)
      ∀ V : Space 2 → Finset (Space 2),
        (∀ z ∈ Z, m ≤ ((V z).card:ℝ) ∧ ((V z).card:ℝ) ≤ E*m ∧
          InBoundedLineChart (V z) ∧ FiniteSeparatedAt δ (V z) ∧
          NormalizedFiniteBallBound δ s E (V z) ∧ ∀ l ∈ V z, TubeIncident δ z l) →
        ¬ ((Z.biUnion V).card:ℝ) ≤ m/δ^(s+η) := by
  obtain ⟨ε,η,N0,hε,hε1,hη,hN0,hgain⟩ := full_chart_regular_fine_gain hκ hκ1
  refine ⟨ε,η,max N0 5,hε,hε1,hη,lt_of_lt_of_le hN0 (le_max_left _ _),?_⟩
  intro n hn s t m hs hs1 hgap ht hm N hN L L' hL hL' B f g K p q hsub
    M hM hmass Q hQ i j hji hi p₀ hp₀ hlen A hA hprofile
  dsimp only
  intro hpointBudget hcoverBudget V hV
  have hn3 : 3 ≤ n := by have := (le_max_right N0 5).trans hn; omega
  have ht0 : 0 ≤ t := by linarith only [hκ,hs,hgap]
  obtain ⟨hne,hchart,hsep,hball⟩ := blockClass_retained_endpoint_ball hL hL' B f g K p q
    hsub hM hmass Q hQ hji hi hp₀ hN ht0 hA (fun k hjk hki => (hprofile k hjk hki).1)
  have hcover := blockClass_retained_midscale_cover hN hL B f g K p q hsub Q hQ hji hi hp₀
    hn3 hlen ht0 (fun k hjk hki => (hprofile k hjk hki).2)
  rw [hlen] at hsep hball
  apply hgain n ((le_max_left _ _).trans hn) s t m hs hs1 hgap ht hm _ hne hchart hsep
  · exact normalizedFiniteBallBound_mono_constant (by positivity) hpointBudget hball
  · exact hcover.trans (div_le_div_of_nonneg_right hcoverBudget (by positivity))
  · exact hV

end Falconer

end OAI

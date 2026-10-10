import Mathlib
import OAI.Combinatorics.KMedian.Rounding.RationalProposalCount
import OAI.Combinatorics.KMedian.Rounding.RationalPhysicalGraphInstance

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {Δ : ℕ}
local instance rationalPhysicalCountCopyOrder : LinearOrder (CopyState.Copy (F := F) Δ) := copyOrder

omit [Fintype F] in

theorem step_count_tail (d : F → F → ℚ) (location : F → X)
    (hd : ∀ i j, dist (location i) (location j)=(d i j:ℝ))
    (g β p φ P : ℚ) (hp0 : 0 ≤ p) (hφ0 : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (s : State F Δ g β)
    (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hp : 0 < (p:ℝ))
    (hφ : 0 < (φ:ℝ)) (hφ1 : (φ:ℝ) ≤ 1) (hβ : 0 < (β:ℝ))
    (hunit : (g:ℝ)*(Δ:ℝ)=1) (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2)
    (hA : 1 ≤ mass (g:ℝ) s.1) (hsmall : 8*(p:ℝ)*(Δ:ℝ) ≤ (φ:ℝ)*(g:ℝ)) :
    (step d g β p φ P hp0 hφ0 hupper s).expectation
      (fun t => if mass (g:ℝ) s.1+4/((g:ℝ)*(β:ℝ)) < mass (g:ℝ) t.1 then 1 else 0) ≤
      96*(Δ:ℝ)^2*(β:ℝ)/((p:ℝ)*(φ:ℝ)^2*(g:ℝ)) := by
  let μ := graphLaw d g P s.1
  let ν : (G : s.1 → Finset s.1) → SparseIntegerLaw
      (Finset (FixedBatch.HeavyAction (RationalBatchData.graph G)
        (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β))) :=
    fun G => RationalBatchData.proposal G Δ g β p φ hp0 hφ0 hupper
      (RationalBatchData.enumeration (RationalBatchData.graph G)
        (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β))
  let V := fun (G : s.1 → Finset s.1) Z =>
    if mass (g:ℝ) s.1+4/((g:ℝ)*(β:ℝ)) < mass (g:ℝ)
      (RationalBatchData.transition s.1 G
        (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β) Z) then (1:ℝ) else 0
  obtain ⟨D,hgood,_,_⟩ := graph_data d location hd g P s.1 hg hunit hP hP1 hA
  have hc : ∀ G, 0 < μ.real.weight G → (ν G).real.expect (V G) ≤
      96*(Δ:ℝ)^2*(β:ℝ)/((p:ℝ)*(φ:ℝ)^2*(g:ℝ)) := by
    intro G hG
    exact RationalBatchData.proposal_count_tail s.1 G g β p φ hp0 hφ0 hupper
      (RationalBatchData.enumeration (RationalBatchData.graph G)
        (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β))
      hg hg1 hp hφ hφ1 hβ hunit (hgood G hG).1 hsmall
  have hh := μ.real.expect_mono_support hc
  rw [FiniteLaw.expect_const] at hh
  rw [step_expectation, ← SparseIntegerLaw.real_expect_all]
  change μ.real.expect (fun G => (ν G).expectation (V G)) ≤ _
  have he : ∀ G, (ν G).expectation (V G)=(ν G).real.expect (V G) :=
    fun G => (SparseIntegerLaw.real_expect_all (ν G) (V G)).symm
  simp_rw [he]
  exact hh

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI

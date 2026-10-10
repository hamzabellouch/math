import Mathlib
import OAI.Combinatorics.KMedian.Rounding.RationalPhysicalGraphInstance
import OAI.Combinatorics.KMedian.Rounding.RationalPhysicalReplay
import OAI.Combinatorics.KMedian.Rounding.RationalProposalSurvival

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {Δ : ℕ}
local instance : LinearOrder (CopyState.Copy (F := F) Δ) := copyOrder

omit [Fintype F] in
                                                                               
theorem step_survival (d₀ : F → F → ℚ) (location : F → X)
    (hd : ∀ i j, dist (location i) (location j)=(d₀ i j:ℝ))
    (g β p φ P : ℚ) (hp0 : 0 ≤ p) (hφ0 : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (s : State F Δ g β) (S : Finset (CopyState.Copy (F := F) Δ))
    {x h : ℝ} (d : F → ℝ) (hprob : (p:ℝ)=2*h*(g:ℝ))
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2)
    (hh0 : 0 ≤ h) (hφ1 : (φ:ℝ) ≤ 1)
    (hA : 1 ≤ mass (g:ℝ) s.1)
    (hsmall : (2*h*(g:ℝ))*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ)) ≤ 1) (hSA : S ⊆ s.1) :
    (step d₀ g β p φ P hp0 hφ0 hupper s).expectation
      (fun t => mass (g:ℝ) (labels g β x (fun (_ : Unit) => d) t (fun _ => S) ())) ≤
      (1-h/2)*mass (g:ℝ) S := by
  let μ := graphLaw d₀ g P s.1
  let ν : (G : s.1 → Finset s.1) → SparseIntegerLaw
      (Finset (FixedBatch.HeavyAction (RationalBatchData.graph G)
        (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β))) :=
    fun G => RationalBatchData.proposal G Δ g β p φ hp0 hφ0 hupper
      (RationalBatchData.enumeration (RationalBatchData.graph G)
        (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β))
  let V := fun (G : s.1 → Finset s.1) Z =>
    mass (g:ℝ) (CopyState.roundAlive s.1 S G
      (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β) Z x (g:ℝ) d)
  obtain ⟨D,hgood,_,_⟩ := graph_data d₀ location hd g P s.1 hg hunit hP hP1 hA
  have hc : ∀ G, 0 < μ.real.weight G → (ν G).real.expect (V G) ≤ (1-h/2)*mass (g:ℝ) S := by
    intro G hG
    exact RationalBatchData.proposal_survival s.1 S G g β p φ hp0 hφ0 hupper
      (RationalBatchData.enumeration (RationalBatchData.graph G)
        (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β))
      d hprob (hgood G hG).1 hg.le hunit hh0 hφ1 hsmall hSA
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

import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparsePhysicalCount
import OAI.Combinatorics.KMedian.Rounding.RationalBatchFacts
import OAI.Combinatorics.KMedian.Rounding.RationalCopyTransition

namespace OAI

section
section
namespace MetricKMedian.RationalBatchData
open Finset FixedBatch PhysicalPotential
variable {I : Type} [DecidableEq I] [Fintype I]

theorem graph_heavy_eq (G : I → Finset I) (g β : ℚ) :
    heavySet (graphMass G g) β=
      univ.filter (fun h => max (1:ℝ)
        ((β:ℝ)*SourceBalance.amount (fun h => mass (g:ℝ) ((graphActions G).erase h)))<
        mass (g:ℝ) ((graphActions G).erase h)) := by
  simpa only [cast_graphMass] using heavySet_eq (graphMass G g) β

end MetricKMedian.RationalBatchData

namespace MetricKMedian.RationalBatchData
open Finset FixedBatch PhysicalPotential
variable {F : Type} [DecidableEq F] {Δ n : ℕ}

theorem proposal_count_tail (A : Finset (CopyState.Copy (F := F) Δ)) (G : A → Finset A)
    (g β p φ : ℚ) (hp0 : 0 ≤ p) (hφ0 : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (enum : Fin n ≃ HeavyAction (graph G) (heavySet (graphMass G g) β))
    (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hp : 0 < (p:ℝ))
    (hφ : 0 < (φ:ℝ)) (hφ1 : (φ:ℝ) ≤ 1) (hβ : 0 < (β:ℝ))
    (hunit : (g:ℝ)*(Δ:ℝ)=1) (hG : ∀ i, (G i).card=Δ)
    (hsmall : 8*(p:ℝ)*(Δ:ℝ) ≤ (φ:ℝ)*(g:ℝ)) :
    (proposal G Δ g β p φ hp0 hφ0 hupper enum).real.prob
      (fun Z => mass (g:ℝ) A+4/((g:ℝ)*(β:ℝ)) <
        mass (g:ℝ) (transition A G (heavySet (graphMass G g) β) Z)) ≤
      96*(Δ:ℝ)^2*(β:ℝ)/((p:ℝ)*(φ:ℝ)^2*(g:ℝ)) := by
  have hpp : 0 ≤ p ∧ p ≤ 1 := ⟨hp0,by have hh := mul_nonneg hp0 hφ0; nlinarith only [hh,hupper]⟩
  let H := heavySet (graphMass G g) β
  let q := fun e : HeavyAction (graph G) H => bias (graphMass G g) p φ (heavyParent (graph G) H e)
  have hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1 := fun e => bias_probability _ hp0 hφ0 hupper _
  have hh := @SparseCopyState.physical_count_tail F _ Δ n A G g p (φ:ℝ) (β:ℝ)
    hg hg1 hp hφ hφ1 hβ hunit hG hpp hsmall
  dsimp only at hh
  rw [← graph_heavy_eq G g β] at hh
  have hqcast : ∀ e, (q e:ℝ)=SourceBalance.bias
      (fun h => mass (g:ℝ) ((graphActions G).erase h)) (p:ℝ) (φ:ℝ)
      (heavyParent (graph G) H e) := by
    intro e
    simpa only [q,cast_graphMass] using cast_bias (graphMass G g) p φ (heavyParent (graph G) H e)
  have ht := hh enum q hq hqcast
  rw [proposal_eq G Δ g β p φ hp0 hφ0 hupper enum hpp hq]
  exact ht

end MetricKMedian.RationalBatchData
end
end

end OAI

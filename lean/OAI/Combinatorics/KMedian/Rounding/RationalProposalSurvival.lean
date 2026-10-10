import Mathlib
import OAI.Combinatorics.KMedian.Rounding.RationalBatchFacts
import OAI.Combinatorics.KMedian.Sparse.SparsePhysicalSurvival

namespace OAI

section
section
namespace MetricKMedian.RationalBatchData
open Finset PhysicalPotential FixedBatch CopyState
variable {F : Type} [DecidableEq F] {Δ n : ℕ}

theorem proposal_survival (A S : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (g β p φ : ℚ) (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (enum : Fin n ≃ HeavyAction (graph G) (heavySet (graphMass G g) β))
    {x h : ℝ} (d : F → ℝ) (hprob : (p:ℝ)=2*h*(g:ℝ))
    (hG : ∀ i, (G i).card=Δ) (hg : 0 ≤ (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hh0 : 0 ≤ h) (hφ1 : (φ:ℝ) ≤ 1)
    (hsmall : (2*h*(g:ℝ))*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ)) ≤ 1) (hSA : S ⊆ A) :
    (proposal G Δ g β p φ hp hφ hupper enum).real.expect (fun Z =>
      mass (g:ℝ) (roundAlive A S G (heavySet (graphMass G g) β) Z x (g:ℝ) d)) ≤
      (1-h/2)*mass (g:ℝ) S := by
  let H := heavySet (graphMass G g) β
  let q := fun e : HeavyAction (graph G) H => bias (graphMass G g) p φ (heavyParent (graph G) H e)
  have hpp : 0 ≤ p ∧ p ≤ 1 := ⟨hp,by have hh := mul_nonneg hp hφ; nlinarith only [hh,hupper]⟩
  have hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1 := fun e => bias_probability _ hp hφ hupper _
  have hqb : ∀ e, (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ 2*(p:ℝ) := by
    intro e
    have hb : (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ (1+(φ:ℝ))*(p:ℝ) := by
      exact_mod_cast bias_bounds (graphMass G g) hp hφ (heavyParent (graph G) H e)
    have hpR : (0:ℝ) ≤ p := by exact_mod_cast hp
    have hu := mul_le_mul_of_nonneg_right hφ1 hpR
    exact ⟨hb.1,by nlinarith only [hb.2,hu]⟩
  have ht := enumerated_conditional_round_survival A S G H enum p q d hG hg hunit hh0
    hprob hpp hq hqb hsmall hSA (x := x)
  rw [proposal_eq G Δ g β p φ hp hφ hupper enum hpp hq]
  exact ht

end MetricKMedian.RationalBatchData
end
end

end OAI

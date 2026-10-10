import Mathlib
import OAI.Combinatorics.KMedian.Rounding.RationalPhysicalKernel

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential
variable {F : Type} [LinearOrder F] [Fintype F] {Δ : ℕ}

omit [Fintype F] in
                                                                        
theorem own_card (A : Finset (CopyState.Copy (F := F) Δ)) (i : A) :
    (own A i).card ≤ Δ := by
  exact CopyState.own_card_le Δ A i

omit [Fintype F] in

theorem update_mass (g β : ℚ) (A : Finset (CopyState.Copy (F := F) Δ))
    (e : RationalBatchData.Event A g β) (hg : 0 ≤ (g:ℝ))
    (hunit : (g:ℝ)*(Δ:ℝ)=1) (hA : 1 ≤ mass (g:ℝ) A) :
    1 ≤ mass (g:ℝ) (updateEvent g β A e).1 := by
  obtain ⟨G,Z⟩ := e
  exact CopyState.round_mass_at_least_one A G
    (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β) Z hg hunit hA

omit [Fintype F] in
theorem step_mass (d : F → F → ℚ) (g β p φ P : ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (s : State F Δ g β) (hg : 0 ≤ (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hs : 1 ≤ mass (g:ℝ) s.1) (i : Fin (step d g β p φ P hp hφ hupper s).length) :
    1 ≤ mass (g:ℝ) (step d g β p φ P hp hφ hupper s).states[i.val].1 := by
  obtain ⟨e,he⟩ := step_records d g β p φ P hp hφ hupper s i
  rw [he]
  exact update_mass g β s.1 e hg hunit hs

omit [Fintype F] in

theorem histories_mass (d : F → F → ℚ) (g β p φ : ℚ) (P : ℕ → ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A : Finset (CopyState.Copy (F := F) Δ)) (T : ℕ)
    (hg : 0 ≤ (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1) (hA : 1 ≤ mass (g:ℝ) A)
    (i : Fin (histories d g β p φ P hp hφ hupper A T).length) :
    1 ≤ mass (g:ℝ) (histories d g β p φ P hp hφ hupper A T).states[i.val].1.1 := by
  exact SparseHistories.physical_invariant
    (fun t => step d g β p φ (P t) hp hφ hupper) (A,none)
    (fun s => 1 ≤ mass (g:ℝ) s.1) hA
    (fun t s hs j => step_mass d g β p φ (P t) hp hφ hupper s hg hunit hs j) T i

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI

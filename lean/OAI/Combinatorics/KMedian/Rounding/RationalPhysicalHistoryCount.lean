import Mathlib
import OAI.Combinatorics.KMedian.Rounding.RationalPhysicalCount
import OAI.Combinatorics.KMedian.Sparse.SparseBoundedCount

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {Δ : ℕ}

omit [Fintype F] in

theorem histories_count_tail (d : F → F → ℚ) (location : F → X)
    (hd : ∀ i j, dist (location i) (location j)=(d i j:ℝ))
    (g β p φ : ℚ) (P : ℕ → ℚ)
    (hp0 : 0 ≤ p) (hφ0 : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A : Finset (CopyState.Copy (F := F) Δ)) (T : ℕ)
    (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hp : 0 < (p:ℝ))
    (hφ : 0 < (φ:ℝ)) (hφ1 : (φ:ℝ) ≤ 1) (hβ : 0 < (β:ℝ))
    (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : ∀ t < T, 0 < (P t:ℝ)) (hP1 : ∀ t < T, (P t:ℝ) ≤ 1/2)
    (hA : 1 ≤ mass (g:ℝ) A) (hsmall : 8*(p:ℝ)*(Δ:ℝ) ≤ (φ:ℝ)*(g:ℝ)) :
    (histories d g β p φ P hp0 hφ0 hupper A T).expectation
      (fun z => if mass (g:ℝ) A+(T:ℝ)*(4/((g:ℝ)*(β:ℝ))) < mass (g:ℝ) z.1.1 then 1 else 0) ≤
      (T:ℝ)*(96*(Δ:ℝ)^2*(β:ℝ)/((p:ℝ)*(φ:ℝ)^2*(g:ℝ))) := by
  let κ := fun t => step (Δ := Δ) d g β p φ (P t) hp0 hφ0 hupper
  apply SparseHistories.count_tail_up_to κ (A,none)
    (fun s => mass (g:ℝ) s.1) (4/((g:ℝ)*(β:ℝ)))
    (96*(Δ:ℝ)^2*(β:ℝ)/((p:ℝ)*(φ:ℝ)^2*(g:ℝ))) T
  intro t ht i hi
  have hm := histories_mass d g β p φ P hp0 hφ0 hupper A t hg.le hunit hA ⟨i,hi⟩
  exact step_count_tail d location hd g β p φ (P t) hp0 hφ0 hupper
    (SparseHistories.tree κ (A,none) t).states[i].1
    hg hg1 hp hφ hφ1 hβ hunit (hP t ht) (hP1 t ht) hm hsmall

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI

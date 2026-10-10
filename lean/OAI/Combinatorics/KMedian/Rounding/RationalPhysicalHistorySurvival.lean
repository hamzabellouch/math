import Mathlib
import OAI.Combinatorics.KMedian.Rounding.RationalPhysicalSurvival
import OAI.Combinatorics.KMedian.Sparse.SparseBoundedSurvival

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential
variable {F X : Type} [LinearOrder F] [PseudoMetricSpace X] {Δ : ℕ}

theorem histories_survival (d₀ : F → F → ℚ) (location : F → X)
    (hd : ∀ i j, dist (location i) (location j)=(d₀ i j:ℝ))
    (g β p φ : ℚ) (P : ℕ → ℚ)
    (hp0 : 0 ≤ p) (hφ0 : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A S₀ : Finset (CopyState.Copy (F := F) Δ)) (T : ℕ)
    (x : ℕ → ℝ) (d : F → ℝ) {h : ℝ} (hprob : (p:ℝ)=2*h*(g:ℝ))
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : ∀ t < T, 0 < (P t:ℝ)) (hP1 : ∀ t < T, (P t:ℝ) ≤ 1/2)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hφ1 : (φ:ℝ) ≤ 1)
    (hA : 1 ≤ mass (g:ℝ) A)
    (hsmall : (2*h*(g:ℝ))*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ)) ≤ 1) (hSA : S₀ ⊆ A) :
    (histories d₀ g β p φ P hp0 hφ0 hupper A T).expectation
      (fun z => mass (g:ℝ) (replay g β x (fun (_ : Unit) => d) (fun _ => S₀) z ())) ≤
      (1-h/2)^T*mass (g:ℝ) S₀ := by
  let κ := fun t => step (Δ := Δ) d₀ g β p φ (P t) hp0 hφ0 hupper
  let V := fun (_ : ℕ) (z : SparseHistories.History (State F Δ g β)) =>
    mass (g:ℝ) (replay g β x (fun (_ : Unit) => d) (fun _ => S₀) z ())
  have hstep : ∀ t < T, ∀ i : Fin (SparseHistories.tree κ (A,none) t).length,
      (κ t (SparseHistories.tree κ (A,none) t).states[i.val].1).expectation
        (fun s => V (t+1) (SparseHistories.extend (SparseHistories.tree κ (A,none) t).states[i.val] s)) ≤
      (1-h/2)*V t (SparseHistories.tree κ (A,none) t).states[i.val] := by
    intro t ht i
    let z := (SparseHistories.tree κ (A,none) t).states[i.val]
    have hz : z.2.length=t := SparseHistories.past_length κ (A,none) t i
    have ha := histories_alive d₀ g β p φ P hp0 hφ0 hupper A t x
      (fun (_ : Unit) => d) (fun _ => S₀) (fun _ => hSA) i ()
    have hm := histories_mass d₀ g β p φ P hp0 hφ0 hupper A t hg.le hunit hA i
    have hs := step_survival d₀ location hd g β p φ (P t) hp0 hφ0 hupper z.1
      (replay g β x (fun (_ : Unit) => d) (fun _ => S₀) z ()) d hprob hg hunit
      (hP t ht) (hP1 t ht) hh0 hφ1 hm hsmall ha (x := x t)
    change (κ t z.1).expectation (fun s => V (t+1) (SparseHistories.extend z s)) ≤ (1-h/2)*V t z
    dsimp only [V]
    simp_rw [replay_extend,hz]
    exact hs
  have ht := SparseHistories.history_contraction κ (A,none) V (1-h/2)
    (by linarith only [hh1]) T hstep
  simpa only [V,κ,histories,replay,replayList,labels] using ht

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI

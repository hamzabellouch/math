import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.RelativeCopyNoiseFirst
import OAI.Combinatorics.TriangleRemoval.Embeddings.FixedEndpointPairInjective

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

open Classical in

theorem codegree_relative_noise_tail {n : ℕ} (u v : Fin n) (G : Graph n)
    (T : ℕ) (s : ℕ → ℝ) (c B : ℝ) (hc : 0 < c) (hB : 0 ≤ B)
    (hs : ∀ k ≤ T, 0 < s k) (hdec : ∀ k < T, s (k+1) ≤ s k)
    (hjump : ∀ k < T, 6/s (k+1) ≤ c) (r : ℝ) (hr : 0 < r) :
    pmfMean (historyLaw (PMF.pure G) (fun _ => step) T T)
      (fun ω => if ∃ j ≤ T,
        (∀ k < j, (currentCodegree (ω (historyIndex T k)) u v : ℝ) ≤ B*s k) ∧
        r ≤ |historyNoise (fun _ => step)
          (fun k H => (currentCodegree H u v : ℝ)/s k) T j ω| then 1 else 0) ≤
      2*(T+1 : ℝ)*Real.exp
        (-r^2/(4*(c*((currentCodegree G u v : ℝ)/s 0+B*relativeScaleBudget s T+r+c)+c*r))) := by
  have ht := triangle_relative_template_self_bounded_tail (wedgeEdges u v) G T
    (fun _ => 2) s c B hc hB hs hdec (fun _ _ => by norm_num)
    (fun k hk => by simpa only [show (3 : ℝ)*2 = 6 by norm_num] using hjump k hk) r hr
  simp_rw [← currentCodegree_copyCount] at ht
  apply le_trans _ ht
  apply pmfMean_mono
  intro ω _
  by_cases hex : ∃ j ≤ T,
      (∀ k < j, (currentCodegree (ω (historyIndex T k)) u v : ℝ) ≤ B*s k) ∧
      r ≤ |historyNoise (fun _ => step)
        (fun k H => (currentCodegree H u v : ℝ)/s k) T j ω|
  · obtain ⟨j,hj,hcounts,hcross⟩ := hex
    rw [ite_eq_left ⟨j,hj,hcounts,hcross⟩,
      ite_eq_left ⟨j,hj,wedge_pastRelativeCopyLoadsSafe u v T j ω,hcounts,hcross⟩]
  · rw [ite_eq_right hex]
    split <;> norm_num

end SharpTerminalLeave

end

end OAI

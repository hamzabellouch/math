import OAI.NumberTheory.JointDickman.Amplification.GraphEdgeSwap
import OAI.NumberTheory.JointDickman.Amplification.ArithmeticGraphCandidateCount

namespace OAI

/-! # Symmetry of the original arithmetic graph at its two endpoints -/

namespace JointDickman
open Finset Classical

theorem graphTripleSwap_condition {B T N n n' : ℕ} {j : ℤ} {g : GraphCoefficientTriple}
    (hg : g ∈ arithmeticGraphTriples B T) (he : (n : ℤ)+j = n') :
    (graphTripleLag (graphTripleSwap g) = -j ∧ n' ∈ graphTripleEdges N (graphTripleSwap g)) ↔
      (graphTripleLag g = j ∧ n ∈ graphTripleEdges N g) := by
  rw [graphTripleSwap_lag hg,neg_inj]
  constructor
  · rintro ⟨hlag,hn⟩
    have hs := (graphTripleSwap_edge (graphTripleSwap_mem hg) hn).1
    have hback : ((n' : ℤ)+graphTripleLag (graphTripleSwap g)).toNat = n := by
      rw [graphTripleSwap_lag hg,hlag]
      omega
    rw [hback,graphTripleSwap_involutive g] at hs
    exact ⟨hlag,hs⟩
  · rintro ⟨hlag,hn⟩
    have hs := (graphTripleSwap_edge hg hn).1
    have hforward : ((n : ℤ)+graphTripleLag g).toNat = n' := by rw [hlag,he,Int.toNat_natCast]
    rw [hforward] at hs
    exact ⟨hlag,hs⟩

theorem rawArithmeticGraphKernel_reverse {B L T N n n' : ℕ} {τ C : ℝ} {j : ℤ}
    (he : (n : ℤ)+j = n') :
    rawArithmeticGraphKernel B L τ C T N (-j) n' =
      rawArithmeticGraphKernel B L τ C T N j n := by
  unfold rawArithmeticGraphKernel
  symm
  apply sum_bij (fun g _ => graphTripleSwap g)
  · intro g hg
    exact graphTripleSwap_mem hg
  · intro g _ g' _ heq
    exact graphTripleSwap_involutive.injective heq
  · intro g hg
    exact ⟨graphTripleSwap g,graphTripleSwap_mem hg,graphTripleSwap_involutive g⟩
  · intro g hg
    have hc := graphTripleSwap_condition (N := N) hg he
    by_cases hh : graphTripleLag g = j ∧ n ∈ graphTripleEdges N g
    · have hs := hc.mpr hh
      rw [ite_eq_left hh,ite_eq_left hs]
      have hw := graphTripleSwap_weight (L := L) (τ := τ) (C := C) hg hh.2
      have hn : ((n : ℤ)+graphTripleLag g).toNat = n' := by rw [hh.1,he,Int.toNat_natCast]
      rw [hn] at hw
      exact hw.symm
    · rw [ite_eq_right hh,ite_eq_right (fun h => hh (hc.mp h))]

theorem rawArithmeticGraphKernel_block_reverse {B L T M N u : ℕ} {τ C : ℝ}
    (i k : Fin M) :
    rawArithmeticGraphKernel B L τ C T N ((i.val : ℤ)-k.val) (u+(k.val+1)) =
      rawArithmeticGraphKernel B L τ C T N ((k.val : ℤ)-i.val) (u+(i.val+1)) := by
  have he : ((u+(i.val+1) : ℕ) : ℤ)+((k.val : ℤ)-i.val) = (u+(k.val+1) : ℕ) := by
    push_cast
    ring
  simpa only [neg_sub] using rawArithmeticGraphKernel_reverse (B := B) (L := L)
    (T := T) (N := N) (τ := τ) (C := C) he

end JointDickman

end OAI

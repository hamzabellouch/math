import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.HistoryCompensator

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

noncomputable def centeredCodegreeNeighborSum {n : ℕ} (G : Graph n)
    (u v : Fin n) (s : ℝ) : ℝ :=
  ∑ w ∈ commonNeighbors G u v,
    ((currentCodegree G u w : ℝ)+currentCodegree G v w-2*s)

lemma codegree_hazard_centering {n : ℕ} (G : Graph n) (u v : Fin n) (s : ℝ) :
    (∑ w ∈ commonNeighbors G u v,
      ((currentCodegree G u w : ℝ)+currentCodegree G v w-if {u,v} ∈ G then 1 else 0)) =
    (2*s-if {u,v} ∈ G then 1 else 0)*(currentCodegree G u v : ℝ)+
      centeredCodegreeNeighborSum G u v s := by
  classical
  have he : (∑ w ∈ commonNeighbors G u v,
      ((currentCodegree G u w : ℝ)+currentCodegree G v w-if {u,v} ∈ G then 1 else 0)) =
      (∑ _w ∈ commonNeighbors G u v, (2*s-if {u,v} ∈ G then 1 else 0))+
        centeredCodegreeNeighborSum G u v s := by
    rw [centeredCodegreeNeighborSum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [he]
  simp only [Finset.sum_const,nsmul_eq_mul,currentCodegree]
  ring

theorem normalized_codegree_centered_drift {n : ℕ} {G : Graph n}
    (hG : G ⊆ completeGraph n) (u v : Fin n) (huv : u ≠ v) (s t : ℝ) :
    pmfMean (step G) (fun H => (currentCodegree H u v : ℝ)/t)-
      (currentCodegree G u v : ℝ)/s =
    (currentCodegree G u v : ℝ)*(1/t-1/s)-
      ((2*s-if {u,v} ∈ G then 1 else 0)*(currentCodegree G u v : ℝ)+
        centeredCodegreeNeighborSum G u v s)/((triangles G).card*t) := by
  by_cases hQ : (triangles G).Nonempty
  · have hd := step_mean_codegree hG hQ u v huv
    rw [codegree_hazard_centering G u v s] at hd
    simp only [div_eq_mul_inv,pmfMean_mul_const] at hd ⊢
    rw [hd,mul_inv_rev]
    ring
  · have hzero : triangles G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hQ
    rw [step,dite_eq_right hQ,pmfMean_pure,hzero,Finset.card_empty,Nat.cast_zero,zero_mul,div_zero]
    ring

theorem prefix_codegree_centered_drift {n : ℕ} {G : Graph n}
    (hG : G ⊆ completeGraph n) (u v : Fin n) (huv : u ≠ v) (k : ℕ) :
    pmfMean (step G) (prefixNormalizedCodegree u v (k+1))-
      prefixNormalizedCodegree u v k G =
    (currentCodegree G u v : ℝ)*(1/earlyTemplateScale 1 2 n (k+1)-1/earlyTemplateScale 1 2 n k)-
      ((2*earlyTemplateScale 1 2 n k-if {u,v} ∈ G then 1 else 0)*
        (currentCodegree G u v : ℝ)+
        centeredCodegreeNeighborSum G u v (earlyTemplateScale 1 2 n k))/
      ((triangles G).card*earlyTemplateScale 1 2 n (k+1)) :=
  normalized_codegree_centered_drift hG u v huv _ _

end SharpTerminalLeave

end

end OAI

import Mathlib
import OAI.Combinatorics.ThinTrees.Normalization.Descent

namespace OAI

/-! Normalization packing. -/

section

namespace AlgorithmicThinTrees.Normalization
open Matrix Finset StrongThinTree
open scoped MatrixOrder

lemma covariance_posSemidef {E I : Type*} [Fintype E] [Fintype I]
    (v : E → I → ℝ) (a : E → ℝ) (ha : ∀e, 0 ≤ a e) : (covariance v a).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro e _
  have h : (vecMulVec (v e) (v e)).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (v e)
  exact h.smul (ha e)

lemma covariance_embedding {E J I : Type*} [Fintype E] [DecidableEq E]
    [Fintype J] [DecidableEq J] [Fintype I]
    (f : J ↪ E) (v : E → I → ℝ) (a : E → ℝ) :
    covariance v a=covariance (v ∘ f) (a ∘ f)+
      ∑e ∈ univ \ univ.map f, a e • vecMulVec (v e) (v e) := by
  unfold covariance
  simp only [Function.comp_apply]
  rw [←Finset.sum_map (f := fun e => a e • vecMulVec (v e) (v e))]
  exact (Finset.sum_sdiff (f := fun e => a e • vecMulVec (v e) (v e)) (subset_univ (univ.map f))).symm.trans (add_comm ..)

structure ContainedPacking {E : Type*} {d : ℕ} (v : E → Fin d → ℝ) (q : ℕ) where
  positive : 0 < q
  edges : (Fin q × Fin d) ↪ E
  invertible : ∀t, IsUnit (Matrix.of (fun i j => v (edges (t,j)) i))
  determinant : ∀t, 1 ≤ (Matrix.det (fun i j => v (edges (t,j)) i))^2

namespace ContainedPacking
variable {E : Type*} [Fintype E] [DecidableEq E] {q d : ℕ}
variable {v : E → Fin d → ℝ} (B : ContainedPacking v q)

noncomputable def full : BasisPacking (v ∘ B.edges) q :=
  ⟨B.positive,Equiv.refl _,B.invertible,B.determinant⟩

include B
lemma extra_posSemidef (a : E → ℝ) (ha : ∀e, 0 ≤ a e) :
    (∑e ∈ univ \ univ.map B.edges, a e • vecMulVec (v e) (v e)).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro e _
  have h : (vecMulVec (v e) (v e)).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (v e)
  exact h.smul (ha e)

lemma covariance_posDef (a : E → ℝ) (ha : ∀e, 0 < a e) : (covariance v a).PosDef := by
  rw [covariance_embedding B.edges v a]
  exact (B.full.covariance_posDef (a ∘ B.edges) (fun e => ha _)).add_posSemidef
    (B.extra_posSemidef a (fun e => (ha e).le))

lemma objective_nonneg (a : E → ℝ) (ha : ∀e, 0 < a e) (ha1 : ∀e, a e ≤ 1) :
    0 ≤ objective q v a := by
  have hb := B.full.objective_nonneg (a ∘ B.edges) (fun e => ha _)
  have hpd := B.full.covariance_posDef (a ∘ B.edges) (fun e => ha _)
  have hd : (covariance (v ∘ B.edges) (a ∘ B.edges)).det ≤ (covariance v a).det := by
    rw [covariance_embedding B.edges v a]
    exact det_le_det_add_of_posSemidef hpd (B.extra_posSemidef a (fun e => (ha e).le))
  have hl := Real.log_le_log hpd.det_pos hd
  have hlogs : (∑e, Real.log (a e)) ≤ ∑j, Real.log (a (B.edges j)) := by
    rw [←Finset.sum_map (f := fun e => Real.log (a e))]
    have hsum := Finset.sum_sdiff (f := fun e => Real.log (a e)) (subset_univ (univ.map B.edges))
    have hnonpos : ∑e ∈ univ \ univ.map B.edges, Real.log (a e) ≤ 0 :=
      sum_nonpos (fun e _ => Real.log_nonpos (ha e).le (ha1 e))
    linarith only [hsum,hnonpos]
  have hdiv := div_le_div_of_nonneg_right hlogs (Nat.cast_nonneg q : (0:ℝ)≤q)
  unfold objective at hb ⊢
  exact hb.trans (sub_le_sub hl hdiv)

lemma initial_gap (hsize : ∀e, v e ⬝ᵥ v e ≤ 2) :
    objective q v (fun _ => 1) ≤ 2*Fintype.card E := by
  have hh := logdet_le_trace (B.covariance_posDef (fun _ => 1) (by simp))
  simp only [objective,Real.log_one,sum_const_zero,zero_div,sub_zero]
  apply hh.trans
  simp only [covariance,one_smul,Matrix.trace_sum,Matrix.trace_vecMulVec]
  calc
    _ ≤ ∑_e : E, (2:ℝ) := sum_le_sum (fun e _ => hsize e)
    _ = _ := by simp [mul_comm]

end ContainedPacking
end AlgorithmicThinTrees.Normalization
end

end OAI

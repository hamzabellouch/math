import Mathlib
import OAI.Analysis.Commutator.DerivationCyclicColumns
import OAI.Analysis.Commutator.MainMatrix

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace Topology

open Filter

namespace Kadison.DerivationColumns

open CyclicColumns CyclicDecomposition

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
  (D : A →L[ℂ] (H →L[ℂ] H))
  (hD : ∀ a b,D (a*b)=(D a).comp (σ b)+(σ a).comp (D b))
  (Q : Decomposition σ.range)

lemma finite_matrix_identity (s : Finset Q.I) (h : ℕ) (X : CStarMatrix (Fin h) (Fin h) A) :
    diagonalAmplification h (finiteImplementer σ D hD Q s)*matrixRepresentation σ X-
      matrixRepresentation σ X*diagonalAmplification h (finiteImplementer σ D hD Q s)=
    matrixAction (fun i j => D (X i j))*diagonalAmplification h (finiteProjection σ Q s) := by
  ext x i
  change (diagonalAmplification h (finiteImplementer σ D hD Q s)
    (matrixAction (fun i j => σ (X i j)) x)) i-
    (matrixAction (fun i j => σ (X i j)) (diagonalAmplification h (finiteImplementer σ D hD Q s) x)) i=_
  simp only [mul_apply_eq_comp,diagonalAmplification_apply,matrixAction_apply,map_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg (fun L : H →L[ℂ] H => L (x j)) (finite_column_identity σ D hD Q s (X i j))

omit [PartialOrder A] [StarOrderedRing A] in
lemma finiteProjection_strong (h : ℕ) (x : PiLp 2 (fun _ : Fin h => H)) :
    Tendsto (fun s : Finset Q.I => diagonalAmplification h (finiteProjection σ Q s) x) atTop (𝓝 x) := by
  have ht : Tendsto (fun s : Finset Q.I => fun i : Fin h => finiteProjection σ Q s (x i))
      atTop (𝓝 (fun i : Fin h => x i)) := tendsto_pi_nhds.mpr (fun i => Q.strong (x i))
  have hconv := ((PiLp.homeomorph 2 (fun _ : Fin h => H)).symm.continuous.tendsto
    (fun i : Fin h => x i)).comp ht
  have he (s : Finset Q.I) : (PiLp.homeomorph 2 (fun _ : Fin h => H)).symm
      (fun i => finiteProjection σ Q s (x i))=diagonalAmplification h (finiteProjection σ Q s) x := by
    ext i
    rfl
  have hx : (PiLp.homeomorph 2 (fun _ : Fin h => H)).symm (fun i => x i)=x := by
    ext i
    rfl
  simpa only [Function.comp_def,he,hx] using hconv

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_le_of_finite_columns (h : ℕ) (T : PiLp 2 (fun _ : Fin h => H) →L[ℂ] PiLp 2 (fun _ : Fin h => H))
    {c : ℝ} (hc : 0≤c)
    (hT : ∀ s : Finset Q.I,‖T*diagonalAmplification h (finiteProjection σ Q s)‖≤c) :
    ‖T‖≤c := by
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro x
  have ht := (T.continuous.tendsto x).comp (finiteProjection_strong σ Q h x)
  apply le_of_tendsto ht.norm
  apply Filter.Eventually.of_forall
  intro s
  exact ((T*diagonalAmplification h (finiteProjection σ Q s)).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (hT s) (norm_nonneg x))

end Kadison.DerivationColumns

end

end
end

end OAI

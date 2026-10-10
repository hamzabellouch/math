import Mathlib
import OAI.Analysis.Commutator.CyclicMatrix

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.CyclicColumns

variable {A H ι κ : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [Fintype κ]

def reindexHilbert (e : ι ≃ κ) : PiLp 2 (fun _ : ι => H) ≃ₗᵢ[ℂ] PiLp 2 (fun _ : κ => H) where
  toFun x := WithLp.toLp 2 (fun j => x (e.symm j))
  invFun x := WithLp.toLp 2 (fun i => x (e i))
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp
  map_add' x y := by ext i; rfl
  map_smul' c x := by ext i; rfl
  norm_map' x := by
    rw [PiLp.norm_eq_of_L2,PiLp.norm_eq_of_L2]
    congr 1
    exact Fintype.sum_equiv e.symm _ _ (fun j => rfl)

lemma matrixAction_reindex (e : ι ≃ κ) (X : ι → ι → H →L[ℂ] H) :
    matrixAction (fun i j => X (e.symm i) (e.symm j))=
    (reindexHilbert (H:=H) e).conjStarAlgEquiv (matrixAction X) := by
  ext x i
  rw [matrixAction_apply,LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  change ∑ j : κ,X (e.symm i) (e.symm j) (x j)=
    matrixAction X (WithLp.toLp 2 (fun j => x (e j))) (e.symm i)
  rw [matrixAction_apply]
  exact Fintype.sum_equiv e.symm _ _ (fun j => by simp)

lemma matrixAction_reindex_norm (e : ι ≃ κ) (X : ι → ι → H →L[ℂ] H) :
    ‖matrixAction (fun i j => X (e.symm i) (e.symm j))‖=‖matrixAction X‖ := by
  rw [matrixAction_reindex]
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply,
    ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

lemma matrix_bound_of_fin (D : A → H →L[ℂ] H) {c : ℝ} (hc : 0≤c)
    (hfin : ∀ h : ℕ,1≤h → ∀ X : CStarMatrix (Fin h) (Fin h) A,
      ‖matrixAction (fun i j => D (X i j))‖≤c*‖X‖)
    (X : CStarMatrix ι ι A) : ‖matrixAction (fun i j => D (X i j))‖≤c*‖X‖ := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hi =>
    have hz : matrixAction (fun i j => D (X i j))=0 := by ext x i; exact isEmptyElim i
    rw [hz,norm_zero]
    exact mul_nonneg hc (norm_nonneg X)
  | inr hi =>
    let e := Fintype.equivFin ι
    have hn := hfin (Fintype.card ι) (Fintype.card_pos_iff.mpr hi)
      (CStarMatrix.reindexₐ ℂ A e X)
    have he : matrixAction (fun i j => D ((CStarMatrix.reindexₐ ℂ A e X) i j))=
        matrixAction (fun i j => D (X (e.symm i) (e.symm j))) := rfl
    rw [he,matrixAction_reindex_norm e (fun i j => D (X i j)),
      StarAlgEquiv.norm_map (CStarMatrix.reindexₐ ℂ A e) X] at hn
    exact hn

end Kadison.CyclicColumns

end

end
end

end OAI

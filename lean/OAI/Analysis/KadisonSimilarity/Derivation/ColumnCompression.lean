import OAI.Analysis.KadisonSimilarity.Derivation.CyclicApproximation

namespace OAI

/-! Contractive extraction of one column of a C-star matrix. -/
noncomputable section
namespace KadisonSimilarity

variable {A : Type*}

/-- Extract a column without changing the number of rows. -/
def cstarColumn {n : ℕ} (X : CStarMatrix (Fin n) (Fin n) A) (j : Fin n) :
    CStarMatrix (Fin n) (Fin 1) A :=
  CStarMatrix.ofMatrix (fun i _ => X i j)

@[simp] theorem cstarColumn_apply {n : ℕ} (X : CStarMatrix (Fin n) (Fin n) A)
    (j i : Fin n) (k : Fin 1) : cstarColumn X j i k = X i j := rfl

variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A coordinate projection on the standard C-star module is contractive. -/
theorem norm_cstarColumn_le {n : ℕ} (X : CStarMatrix (Fin n) (Fin n) A) (j : Fin n) :
    ‖cstarColumn X j‖ ≤ ‖X‖ := by
  classical
  rw [CStarMatrix.norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg X)
  intro v
  have he : CStarMatrix.toCLM (cstarColumn X j) v =
      (WithCStarModule.equiv A (Fin 1 → A)).symm (Pi.single (0 : Fin 1) (CStarMatrix.toCLM X v j)) := by
    apply (WithCStarModule.equiv A (Fin 1 → A)).injective
    funext k
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    change (CStarMatrix.toCLM (cstarColumn X j) v) 0 = (CStarMatrix.toCLM X v) j
    simp only [CStarMatrix.toCLM_apply_eq_sum, cstarColumn_apply,
      WithCStarModule.equiv_symm_pi_apply]
  rw [he, WithCStarModule.norm_single]
  exact (WithCStarModule.norm_apply_le_norm _ j).trans (X.toCLM.le_opNorm v)

end KadisonSimilarity

end

end OAI

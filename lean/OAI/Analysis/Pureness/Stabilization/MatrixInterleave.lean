import OAI.Analysis.Pureness.Stabilization.MatrixSystem

namespace OAI
noncomputable section
open scoped CStarAlgebra
namespace CuntzTrace
variable {A : Type*} [NonUnitalCStarAlgebra A]

private def interleaveEntry {n : ℕ} (P : FinMatrix A n × FinMatrix A n)
    (i j : Fin n × Fin 2) : A :=
  if i.2 = j.2 then if i.2 = 0 then P.1 i.1 j.1 else P.2 i.1 j.1 else 0

def matrixInterleaveRaw (n : ℕ) :
    (FinMatrix A n × FinMatrix A n) →⋆ₙₐ[ℂ] CStarMatrix (Fin n × Fin 2) (Fin n × Fin 2) A where
  toFun P := CStarMatrix.ofMatrix (interleaveEntry P)
  map_zero' := by
    apply CStarMatrix.ext; rintro ⟨i,r⟩ ⟨j,s⟩
    change interleaveEntry (0 : FinMatrix A n × FinMatrix A n) (i,r) (j,s) = 0
    simp [interleaveEntry]
  map_add' P Q := by
    apply CStarMatrix.ext; rintro ⟨i,r⟩ ⟨j,s⟩
    change interleaveEntry (P + Q) (i,r) (j,s) =
      interleaveEntry P (i,r) (j,s) + interleaveEntry Q (i,r) (j,s)
    fin_cases r <;> fin_cases s <;> simp [interleaveEntry]
  map_mul' P Q := by
    apply CStarMatrix.ext; rintro ⟨i,r⟩ ⟨j,s⟩
    change interleaveEntry (P * Q) (i,r) (j,s) =
      ∑ k, interleaveEntry P (i,r) k * interleaveEntry Q k (j,s)
    fin_cases r <;> fin_cases s <;>
      simp [interleaveEntry, CStarMatrix.mul_apply,Fintype.sum_prod_type]
  map_smul' c P := by
    apply CStarMatrix.ext; rintro ⟨i,r⟩ ⟨j,s⟩
    change interleaveEntry (c • P) (i,r) (j,s) = c • interleaveEntry P (i,r) (j,s)
    fin_cases r <;> fin_cases s <;> simp [interleaveEntry]
  map_star' P := by
    apply CStarMatrix.ext; rintro ⟨i,r⟩ ⟨j,s⟩
    change interleaveEntry (star P) (i,r) (j,s) = star (interleaveEntry P (j,s) (i,r))
    fin_cases r <;> fin_cases s <;> simp [interleaveEntry, CStarMatrix.star_apply]

lemma matrixInterleaveRaw_injective (n : ℕ) : Function.Injective (matrixInterleaveRaw (A := A) n) := by
  intro P Q h
  apply Prod.ext
  · apply CStarMatrix.ext; intro i j
    have hh := congrArg (fun M : CStarMatrix (Fin n × Fin 2) (Fin n × Fin 2) A => M (i,0) (j,0)) h
    change interleaveEntry P (i,0) (j,0) = interleaveEntry Q (i,0) (j,0) at hh
    simpa [interleaveEntry] using hh
  · apply CStarMatrix.ext; intro i j
    have hh := congrArg (fun M : CStarMatrix (Fin n × Fin 2) (Fin n × Fin 2) A => M (i,1) (j,1)) h
    change interleaveEntry P (i,1) (j,1) = interleaveEntry Q (i,1) (j,1) at hh
    simpa [interleaveEntry] using hh

def matrixInterleave (n : ℕ) : (FinMatrix A n × FinMatrix A n) →⋆ₙₐ[ℂ] FinMatrix A (n*2) :=
  (CStarMatrix.reindexₐ ℂ A finProdFinEquiv).toNonUnitalStarAlgHom.comp (matrixInterleaveRaw n)

lemma matrixInterleave_injective (n : ℕ) : Function.Injective (matrixInterleave (A := A) n) :=
  (CStarMatrix.reindexₐ ℂ A finProdFinEquiv).injective.comp (matrixInterleaveRaw_injective n)

section
variable [PartialOrder A] [StarOrderedRing A]

theorem matrixInterleave_isometry (n : ℕ) : Isometry (matrixInterleave (A := A) n) :=
  NonUnitalStarAlgHom.isometry _ (matrixInterleave_injective n)

@[simp] theorem matrixInterleave_norm (n : ℕ) (P : FinMatrix A n × FinMatrix A n) :
    ‖matrixInterleave n P‖ = max ‖P.1‖ ‖P.2‖ :=
  NonUnitalStarAlgHom.norm_map _ (matrixInterleave_injective n) P

end

@[simp] theorem matrixInterleave_entry (n : ℕ) (P : FinMatrix A n × FinMatrix A n)
    (i j : Fin n) (r s : Fin 2) :
    matrixInterleave n P (finProdFinEquiv (i,r)) (finProdFinEquiv (j,s)) =
      if r = s then if r = 0 then P.1 i j else P.2 i j else 0 := by
  change interleaveEntry P (finProdFinEquiv.symm (finProdFinEquiv (i,r)))
    (finProdFinEquiv.symm (finProdFinEquiv (j,s))) = _
  simp [interleaveEntry]
end CuntzTrace

end

end OAI

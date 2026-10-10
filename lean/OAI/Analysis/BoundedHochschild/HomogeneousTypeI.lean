import OAI.Analysis.BoundedHochschild.SignedMatrixUnitaries
import OAI.Analysis.BoundedHochschild.CentralBlockSpans
import OAI.Analysis.BoundedHochschild.TypeICentralSupport

namespace OAI

/-! The abelian commutant of a finite homogeneous type I matrix system. -/

noncomputable section

namespace HochschildMatrixSystems
namespace MatrixSystem

variable {M : Type*} [CStarAlgebra M] {n : ℕ} (E : MatrixSystem M n)

lemma commutant_central (hcomm : ∀ a b : E.commutant, Commute a b)
    (a : E.commutant) (x : M) : (a : M) * x = x * (a : M) := by
  have hc : Commute (a : M) x := by
    rw [← E.reconstruct x]
    apply Commute.sum_right
    intro i _
    apply Commute.sum_right
    intro j _
    exact (a.property i j).mul_right (show Commute (a : M) (E.coefficient i j x) from
      congrArg (fun z : E.commutant => (z : M))
        (hcomm a ⟨_, E.coefficient_mem i j x⟩).eq)
  exact hc.eq

lemma commutant_commutative_of_abelian_diagonal (i : Fin n)
    (hi : FinitePathMain.AbelianProjection (E.entry i i)) :
    ∀ a b : E.commutant, Commute a b := by
  intro a b
  have hcut (a : E.commutant) : E.entry i i * (a : M) * E.entry i i =
      E.entry i i * (a : M) := by
    rw [mul_assoc, (a.property i i).eq, ← mul_assoc, (E.diagonal_proj i).isIdempotentElem.eq]
  have hprod (a b : E.commutant) :
      (E.entry i i * (a : M)) * (E.entry i i * (b : M)) =
        E.entry i i * ((a : M) * (b : M)) := by
    calc
      _ = (E.entry i i * (a : M) * E.entry i i) * (b : M) := by noncomm_ring
      _ = _ := by rw [hcut]; noncomm_ring
  have h := hi.2 (a : M) (b : M)
  change (E.entry i i * (a : M) * E.entry i i) *
      (E.entry i i * (b : M) * E.entry i i) =
    (E.entry i i * (b : M) * E.entry i i) *
      (E.entry i i * (a : M) * E.entry i i) at h
  simp only [hcut, hprod] at h
  have he := congrArg (E.coefficient i i) h
  change E.coefficient i i (E.entry i i * ((a * b : E.commutant) : M)) =
    E.coefficient i i (E.entry i i * ((b * a : E.commutant) : M)) at he
  rw [E.coefficient_of_commutant i (a * b).property,
    E.coefficient_of_commutant i (b * a).property] at he
  exact Subtype.ext he

end MatrixSystem
end HochschildMatrixSystems

end

end OAI

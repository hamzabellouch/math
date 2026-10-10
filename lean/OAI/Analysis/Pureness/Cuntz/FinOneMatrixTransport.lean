import OAI.Analysis.Pureness.Cuntz.MatrixTraceCorrespondence
import OAI.Analysis.Pureness.Quasitrace.QuasitraceFamily

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
variable {A : Type*} [CStarAlgebra A]

lemma scalarMatrixHom_finOne_bijective :
    Function.Bijective (scalarMatrixHom (ι := Fin 1) (A := A)) := by
  constructor
  · intro a b h
    have he := congrArg (fun M : FinMatrix A 1 => M 0 0) h
    exact he
  · intro M
    refine ⟨M 0 0,?_⟩
    apply CStarMatrix.ext
    intro i j
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst i; subst j
    rfl

def scalarFinOneEquiv : A ≃⋆ₐ[ℂ] FinMatrix A 1 :=
  StarAlgEquiv.ofBijective (scalarMatrixHom (ι := Fin 1)) scalarMatrixHom_finOne_bijective

lemma scalarFinOneEquiv_apply (a : A) :
    scalarFinOneEquiv a = scalarMatrixHom (ι := Fin 1) a := rfl

lemma scalarFinOneEquiv_symm_apply (M : FinMatrix A 1) :
    scalarFinOneEquiv.symm M = M 0 0 := by
  obtain ⟨a,rfl⟩ := scalarMatrixHom_finOne_bijective.2 M
  change scalarFinOneEquiv.symm (scalarFinOneEquiv a) = _
  rw [StarAlgEquiv.symm_apply_apply]
  rfl
end CuntzPureness

end

end OAI

import Mathlib
import OAI.Analysis.Commutator.AtomicCoefficients
import OAI.Analysis.Commutator.AtomicDecomposition
import OAI.Analysis.Commutator.MinimalCorner

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.AtomicFactor.Decomposition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} {p : H →L[ℂ] H} (D : Decomposition M p)

theorem finite_dimensional [Finite D.I] (hp : IsMinimalProjection M p) :
    FiniteDimensional ℂ M := by
  classical
  let := Fintype.ofFinite D.I
  let K : Submodule ℂ (H →L[ℂ] H) := Submodule.span ℂ {p}
  have hcoeff (a : M) (ij : D.I×D.I) : star (D.v ij.1)*(a:H →L[ℂ] H)*D.v ij.2∈K := by
    have hpa : p*star (D.v ij.1)=star (D.v ij.1) := by
      simpa only [star_mul,hp.2.1.isSelfAdjoint.star_eq] using congrArg star (D.source ij.1)
    obtain ⟨z,hz⟩ := corner_scalar M hp
      (M.mul_mem (M.mul_mem (M.star_mem' (D.mem ij.1)) a.property) (D.mem ij.2))
      (by rw [←mul_assoc,←mul_assoc,hpa])
      (by rw [mul_assoc,D.source])
    rw [hz]
    exact K.smul_mem z (Submodule.subset_span (Set.mem_singleton p))
  let L : M →ₗ[ℂ] ((D.I×D.I) → K) :=
    { toFun := fun a ij => ⟨star (D.v ij.1)*(a:H →L[ℂ] H)*D.v ij.2,hcoeff a ij⟩
      map_add' := by
        intro a b
        funext ij
        apply Subtype.ext
        change star (D.v ij.1)*((a:H →L[ℂ] H)+(b:H →L[ℂ] H))*D.v ij.2=
          star (D.v ij.1)*(a:H →L[ℂ] H)*D.v ij.2+star (D.v ij.1)*(b:H →L[ℂ] H)*D.v ij.2
        rw [mul_add,add_mul]
      map_smul' := by
        intro c a
        funext ij
        apply Subtype.ext
        change star (D.v ij.1)*(c • (a:H →L[ℂ] H))*D.v ij.2=
          c • (star (D.v ij.1)*(a:H →L[ℂ] H)*D.v ij.2)
        rw [mul_smul_comm,smul_mul_assoc] }
  apply FiniteDimensional.of_injective L
  intro a b hab
  apply Subtype.ext
  apply D.eq_of_coefficients_eq
  intro i j
  exact congrArg (fun f : (D.I×D.I) → K => ((f (i,j)):H →L[ℂ] H)) hab

end Kadison.AtomicFactor.Decomposition

end

end
end

end OAI

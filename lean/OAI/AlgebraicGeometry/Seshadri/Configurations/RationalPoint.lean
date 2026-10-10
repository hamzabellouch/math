import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.PolynomialCharts

namespace OAI

section
noncomputable section
                                       
section

namespace MaximalSeshadri.ProjectiveBertini
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra

lemma exists_point_finite_type {K R : Type} [Field K] [IsAlgClosed K]
    [CommRing R] [Nontrivial R] [Algebra K R] [Algebra.FiniteType K R] :
    Nonempty (R →ₐ[K] K) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  let : m.IsMaximal := hm
  let : Field (R ⧸ m) := Ideal.Quotient.field m
  let : Module.Finite K (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing K _
  exact ⟨(IsAlgClosed.lift : (R ⧸ m) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K m)⟩

lemma linearEquation_ne_zero {K σ : Type} [Field K] [Fintype σ]
    (v : σ → K) (i : σ) (hi : v i ≠ 0) : linearEquation v ≠ 0 := by
  classical
  intro h
  have := congrArg (MvPolynomial.aeval (Pi.single i (1 : K))) h
  simp [linearEquation, Pi.single_apply, Finset.sum_ite_eq', hi] at this

end
end MaximalSeshadri.ProjectiveBertini
end


end
end

end OAI

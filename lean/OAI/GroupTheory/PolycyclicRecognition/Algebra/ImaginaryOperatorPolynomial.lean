import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexCartanJordan
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.RingTheory.Adjoin.Polynomial.Basic

namespace OAI

/-! # The imaginary Cartan operator preserves the triangular flag

Polynomial interpolation on the finite set of Cartan eigenvalues realizes
the imaginary part as a polynomial in the Jordan semisimple operator.
-/

noncomputable section
namespace PolycyclicRecognition.ComplexCartan
open LieAlgebra LieModule Module

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]

/-- Interpolation is on eigenvalues, so coincident weights cause no choice
or distinctness assumption. -/
theorem imaginaryOperator_polynomial (h : H) :
    ∃ p : Polynomial ℂ, Polynomial.aeval (semisimpleOperator H h) p = imaginaryOperator H h := by
  classical
  let s : Finset ℂ := Finset.univ.image (fun χ : Weight ℂ H L => χ h)
  let p : Polynomial ℂ := Lagrange.interpolate s id imaginaryPart
  have hp (χ : Weight ℂ H L) : p.eval (χ h) = imaginaryPart (χ h) := by
    exact Lagrange.eval_interpolate_at_node imaginaryPart (fun _ _ _ _ he => he)
      (Finset.mem_image.mpr ⟨χ,Finset.mem_univ _,rfl⟩)
  refine ⟨p,?_⟩
  apply LinearMap.ext
  intro x
  apply root_induction H (x := x)
  · intro χ v hv
    rw [Module.End.aeval_apply_of_mem_apply_eq_smul (semisimpleOperator_apply H h χ hv),
      imaginaryOperator_apply H h χ hv,hp]
  · simp
  · intro v w hv hw
    simp only [map_add,hv,hw]

/-- The imaginary part is a polynomial in the original Cartan adjoint
operator, through its Jordan semisimple part. -/
theorem imaginaryOperator_adjoin (h : H) :
    imaginaryOperator H h ∈ Algebra.adjoin ℂ {ad ℂ L (h : L)} := by
  obtain ⟨p,hp⟩ := imaginaryOperator_polynomial H h
  have hle : Algebra.adjoin ℂ {semisimpleOperator H h} ≤
      Algebra.adjoin ℂ {ad ℂ L (h : L)} := by
    apply Algebra.adjoin_le
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact (semisimpleOperator_jordan H h).1
  rw [← hp]
  exact hle (p.aeval_mem_adjoin_singleton ℂ (semisimpleOperator H h))

/-- The imaginary semisimple operator preserves the same upper triangular
flag as the original adjoint action. -/
theorem imaginaryOperator_upper {n : ℕ} (b : Basis (Fin n) ℂ L) (h : H)
    (hh : (LinearMap.toMatrix b b (ad ℂ L (h : L))).IsUpperTriangular) :
    (LinearMap.toMatrix b b (imaginaryOperator H h)).IsUpperTriangular := by
  let F := LinearMap.toMatrixAlgEquiv b
  let A := Matrix.blockTriangularSubalgebra ℂ ℂ (id : Fin n → Fin n)
  have hle : Algebra.adjoin ℂ {ad ℂ L (h : L)} ≤ A.comap F.toAlgHom := by
    apply Algebra.adjoin_le
    intro f hf
    obtain rfl := Set.mem_singleton_iff.mp hf
    exact hh
  exact hle (imaginaryOperator_adjoin H h)

end PolycyclicRecognition.ComplexCartan

end

end OAI

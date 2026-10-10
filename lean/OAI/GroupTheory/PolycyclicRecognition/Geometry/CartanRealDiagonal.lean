import OAI.GroupTheory.PolycyclicRecognition.Algebra.ImaginaryOperatorPolynomial
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexTriangularPolynomial

namespace OAI

/-! # Removing the imaginary Cartan eigenvalues on the original flag -/

noncomputable section
namespace PolycyclicRecognition.ComplexCartan
open LieAlgebra LieModule Module

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]

theorem semisimpleOperator_diagonal {n : ℕ} (b : Basis (Fin n) ℂ L) (h : H)
    (hh : (LinearMap.toMatrix b b (ad ℂ L (h : L))).IsUpperTriangular) (i : Fin n) :
    LinearMap.toMatrix b b (semisimpleOperator H h) i i =
      LinearMap.toMatrix b b (ad ℂ L (h : L)) i i := by
  let F := LinearMap.toMatrixAlgEquiv b
  have hn : IsNilpotent (F (ad ℂ L (h : L)) - F (semisimpleOperator H h)) := by
    obtain ⟨k,hk⟩ := (semisimpleOperator_jordan H h).2
    refine ⟨k,?_⟩
    rw [← map_sub,← map_pow,hk,map_zero]
  have hz := complex_upper_nilpotent_diagonal _
    (hh.sub (semisimpleOperator_upper H b h hh)) hn i
  exact (sub_eq_zero.mp hz).symm

/-- Each diagonal eigenvalue of the semisimple operator is one of its
root-space eigenvalues, including when several roots have the same value. -/
theorem semisimpleOperator_diagonal_weight {n : ℕ} (b : Basis (Fin n) ℂ L) (h : H)
    (hh : (LinearMap.toMatrix b b (ad ℂ L (h : L))).IsUpperTriangular) (i : Fin n) :
    ∃ χ : Weight ℂ H L, LinearMap.toMatrix b b (semisimpleOperator H h) i i = χ h := by
  classical
  let Q : Polynomial ℂ := ∏ χ : Weight ℂ H L, (Polynomial.X - Polynomial.C (χ h))
  have hQ : Polynomial.aeval (semisimpleOperator H h) Q = 0 := by
    ext x
    apply root_induction H (p := fun v => Polynomial.aeval (semisimpleOperator H h) Q v = 0)
      (x := x)
    · intro χ v hv
      rw [Module.End.aeval_apply_of_mem_apply_eq_smul (semisimpleOperator_apply H h χ hv)]
      have hz : Q.eval (χ h) = 0 := by
        simp only [Q,Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,
          Polynomial.eval_C]
        exact Finset.prod_eq_zero (Finset.mem_univ χ) (sub_self _)
      rw [hz,zero_smul]
    · simp
    · intro v w hv hw
      simp only [map_add,hv,hw,add_zero]
  let F := LinearMap.toMatrixAlgEquiv b
  have hu : (F (semisimpleOperator H h)).IsUpperTriangular :=
    semisimpleOperator_upper H b h hh
  have hzero : Q.eval (F (semisimpleOperator H h) i i) = 0 := by
    rw [← complex_matrix_aeval_diagonal (F (semisimpleOperator H h)) hu Q i,
      Polynomial.aeval_algHom_apply, hQ, map_zero]
    rfl
  simp only [Q,Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,
    Polynomial.eval_C,Finset.prod_eq_zero_iff,Finset.mem_univ,true_and] at hzero
  obtain ⟨χ,hχ⟩ := hzero
  exact ⟨χ,sub_eq_zero.mp hχ⟩

/-- Polynomial interpolation removes exactly the imaginary diagonal part. -/
theorem imaginaryOperator_diagonal {n : ℕ} (b : Basis (Fin n) ℂ L) (h : H)
    (hh : (LinearMap.toMatrix b b (ad ℂ L (h : L))).IsUpperTriangular) (i : Fin n) :
    LinearMap.toMatrix b b (imaginaryOperator H h) i i =
      imaginaryPart (LinearMap.toMatrix b b (ad ℂ L (h : L)) i i) := by
  obtain ⟨χ,hχ⟩ := semisimpleOperator_diagonal_weight H b h hh i
  obtain ⟨p,hp⟩ := imaginaryOperator_polynomial H h
  have hpχ : p.eval (χ h) = imaginaryPart (χ h) := by
    obtain ⟨v,hv,hv0⟩ := χ.exists_ne_zero
    have he := congrArg (fun f : Module.End ℂ L => f v) hp
    rw [Module.End.aeval_apply_of_mem_apply_eq_smul (semisimpleOperator_apply H h χ hv),
      imaginaryOperator_apply H h χ hv] at he
    exact (smul_left_injective ℂ hv0) he
  let F := LinearMap.toMatrixAlgEquiv b
  change F (semisimpleOperator H h) i i = χ h at hχ
  calc
    F (imaginaryOperator H h) i i = Polynomial.aeval (F (semisimpleOperator H h)) p i i := by
      rw [Polynomial.aeval_algHom_apply,hp]
    _ = p.eval (F (semisimpleOperator H h) i i) :=
      complex_matrix_aeval_diagonal _ (semisimpleOperator_upper H b h hh) p i
    _ = imaginaryPart (F (semisimpleOperator H h) i i) := by rw [hχ,hpχ]
    _ = imaginaryPart (F (ad ℂ L (h : L)) i i) := by
      exact congrArg imaginaryPart (semisimpleOperator_diagonal H b h hh i)

theorem realPartOperator_diagonal_im {n : ℕ} (b : Basis (Fin n) ℂ L) (h : H)
    (hh : (LinearMap.toMatrix b b (ad ℂ L (h : L))).IsUpperTriangular) (i : Fin n) :
    (LinearMap.toMatrix b b (ad ℂ L (h : L) - imaginaryOperator H h) i i).im = 0 := by
  rw [map_sub,Matrix.sub_apply,imaginaryOperator_diagonal H b h hh]
  simp [imaginaryPart]

end PolycyclicRecognition.ComplexCartan

end

end OAI

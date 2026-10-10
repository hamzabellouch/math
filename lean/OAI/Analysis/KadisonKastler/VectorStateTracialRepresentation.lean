import OAI.Analysis.KadisonKastler.TracialMatrixInjectivity
import OAI.Analysis.KadisonKastler.TracialCauchySchwarz
import OAI.Analysis.KadisonKastler.ExpectedCentralizer
import OAI.Analysis.KadisonKastler.MatrixStagesInClosure

namespace OAI

/-! # Recognizing a faithful tracial vector state

The expected finite algebra in the modular argument already has a faithful
trace represented by the common vector. This yields the tracial matrix
injectivity theorem directly in that representation.
-/

namespace KadisonKastler

open UltrapowerBridge

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

/-- A faithful vector trace supplies precisely the concrete tracial representation data. -/
def tracialRepresentationOfVectorState (τ : FaithfulTracialState (Algebra M))
    (Ω : H) (hΩ : ∀ a : Algebra M, τ.toLinearMap a = inner ℂ Ω (a.val Ω)) :
    TracialRepresentation M where
  vector := Ω
  norm_vector := by
    have h := hΩ 1
    rw [τ.map_one] at h
    change (1 : ℂ) = inner ℂ Ω Ω at h
    have hr := congrArg Complex.re h
    change (1 : ℝ) = RCLike.re (inner ℂ Ω Ω) at hr
    rw [inner_self_eq_norm_sq] at hr
    nlinarith [norm_nonneg Ω]
  cyclic S T := by
    change inner ℂ Ω ((S * T).val Ω) = inner ℂ Ω ((T * S).val Ω)
    rw [← hΩ, ← hΩ, τ.tracial]
  separating T hT := by
    apply τ.faithful T
    rw [hΩ]
    change inner ℂ Ω ((star T.val) (T.val Ω)) = 0
    rw [hT, map_zero, inner_zero_right]

/-- A matrix closure carrying a faithful vector trace is injective without an AFD input. -/
theorem isInjective_matrix_closure_of_vector_state
    (τ : FaithfulTracialState (Algebra M)) (Ω : H)
    (hΩ : ∀ a : Algebra M, τ.toLinearMap a = inner ℂ Ω (a.val Ω))
    (A : ℕ → Generator.FiniteMatrixStage M)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra)) :
    IsInjective (Generator.FiniteMatrixStage.generatedVonNeumann A) :=
  isInjective_tracial_matrix_closure (tracialRepresentationOfVectorState τ Ω hΩ) A hA

/-- The trace need only be defined on the generated matrix closure. -/
theorem isInjective_matrix_closure_of_generated_vector_state
    (A : ℕ → Generator.FiniteMatrixStage M)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (τ : FaithfulTracialState (Algebra (Generator.FiniteMatrixStage.generatedVonNeumann A)))
    (Ω : H) (hΩ : ∀ a, τ.toLinearMap a = inner ℂ Ω (a.val Ω)) :
    IsInjective (Generator.FiniteMatrixStage.generatedVonNeumann A) := by
  rw [← matrixStagesInClosure_generated A]
  exact isInjective_matrix_closure_of_vector_state τ Ω hΩ (matrixStagesInClosure A)
    (by simpa only [matrixStagesInClosure_algebra] using hA)

/-- A unital left-module expectation identifies its trace on the subalgebra
with the restriction of the represented expected state. -/
theorem trace_vector_of_expected_state {N : VonNeumannAlgebra H} (hNM : N ≤ M)
    (τ : FaithfulTracialState (Algebra N)) (P : Algebra M →L[ℂ] Algebra N)
    (hP : P 1 = 1)
    (hleft : ∀ (r : Algebra N) (x : Algebra M),
      P (StarSubalgebra.inclusion hNM r * x) = r * P x)
    (Ω : H) (hΩ : ∀ x : Algebra M, expectedTrace τ P x = inner ℂ Ω (x.val Ω)) :
    ∀ r : Algebra N, τ.toLinearMap r = inner ℂ Ω (r.val Ω) := by
  intro r
  have hp := hleft r 1
  simp only [mul_one, hP] at hp
  have hv := hΩ (StarSubalgebra.inclusion hNM r)
  rw [expectedTrace_apply, hp] at hv
  exact hv

end

end KadisonKastler

end OAI

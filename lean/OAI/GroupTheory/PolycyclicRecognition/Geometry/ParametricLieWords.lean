import Mathlib.Algebra.Free
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.NormedSpace

namespace OAI

/-! # Lie words as functions of their structure constants

The bilinear bracket itself varies in a finite-dimensional vector space.
Word evaluation is smooth jointly in that bracket and the input vectors, so
word identities and normalization equations persist under limits.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A bound on bilinear evaluations bounds the iterated operator norm. -/
theorem norm_bilinear_le_of_bound (B : V →L[ℝ] V →L[ℝ] V) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ x y, ‖B x y‖ ≤ C * ‖x‖ * ‖y‖) : ‖B‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound B hC
  intro x
  apply ContinuousLinearMap.opNorm_le_bound (B x) (mul_nonneg hC (norm_nonneg x))
  exact h x

/-- Evaluate a bracket word with a specified continuous bilinear bracket. -/
def evalBilinearWord (B : V →L[ℝ] V →L[ℝ] V) (X : I → V) : FreeMagma I → V
  | .of i => X i
  | .mul a b => B (evalBilinearWord B X a) (evalBilinearWord B X b)

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {n : ℕ∞}

/-- Smooth dependence of a finite word on both bracket and generator data. -/
theorem contDiff_evalBilinearWord (B : P → V →L[ℝ] V →L[ℝ] V)
    (X : P → I → V) (hB : ContDiff ℝ n B)
    (hX : ∀ i, ContDiff ℝ n (fun p => X p i)) (w : FreeMagma I) :
    ContDiff ℝ n (fun p => evalBilinearWord (B p) (X p) w) := by
  induction w using FreeMagma.rec with
  | of i => exact hX i
  | mul a b ha hb => exact (hB.clm_apply ha).clm_apply hb

/-- The defining identities of a real Lie bracket, with bilinearity supplied
by its continuous-linear-map type. -/
def IsLieBracket (B : V →L[ℝ] V →L[ℝ] V) : Prop :=
  (∀ x, B x x = 0) ∧ ∀ x y z, B x (B y z) = B (B x y) z + B y (B x z)

/-- Alternation and Jacobi are closed conditions on the bracket. -/
theorem isClosed_setOf_isLieBracket :
    IsClosed {B : V →L[ℝ] V →L[ℝ] V | IsLieBracket B} := by
  simp only [IsLieBracket, ofPred_and, ofPred_forall]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro x
    exact isClosed_eq (by fun_prop) continuous_const
  · apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro y
    apply isClosed_iInter
    intro z
    exact isClosed_eq (by fun_prop) (by fun_prop)

/-- A fixed word equation is closed even while both bracket and generators
vary. This is the normalization condition used by rescaled word bases. -/
theorem isClosed_bilinearWord_eq [Fintype I] (w : FreeMagma I) (v : V) :
    IsClosed {p : (V →L[ℝ] V →L[ℝ] V) × (I → V) |
      evalBilinearWord p.1 p.2 w = v} := by
  have hc : Continuous (fun p : (V →L[ℝ] V →L[ℝ] V) × (I → V) =>
      evalBilinearWord p.1 p.2 w) :=
    (contDiff_evalBilinearWord (n := 0) Prod.fst (fun p => p.2) contDiff_fst
      (fun i => (contDiff_apply ℝ V i).comp contDiff_snd) w).continuous
  exact isClosed_eq hc continuous_const

/-- All finite word-normalization equations hold on a closed parameter set. -/
theorem isClosed_wordNormalizations [Fintype I] {J : Type*}
    (w : J → FreeMagma I) (v : J → V) :
    IsClosed {p : (V →L[ℝ] V →L[ℝ] V) × (I → V) |
      ∀ j, evalBilinearWord p.1 p.2 (w j) = v j} := by
  simp only [ofPred_forall]
  exact isClosed_iInter (fun j => isClosed_bilinearWord_eq (w j) (v j))

end PolycyclicRecognition

end

end OAI

import OAI.Analysis.KadisonKastler.ConcreteTraceUniqueness
import OAI.Analysis.KadisonKastler.PreparedPairState

namespace OAI

/-! # A finite expected subfactor gives a centralizing functional

The trace in this construction is only on the finite subfactor. Composing
it with a bimodular conditional expectation gives a functional on the
ambient algebra which centralizes that subfactor. No traciality of the
ambient algebra is asserted or used.
-/

namespace KadisonKastler

noncomputable section

section Abstract

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- The functional obtained by composing a finite trace and an expectation. -/
def expectedTrace (τ : FaithfulTracialState A) (E : B →L[ℂ] A) : B →L[ℂ] ℂ :=
  τ.toContinuousLinearMap.comp E

@[simp]
theorem expectedTrace_apply (τ : FaithfulTracialState A) (E : B →L[ℂ] A) (x : B) :
    expectedTrace τ E x = τ.toLinearMap (E x) := rfl

theorem norm_expectedTrace_le (τ : FaithfulTracialState A) (E : B →L[ℂ] A)
    (hE : ‖E‖ ≤ 1) : ‖expectedTrace τ E‖ ≤ 1 := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul τ.norm_toContinuousLinearMap_le hE (norm_nonneg E) zero_le_one).trans
      (by norm_num))

theorem expectedTrace_one (τ : FaithfulTracialState A) (E : B →L[ℂ] A)
    (hE : E 1 = 1) : expectedTrace τ E 1 = 1 := by
  rw [expectedTrace_apply, hE, τ.map_one]

theorem expectedTrace_restrict (τ : FaithfulTracialState A) (E : B →L[ℂ] A)
    (ι : A →⋆ₐ[ℂ] B) (hE : ∀ a, E (ι a) = a) (a : A) :
    expectedTrace τ E (ι a) = τ.toLinearMap a := by
  rw [expectedTrace_apply, hE]

/-- Bimodularity and the finite trace imply the centralizer identity. -/
theorem expectedTrace_centralizes (τ : FaithfulTracialState A) (E : B →L[ℂ] A)
    (ι : A →⋆ₐ[ℂ] B)
    (hleft : ∀ a x, E (ι a * x) = a * E x)
    (hright : ∀ a x, E (x * ι a) = E x * a) (a : A) (x : B) :
    expectedTrace τ E (ι a * x) = expectedTrace τ E (x * ι a) := by
  rw [expectedTrace_apply, expectedTrace_apply, hleft, hright]
  exact τ.tracial a (E x)

end Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- When the composed state is represented by a vector, its centralizer
identity is exactly the identity required by the matrix-state argument. -/
theorem vector_functional_centralizes_of_expectation
    (M R : VonNeumannAlgebra H) (hRM : R ≤ M)
    (τ : FaithfulTracialState (Algebra R))
    (E : Algebra M →L[ℂ] Algebra R)
    (hleft : ∀ (r : Algebra R) (x : Algebra M),
      E (StarSubalgebra.inclusion hRM r * x) = r * E x)
    (hright : ∀ (r : Algebra R) (x : Algebra M),
      E (x * StarSubalgebra.inclusion hRM r) = E x * r)
    (Ω : H)
    (hΩ : ∀ x : Algebra M, expectedTrace τ E x = inner ℂ Ω (x.val Ω))
    (r : Algebra R) (x : Algebra M) :
    inner ℂ Ω ((r.val * x.val) Ω) = inner ℂ Ω ((x.val * r.val) Ω) := by
  have he := expectedTrace_centralizes τ E (StarSubalgebra.inclusion hRM)
    hleft hright r x
  rw [hΩ, hΩ] at he
  exact he

/-- A normalized expectation and a representing vector force unit norm. -/
theorem norm_vector_of_expectedTrace
    (M R : VonNeumannAlgebra H) (τ : FaithfulTracialState (Algebra R))
    (E : Algebra M →L[ℂ] Algebra R) (hE : E 1 = 1) (Ω : H)
    (hΩ : ∀ x : Algebra M, expectedTrace τ E x = inner ℂ Ω (x.val Ω)) :
    ‖Ω‖ = 1 := by
  have he : inner ℂ Ω Ω = 1 := by
    simpa only [OneMemClass.coe_one, one_apply_eq_self] using
      (hΩ 1).symm.trans (expectedTrace_one τ E hE)
  have hs : ‖Ω‖ ^ 2 = 1 := by
    have hr := congrArg Complex.re he
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) Ω]
    exact hr
  nlinarith [norm_nonneg Ω]

end

end KadisonKastler

end OAI

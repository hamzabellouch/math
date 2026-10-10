import OAI.Analysis.KadisonKastler.ProductStateCentralizer
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

/-! # A semantic certificate for the modular action of a vector state

The bounded KMS strip condition is Blackadar, *Operator Algebras*,
III.4.7.1--2 (printed pp.325--326). For a faithful normal vector state
it characterizes its modular automorphism group. Retaining the condition
prevents the core classification from being applied to an arbitrary
strongly continuous action.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The scalar strip condition at inverse temperature minus one, with
the sign convention `σ_t(x) = U_t x U_t*`. -/
def VectorStateKMS (M : VonNeumannAlgebra H) (Ω : H)
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) : Prop :=
  ∀ x ∈ M, ∀ y ∈ M, ∃ f : ℂ → ℂ,
    ContinuousOn f {z | 0 ≤ z.im ∧ z.im ≤ 1} ∧
    DifferentiableOn ℂ f {z | 0 < z.im ∧ z.im < 1} ∧
    (∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 1 → ‖f z‖ ≤ C) ∧
    (∀ t : ℝ, f t = productVectorState Ω
      (unitaryConj (U (Multiplicative.ofAdd t)) x * y)) ∧
    (∀ t : ℝ, f ((t : ℂ) + Complex.I) = productVectorState Ω
      (y * unitaryConj (U (Multiplicative.ofAdd t)) x))

/-- The canonical implementation fixes the vector; together with the
strip condition this identifies the represented modular state action. -/
structure IsModularStateGroup (M : VonNeumannAlgebra H) (Ω : H)
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) : Prop where
  fixes_vector : ∀ t, (U t : H →L[ℂ] H) Ω = Ω
  kms : VectorStateKMS M Ω U

theorem productVectorState_unitaryConj_of_fixes
    (Ω : H) (u : unitary (H →L[ℂ] H))
    (hfix : (u : H →L[ℂ] H) Ω = Ω) (x : H →L[ℂ] H) :
    productVectorState Ω (unitaryConj u x) = productVectorState Ω x := by
  have hstar : (star (u : H →L[ℂ] H)) Ω = Ω := by
    have hinv := Unitary.star_mul_self_of_mem u.property
    calc
      _ = (star (u : H →L[ℂ] H)) ((u : H →L[ℂ] H) Ω) := by rw [hfix]
      _ = (star (u : H →L[ℂ] H) * (u : H →L[ℂ] H)) Ω := rfl
      _ = Ω := by rw [hinv]; rfl
  change inner ℂ Ω ((u : H →L[ℂ] H) (x ((star (u : H →L[ℂ] H)) Ω))) = _
  rw [hstar]
  calc
    _ = inner ℂ ((u : H →L[ℂ] H) Ω) ((u : H →L[ℂ] H) (x Ω)) := by rw [hfix]
    _ = _ := _root_.Unitary.inner_map_map u Ω (x Ω)

theorem IsModularStateGroup.state_invariant {M : VonNeumannAlgebra H} {Ω : H}
    {U : Multiplicative ℝ →* unitary (H →L[ℂ] H)}
    (h : IsModularStateGroup M Ω U) (t : Multiplicative ℝ) (x : H →L[ℂ] H) :
    productVectorState Ω (unitaryConj (U t) x) = productVectorState Ω x :=
  productVectorState_unitaryConj_of_fixes Ω (U t) (h.fixes_vector t) x

end

end KadisonKastler

end OAI

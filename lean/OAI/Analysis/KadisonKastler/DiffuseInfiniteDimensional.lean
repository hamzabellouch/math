import OAI.Analysis.KadisonKastler.FiniteDimensionalGap
import OAI.Analysis.FactorGeneration.Target

namespace OAI

/-! # Diffuse projection algebras are infinite dimensional

Splitting a nonzero projection strictly decreases the dimension of its
right ideal. Finite dimensionality therefore contradicts diffuseness.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (M : VonNeumannAlgebra H)

def projectionRightIdeal (p : Algebra M) : Submodule ℂ (Algebra M) where
  carrier := {x | p * x = x}
  zero_mem' := mul_zero _
  add_mem' hx hy := by change p * (_ + _) = _; rw [mul_add, hx, hy]
  smul_mem' c x hx := by change p * (c • x) = _; rw [mul_smul_comm, hx]

theorem projectionRightIdeal_strict {p q : Algebra M}
    (hp : IsStarProjection p) (hqp : q * p = q) (hpq : p * q = q) (hne : q ≠ p) :
    projectionRightIdeal M q < projectionRightIdeal M p := by
  apply lt_of_le_of_ne
  · intro x hx
    change p * x = x
    change q * x = x at hx
    rw [← hx, ← mul_assoc, hpq, hx]
  · intro he
    have hmem : p ∈ projectionRightIdeal M q := by
      rw [he]
      exact hp.isIdempotentElem.eq
    exact hne (hqp.symm.trans hmem)

/-- The ordinary II₁-factor projection predicate forces its concrete
operator algebra to be infinite dimensional. -/
theorem not_finiteDimensional_of_isII1Factor (hM : Generator.IsII1Factor M.toStarSubalgebra) :
    ¬ FiniteDimensional ℂ (Algebra M) := by
  intro hdim
  let := hdim
  have hz : ∀ n : ℕ, ∀ p : Algebra M, IsStarProjection p →
      Module.finrank ℂ (projectionRightIdeal M p) = n → p = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hp hpn
      by_contra hne
      obtain ⟨q, hq, hqne, hneq, hpq, hqp⟩ := hM.diffuse p hp hne
      have hlt := Submodule.finrank_lt_finrank_of_lt
        (projectionRightIdeal_strict M hp hqp hpq hneq)
      rw [hpn] at hlt
      exact hqne (ih _ hlt q hq rfl)
  have hone := hz _ 1 (IsStarProjection.one _) rfl
  exact hM.nonzero (congrArg Subtype.val hone).symm

end

end KadisonKastler

end OAI

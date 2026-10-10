import OAI.NumberTheory.Ostmann.Construction.TransferCompletePhase
import OAI.NumberTheory.Ostmann.Characters.PermutedAdditiveCancellation

namespace OAI

/-! # The common-center additive phase cancels on the matched diagonal -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

section

variable {H Y : Type*} [Fintype H] [Fintype Y]
variable (L : H → ℕ) (U : Y → ℕ)
variable [∀ h, Fact (L h).Prime] [∀ y, Fact (U y).Prime]

theorem retainedAdditiveBranch_equiv (e : Equiv.Perm H)
    (center : ∀ p : ℕ, ZMod p) (M : ℕ) (v : ℤ) :
    retainedAdditiveBranch (fun h => L (e h)) U center M v =
      retainedAdditiveBranch L U center M v := by
  unfold retainedAdditiveBranch
  simp_rw [tupleCofactor_equiv e L (fun h => (Fact.out : (L h).Prime).ne_zero), Equiv.prod_comp e L]
  rw [Equiv.prod_comp e (fun h => (ZMod.stdAddChar
    (center (L h) * ((v : ZMod (L h)) /
      ((M * (tupleCofactor L h * ∏ y, U y) : ℕ) : ZMod (L h)))) : ℂ))]

theorem retainedAdditiveBranch_norm (center : ∀ p : ℕ, ZMod p) (M : ℕ) (v : ℤ) :
    ‖retainedAdditiveBranch L U center M v‖ = 1 := by
  simp only [retainedAdditiveBranch, norm_mul, norm_prod,
    ZMod.stdAddChar_apply, Circle.norm_coe, Finset.prod_const_one, mul_one]

theorem retained_additive_matching_cancel (e : Equiv.Perm H)
    (center : ∀ p : ℕ, ZMod p) (M : ℕ) (v : ℤ) (W W' : ℂ) :
    (retainedAdditiveBranch L U center M v * W) *
      conj (retainedAdditiveBranch (fun h => L (e h)) U center M v * W') = W * conj W' := by
  rw [retainedAdditiveBranch_equiv, map_mul]
  have hn : retainedAdditiveBranch L U center M v *
      conj (retainedAdditiveBranch L U center M v) = 1 := by
    rw [Complex.mul_conj', retainedAdditiveBranch_norm]
    norm_num
  calc
    _ = (retainedAdditiveBranch L U center M v * conj (retainedAdditiveBranch L U center M v)) *
        (W * conj W') := by ring
    _ = _ := by rw [hn, one_mul]

/-- The integer pivot and the common prime centers introduce no residual
additive phase in a matched pair, even when the character rows differ. -/
theorem retainedPrimePhase_matching (e : Equiv.Perm H)
    (center : ∀ p : ℕ, ZMod p)
    (χH χH' : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY χY' : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b b' : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (νH νH' : H → ℂ) (νY νY' : Y → ℂ) (M : ℕ) (v : ℤ) (W W' : ℂ) :
    (W * retainedPrimePhase L U center χH χY b νH νY M v) *
      conj (W' * retainedPrimePhase (fun h => L (e h)) U center χH' χY' b' νH' νY' M v) =
    (W * retainedCharacterBranch L U χH χY b νH νY M) *
      conj (W' * retainedCharacterBranch (fun h => L (e h)) U χH' χY' b' νH' νY' M) := by
  unfold retainedPrimePhase
  calc
    _ = (retainedAdditiveBranch L U center M v *
          (W * retainedCharacterBranch L U χH χY b νH νY M)) *
        conj (retainedAdditiveBranch (fun h => L (e h)) U center M v *
          (W' * retainedCharacterBranch (fun h => L (e h)) U χH' χY' b' νH' νY' M)) := by
      simp only [map_mul]
      ring
    _ = _ := retained_additive_matching_cancel L U e center M v _ _

end

end Ostmann

end OAI

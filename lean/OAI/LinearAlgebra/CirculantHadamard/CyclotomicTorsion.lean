import OAI.LinearAlgebra.CirculantHadamard.CyclotomicRings
import OAI.LinearAlgebra.CirculantHadamard.Kronecker

namespace OAI

/-!
# Kronecker's criterion in the actual alternating coefficient ring

The finite generator and root-of-unity hypotheses are discharged for the
literal ring `B u = ℤ[i, rho_p : p ∣ u]`. The modulus-one hypothesis follows
for alternating products by clearing the actual product denominator and
evaluating the norm identities.
-/

namespace CirculantHadamard

theorem B_root_of_unity (u : ℕ) (z : CyclotomicRings.B u)
    (hz : ∀ σ : CyclotomicRings.B u →+* ℂ, ‖σ z‖ = 1) :
    ∃ n : ℕ, 0 < n ∧ z ^ n = 1 := by
  apply finite_adjoin_root_of_unity
    (({Complex.I} : Set ℂ) ∪ CyclotomicRings.rho '' (u.primeFactors : Set ℕ))
    ((Set.finite_singleton Complex.I).union
      (u.primeFactors.finite_toSet.image CyclotomicRings.rho)) ?_ z hz
  intro ζ hζ
  rcases hζ with hI | ⟨p, hp, rfl⟩
  · have hζI : ζ = Complex.I := Set.mem_singleton_iff.mp hI
    subst ζ
    exact ⟨4, by decide, CyclotomicRings.I_isPrimitiveRoot.pow_eq_one⟩
  · have hprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
    exact ⟨p, hprime.pos, CyclotomicRings.rho_pow p hprime.ne_zero⟩

end CirculantHadamard

end OAI

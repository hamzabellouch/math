import OAI.AlgebraicGeometry.CommutingDerivations.DerivationOperations
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Localization.Away.Basic

namespace OAI

/-!
A common exponent clears finitely many localized generator images.
Leibniz and polynomial induction extend the generator bounds to the full ring
and yield descended derivations.
-/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

variable {K σ τ L : Type*} [CommRing K] [CommRing L]

/-- Leibniz extends a closure proof on the literal polynomial generators to
the whole polynomial ring. No finite-variable or domain assumption is needed. -/
theorem derivation_preserves_polynomial_image [Algebra K L]
    (ι : MvPolynomial σ K →ₐ[K] L) (D : Derivation K L L)
    (hX : ∀ j : σ, ∃ q : MvPolynomial σ K, ι q = D (ι (X j))) :
    ∀ p : MvPolynomial σ K, ∃ q : MvPolynomial σ K, ι q = D (ι p) := by
  intro p
  induction p using MvPolynomial.induction_on with
  | C a =>
      refine ⟨0, ?_⟩
      simp only [map_zero, algHom_C, Derivation.map_algebraMap]
  | add p q hp hq =>
      obtain ⟨dp, hdp⟩ := hp
      obtain ⟨dq, hdq⟩ := hq
      exact ⟨dp + dq, by simp only [map_add, hdp, hdq]⟩
  | mul_X p j hp =>
      obtain ⟨dp, hdp⟩ := hp
      obtain ⟨dj, hdj⟩ := hX j
      refine ⟨p * dj + X j * dp, ?_⟩
      simp only [map_add, map_mul, hdp, hdj, Derivation.leibniz, smul_eq_mul]

section Clearing
variable [Fintype σ] [Fintype τ]
  [Algebra (MvPolynomial σ K) L]

/-- One exponent clears any finite collection of localization elements.
The proof selects actual numerators and takes the finite maximum of exponents.
It remains valid when the original coefficient ring has zero divisors. -/
theorem finite_localization_denominator_bound (c : MvPolynomial σ K)
    [IsLocalization.Away c L] (z : τ → σ → L) :
    ∃ N : ℕ, ∀ (i : τ) (j : σ), ∃ a : MvPolynomial σ K,
      algebraMap (MvPolynomial σ K) L a =
        (algebraMap (MvPolynomial σ K) L c)^N * z i j := by
  classical
  choose m a ha using fun ij : τ × σ => IsLocalization.Away.surj c (z ij.1 ij.2)
  let N : ℕ := Finset.univ.sup m
  refine ⟨N, ?_⟩
  intro i j
  have hle : m (i, j) ≤ N := Finset.le_sup (f := m) (Finset.mem_univ (i, j))
  refine ⟨c^(N - m (i, j)) * a (i, j), ?_⟩
  rw [map_mul, map_pow, ← ha (i, j)]
  calc
    (algebraMap (MvPolynomial σ K) L c)^(N - m (i, j)) *
        (z i j * (algebraMap (MvPolynomial σ K) L c)^m (i, j)) =
      (algebraMap (MvPolynomial σ K) L c)^(N - m (i, j) + m (i, j)) * z i j := by
        rw [pow_add]
        ring
    _ = (algebraMap (MvPolynomial σ K) L c)^N * z i j := by
        rw [Nat.sub_add_cancel hle]

variable [Algebra K L] [IsScalarTower K (MvPolynomial σ K) L]

/-- Construct descended derivations with a common clearing exponent,
assuming injectivity of the localization map. -/
theorem exists_common_denominator_descent (c : MvPolynomial σ K)
    [IsLocalization.Away c L]
    (hinj : Function.Injective (algebraMap (MvPolynomial σ K) L))
    (D : τ → Derivation K L L) :
    ∃ (N : ℕ) (d : τ → Derivation K (MvPolynomial σ K) (MvPolynomial σ K)),
      ∀ (i : τ) (p : MvPolynomial σ K),
        algebraMap (MvPolynomial σ K) L (d i p) =
          (algebraMap (MvPolynomial σ K) L c)^N *
            D i (algebraMap (MvPolynomial σ K) L p) := by
  let ι : MvPolynomial σ K →ₐ[K] L := IsScalarTower.toAlgHom K (MvPolynomial σ K) L
  obtain ⟨N, hN⟩ := finite_localization_denominator_bound c
    (fun i j => D i (algebraMap (MvPolynomial σ K) L (X j)))
  have hstable (i : τ) : ∀ p : MvPolynomial σ K,
      ∃ q : MvPolynomial σ K, ι q =
        ((algebraMap (MvPolynomial σ K) L c)^N • D i) (ι p) := by
    apply derivation_preserves_polynomial_image ι
    intro j
    simpa [ι, Derivation.smul_apply, smul_eq_mul] using hN i j
  choose d hd using fun i => exists_descendDerivation ι hinj
    ((algebraMap (MvPolynomial σ K) L c)^N • D i) (hstable i)
  refine ⟨N, d, ?_⟩
  intro i p
  simpa [ι, Derivation.smul_apply, smul_eq_mul] using hd i p

end Clearing
end AbhyankarSathaye.CommutingDerivations

end

end OAI

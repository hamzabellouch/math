import Mathlib
import OAI.NumberTheory.CubicGram.EuclideanDomain

namespace OAI

/-! Squarefree factorization and exact prime detector products. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
open UniqueFactorizationMonoid
def primeFactors (n : Eisenstein) : Finset Eisenstein := (normalizedFactors n).toFinset

lemma primeFactors_nodup {n : Eisenstein} (hn : Squarefree n) :
    (normalizedFactors n).Nodup :=
  (squarefree_iff_nodup_normalizedFactors hn.ne_zero).mp hn

lemma primeFactors_norm_prod {n : Eisenstein} (hn : Squarefree n) :
    ∏ p ∈ primeFactors n, normNat p = normNat n := by
  rw [primeFactors, Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr (primeFactors_nodup hn)]
  exact (map_multiset_prod normNatHom _).symm.trans
    (associated_normNat (prod_normalizedFactors hn.ne_zero))

lemma primeFactors_norm_prod_real {n : Eisenstein} (hn : Squarefree n) :
    ∏ p ∈ primeFactors n, norm p = norm n := by
  simpa only [Nat.cast_prod, normNat_cast] using
    congrArg (fun m : ℕ => (m : ℝ)) (primeFactors_norm_prod hn)

lemma prime_iff_primeFactors_card_one {n : Eisenstein} (hn : Squarefree n) :
    Prime n ↔ (primeFactors n).card = 1 := by
  rw [primeFactors, Multiset.toFinset_card_of_nodup (primeFactors_nodup hn)]
  constructor
  · intro hp
    rw [normalizedFactors_irreducible hp.irreducible]
    rfl
  · intro h
    obtain ⟨p, hp⟩ := Multiset.card_eq_one.mp h
    have hprime : Prime p := prime_of_normalized_factor p (by rw [hp]; simp)
    have hassoc := prod_normalizedFactors hn.ne_zero
    rw [hp, Multiset.prod_singleton] at hassoc
    exact hassoc.prime_iff.mp hprime

def roughProduct (ψ : ℝ → ℝ) (y : ℝ) (n : Eisenstein) : ℝ :=
  ∏ p ∈ primeFactors n, (1 - ψ (norm p / y))

lemma primeFactor_norm_pos {n p : Eisenstein} (hp : p ∈ primeFactors n) :
    0 < norm p := by
  have hprime := prime_of_normalized_factor p (Multiset.mem_toFinset.mp hp)
  exact Complex.normSq_pos.mpr (fun h => hprime.ne_zero (Subtype.ext h))

lemma roughProduct_of_prime {ψ : ℝ → ℝ} {y : ℝ} {n : Eisenstein}
    (hψ : ∀ x : ℝ, 2 ≤ x → ψ x = 0) (hy : 0 < y)
    (hn : Prime n) (hlarge : 2*y ≤ norm n) : roughProduct ψ y n = 1 := by
  have hnorm : norm (normalize n) = norm n := by
    simpa only [normNat_cast] using congrArg (fun m : ℕ => (m : ℝ))
      (associated_normNat (normalize_associated n))
  simp only [roughProduct, primeFactors, normalizedFactors_irreducible hn.irreducible,
    Multiset.toFinset_singleton, Finset.prod_singleton, hnorm]
  rw [hψ _ ((le_div_iff₀ hy).mpr hlarge), sub_zero]

lemma roughProduct_eq_zero_of_three_factors {ψ : ℝ → ℝ} {y : ℝ} {n : Eisenstein}
    (hψ : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1) (hy : 1 ≤ y)
    (hn : Squarefree n) (hsmall : norm n < y^3)
    (hthree : 3 ≤ (primeFactors n).card) : roughProduct ψ y n = 0 := by
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hex : ∃ p ∈ primeFactors n, norm p ≤ y := by
    by_contra! h
    have hprod : y^(primeFactors n).card ≤ norm n := by
      rw [← primeFactors_norm_prod_real hn, ← Finset.prod_const]
      exact Finset.prod_le_prod₀ (fun _ _ => hypos.le) (fun factor hfactor => (h factor hfactor).le)
    have hpow : y^3 ≤ y^(primeFactors n).card := pow_le_pow_right₀ hy hthree
    exact (not_le_of_gt hsmall) (hpow.trans hprod)
  obtain ⟨p, hp, hple⟩ := hex
  apply Finset.prod_eq_zero_iff.mpr
  refine ⟨p, hp, ?_⟩
  rw [hψ _ (div_pos (primeFactor_norm_pos hp) hypos)
    ((div_le_one hypos).mpr hple), sub_self]

lemma exact_prime_detector {ψ : ℝ → ℝ} {y : ℝ} {n : Eisenstein}
    (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0) (hy : 1 ≤ y)
    (hn : Squarefree n) (hlo : 2*y < norm n) (hhi : norm n < y^3) :
    (if Prime n then (1 : ℝ) else 0) =
      roughProduct ψ y n -
        (if (primeFactors n).card = 2 then roughProduct ψ y n else 0) := by
  have hnotzero : (primeFactors n).card ≠ 0 := by
    intro hzero
    have hemp := Finset.card_eq_zero.mp hzero
    have hnorm := primeFactors_norm_prod_real hn
    rw [hemp, Finset.prod_empty] at hnorm
    nlinarith
  by_cases hp : Prime n
  · have hcard := (prime_iff_primeFactors_card_one hn).mp hp
    rw [ite_eq_left hp, hcard, ite_eq_right (by decide), sub_zero,
      roughProduct_of_prime hψzero (by linarith) hp hlo.le]
  · rw [ite_eq_right hp]
    by_cases htwo : (primeFactors n).card = 2
    · rw [ite_eq_left htwo, sub_self]
    · have hnotone : (primeFactors n).card ≠ 1 :=
        mt (prime_iff_primeFactors_card_one hn).mpr hp
      have hthree : 3 ≤ (primeFactors n).card := by omega
      rw [ite_eq_right htwo, sub_zero,
        roughProduct_eq_zero_of_three_factors hψone hy hn hhi hthree]

lemma roughProduct_distinguished_subsets (ψ : ℝ → ℝ) (w z : ℝ) (n : Eisenstein) :
    roughProduct ψ z n =
      ∑ s ∈ (primeFactors n).powerset,
        (∏ p ∈ s, (ψ (norm p / w) - ψ (norm p / z))) *
          ∏ p ∈ primeFactors n \ s, (1 - ψ (norm p / w)) := by
  rw [← Finset.prod_add]
  unfold roughProduct
  congr 1
  ext p
  ring

end CubicFirstMoment
end
end

end OAI

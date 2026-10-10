import OAI.Analysis.Quantum.DimensionTen.RootReduction

namespace OAI

section
noncomputable section
open NumberField Polynomial
namespace DimensionTen




theorem numberField_frobenius (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] (p : ℕ) [Fact p.Prime] :
    ∃ P : Ideal (𝓞 K), P.IsMaximal ∧ P.LiesOver (Ideal.span {(p : ℤ)}) ∧
      ∃ σ : Gal(K/ℚ), ∀ x : 𝓞 K,
        Ideal.Quotient.mk P (((galRestrict ℤ ℚ K (𝓞 K)) σ) x) =
          (Ideal.Quotient.mk P x) ^ p := by
  let := IsIntegralClosure.MulSemiringAction ℤ ℚ K (𝓞 K)
  let := Algebra.isInvariant_of_isGalois ℤ ℚ K (𝓞 K)
  obtain ⟨P, hP, hOver⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := 𝓞 K) (Ideal.span {(p : ℤ)})
  let := hP
  let := hOver
  let : Finite (𝓞 K ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient
    (Ideal.IsMaximal.ne_bot_of_isIntegral_int P)
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(K/ℚ) P
  refine ⟨P, hP, hOver, σ, ?_⟩
  intro x
  have h := hσ.mk_apply x
  rw [← Ideal.over_def P (Ideal.span {(p : ℤ)}), Int.card_ideal_quot] at h
  exact h

end DimensionTen

end
end

section
noncomputable section
open NumberField Polynomial
namespace DimensionTen

lemma quotient_charP {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 K)) [P.IsMaximal]
    [P.LiesOver (Ideal.span {(p : ℤ)})] : CharP (𝓞 K ⧸ P) p := by
  apply (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
  have hp : algebraMap ℤ (𝓞 K) (p : ℤ) ∈ P :=
    (Ideal.mem_of_liesOver P (Ideal.span {(p : ℤ)}) (p : ℤ)).mp (Ideal.subset_span (by simp))
  simpa using (Ideal.Quotient.eq_zero_iff_mem.mpr hp)

lemma rootInteger_gal {K : Type*} [Field K] [NumberField K]
    (f : ℤ[X]) (hm : f.Monic) (σ : Gal(K/ℚ)) (x : f.rootSet K) :
    rootInteger f hm (σ • x) = (galRestrict ℤ ℚ K (𝓞 K) σ) (rootInteger f hm x) := by
  apply RingOfIntegers.coe_injective
  rw [algebraMap_galRestrict_apply]
  rfl

lemma root_reduction_frobenius {K : Type*} [Field K] [NumberField K]
    (f : ℤ[X]) (hm : f.Monic) (p : ℕ) (P : Ideal (𝓞 K)) (σ : Gal(K/ℚ))
    (hσ : ∀ x : 𝓞 K, Ideal.Quotient.mk P ((galRestrict ℤ ℚ K (𝓞 K) σ) x) =
        (Ideal.Quotient.mk P x) ^ p) (x : f.rootSet K) :
    Ideal.Quotient.mk P (rootInteger f hm (σ • x)) =
        (Ideal.Quotient.mk P (rootInteger f hm x)) ^ p := by
  rw [rootInteger_gal, hσ]

lemma iterate_pow_perm {ι R : Type*} [Monoid R] (σ : Equiv.Perm ι) (r : ι → R)
    (p : ℕ) (h : ∀ i, r (σ i) = r i ^ p) (n : ℕ) :
    ∀ i, r ((σ ^ n) i) = r i ^ (p ^ n) := by
  induction n with
  | zero => intro i; simp
  | succ n ih =>
    intro i
    rw [pow_succ', Equiv.Perm.mul_apply, h, ih, ← pow_mul, pow_succ]

end DimensionTen

end
end

end OAI

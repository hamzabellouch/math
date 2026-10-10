import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Intersection.LocalLengthMulProjectiveClosureDegree

namespace OAI

namespace SiegelZeros


namespace WeightedTorusJets.Geometry


variable {K : Type*} [Field K] [Infinite K]
local notation "P₄" => MvPolynomial (Fin 4) K
local notation "T₄" => Localization.Away (∏ i : Fin 4, (MvPolynomial.X i : P₄))

theorem torus_rectangleJetIdeal_exists_parameters_with_projective_degree_bound
    (q : Ideal T₄) [q.IsPrime] (c : Fin 3 → Fin 4 → K) (t : Fin 3 → ℕ) (b : ℕ)
    {N : ℕ} (hN : 0 < N) {F : P₄} (hF : F ∈ polynomialBox K N)
    (hq : q ∈ (rectangleJetIdeal
      (fun a => algebraMap P₄ T₄ (invariantJet c a F)) t b).minimalPrimes) :
    ∃ g : Fin (Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q))
        (IsLocalRing.CotangentSpace (Localization.AtPrime q))) → P₄,
      (∀ i, g i ∈ Submodule.span K
        ((fun a => invariantJet c a F) '' {a | ∀ j, a j ≤ b * t j})) ∧
      (∀ i, (g i).totalDegree ≤ 4 * N) ∧
      (Ideal.span (Set.range (fun i => algebraMap P₄ (Localization.AtPrime q) (g i)))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime q) ∧
      Module.length (Localization.AtPrime q) (Localization.AtPrime q ⧸
        (rectangleJetIdeal (fun a => algebraMap P₄ T₄ (invariantJet c a F)) t b).map
          (algebraMap T₄ (Localization.AtPrime q))) ≤
        Module.length (Localization.AtPrime q) (Localization.AtPrime q ⧸ Ideal.span
          (Set.range (fun i => algebraMap P₄ (Localization.AtPrime q) (g i)))) ∧
      Module.length (Localization.AtPrime q) (Localization.AtPrime q ⧸ Ideal.span
          (Set.range (fun i => algebraMap P₄ (Localization.AtPrime q) (g i)))) *
        (GradedQuotient.projectiveDegree
          (coneIdeal (q.comap (algebraMap P₄ T₄)))
          (coneIdeal_isHomogeneous (q.comap (algebraMap P₄ T₄))) : ℕ∞) ≤
        ((4 * N) ^ Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q))
          (IsLocalRing.CotangentSpace (Localization.AtPrime q)) : ℕ) := by
  obtain ⟨g, hspan, hdeg, hrad, hlength, _⟩ :=
    rectangleJetIdeal_exists_parameters_with_length
      (A := Localization.AtPrime q) q c t b hN hF hq
  let p := q.comap (algebraMap P₄ T₄)
  let : p.IsPrime := Ideal.comap_isPrime _ q
  let : IsLocalization.AtPrime (Localization.AtPrime q) p :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers (∏ i : Fin 4, (MvPolynomial.X i : P₄))) (Localization.AtPrime q) q
  refine ⟨g, hspan, hdeg, hrad, hlength, ?_⟩
  let e := IsLocalization.algEquiv p.primeCompl
    (Localization.AtPrime q) (Localization.AtPrime p)
  have hcomm i : e (algebraMap P₄ (Localization.AtPrime q) (g i)) =
      algebraMap P₄ (Localization.AtPrime p) (g i) := e.commutes (g i)
  have hrad' := radical_span_eq_maximalIdeal_of_commuting_images e.toRingEquiv
    (fun i => algebraMap P₄ (Localization.AtPrime q) (g i))
    (fun i => algebraMap P₄ (Localization.AtPrime p) (g i)) hcomm hrad
  rw [quotient_length_eq_of_commuting_images e.toRingEquiv
    (fun i => algebraMap P₄ (Localization.AtPrime q) (g i))
    (fun i => algebraMap P₄ (Localization.AtPrime p) (g i)) hcomm]
  exact local_length_mul_projectiveClosure_degree_le p
    (polynomial_prime_height_eq_cotangent_finrank (A := Localization.AtPrime q) p)
    g hdeg hrad'


end WeightedTorusJets.Geometry



end SiegelZeros

end OAI

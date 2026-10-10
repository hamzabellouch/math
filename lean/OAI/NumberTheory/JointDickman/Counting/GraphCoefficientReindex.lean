import OAI.NumberTheory.JointDickman.Amplification.GraphPairMass

namespace OAI

/-! # The graph coefficient triples have no multiplicity at a fixed lag -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def graphTriplePair (i : GraphCoefficientTriple) : ℕ × ℕ :=
  (∏ p ∈ i.2.2, p, ∏ p ∈ i.1, p)

open Classical in
noncomputable def supportedGraphTriples (B T : ℕ) (j : ℤ) : Finset GraphCoefficientTriple :=
  (arithmeticGraphTriples B T).filter (fun i => graphTripleLag i = j ∧
    (∏ p ∈ i.2.1, p, ∏ p ∈ i.1, p) ∈ amplificationCoefficientPairs B T ∧
    graphTriplePair i ∈ amplificationCoefficientPairs B T)

theorem graphTriple_subsets {B T : ℕ} {i : GraphCoefficientTriple}
    (hi : i ∈ arithmeticGraphTriples B T) :
    i.1 ⊆ auxiliaryPrimes B ∧ i.2.1 ⊆ auxiliaryPrimes B ∧ i.2.2 ⊆ auxiliaryPrimes B := by
  classical
  have h := mem_product.mp (mem_filter.mp hi).1
  exact ⟨mem_powerset.mp h.1, mem_powerset.mp (mem_product.mp h.2).1,
    mem_powerset.mp (mem_product.mp h.2).2⟩

theorem graphTriple_positive_relation {B T j : ℕ} {i : GraphCoefficientTriple}
    (hi : i ∈ supportedGraphTriples B T (j : ℤ)) :
    (∏ p ∈ i.2.1, p) = (∏ p ∈ i.2.2, p)+j*(∏ p ∈ i.1, p) := by
  classical
  have h := (mem_filter.mp (mem_filter.mp hi).1).2.2.2.2.1
  change ((∏ p ∈ i.2.1, p : ℕ) : ℤ)-(∏ p ∈ i.2.2, p : ℕ) =
    graphTripleLag i*(∏ p ∈ i.1, p : ℕ) at h
  rw [(mem_filter.mp hi).2.1] at h
  have h' : ((∏ p ∈ i.2.1, p : ℕ) : ℤ) =
      (∏ p ∈ i.2.2, p : ℕ)+(j : ℤ)*(∏ p ∈ i.1, p : ℕ) := by linarith
  exact_mod_cast h'

theorem graphTriplePair_injective {B T : ℕ} (j : ℤ) :
    Set.InjOn graphTriplePair (supportedGraphTriples B T j : Set GraphCoefficientTriple) := by
  classical
  intro i hi k hk hik
  have hi' := (mem_filter.mp hi).1
  have hk' := (mem_filter.mp hk).1
  have his := graphTriple_subsets hi'
  have hks := graphTriple_subsets hk'
  have hD : (∏ p ∈ i.1, p) = ∏ p ∈ k.1, p := congrArg Prod.snd hik
  have hE : (∏ p ∈ i.2.2, p) = ∏ p ∈ k.2.2, p := congrArg Prod.fst hik
  have hei := (mem_filter.mp hi').2.2.2.2.1
  have hek := (mem_filter.mp hk').2.2.2.2.1
  change ((∏ p ∈ i.2.1, p : ℕ) : ℤ)-(∏ p ∈ i.2.2, p : ℕ) =
    graphTripleLag i*(∏ p ∈ i.1, p : ℕ) at hei
  change ((∏ p ∈ k.2.1, p : ℕ) : ℤ)-(∏ p ∈ k.2.2, p : ℕ) =
    graphTripleLag k*(∏ p ∈ k.1, p : ℕ) at hek
  rw [(mem_filter.mp hi).2.1, hD, hE] at hei
  rw [(mem_filter.mp hk).2.1] at hek
  have hA : (∏ p ∈ i.2.1, p) = ∏ p ∈ k.2.1, p := by
    have h : ((∏ p ∈ i.2.1, p : ℕ) : ℤ) = (∏ p ∈ k.2.1, p : ℕ) := by linarith
    exact_mod_cast h
  apply Prod.ext
  · exact primeProduct_injective (auxiliaryPrimes_prime B) his.1 hks.1 hD
  · exact Prod.ext (primeProduct_injective (auxiliaryPrimes_prime B) his.2.1 hks.2.1 hA)
      (primeProduct_injective (auxiliaryPrimes_prime B) his.2.2 hks.2.2 hE)

theorem graphTriple_harmonic_le {B T j : ℕ} :
    (∑ i ∈ supportedGraphTriples B T (j : ℤ),
      (coefficientWeight B (∏ p ∈ i.1, p) * coefficientWeight B (∏ p ∈ i.2.1, p) *
        coefficientWeight B (∏ p ∈ i.2.2, p)) /
          (((∏ p ∈ i.2.1, p : ℕ) : ℝ)*(∏ p ∈ i.2.2, p : ℕ))) ≤
      ∑ bc ∈ amplificationCoefficientPairs B T, graphCoefficientHarmonicTerm B j bc := by
  classical
  have hinj := graphTriplePair_injective (B := B) (T := T) (j : ℤ)
  have hsub : (supportedGraphTriples B T (j : ℤ)).image graphTriplePair ⊆
      amplificationCoefficientPairs B T := by
    intro bc hbc
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hbc
    exact (mem_filter.mp hi).2.2.2
  calc
    _ = ∑ i ∈ supportedGraphTriples B T (j : ℤ),
        graphCoefficientHarmonicTerm B j (graphTriplePair i) := by
      apply sum_congr rfl
      intro i hi
      rw [graphTriple_positive_relation hi]
      unfold graphCoefficientHarmonicTerm graphTriplePair
      push_cast
      ring
    _ = ∑ bc ∈ (supportedGraphTriples B T (j : ℤ)).image graphTriplePair,
        graphCoefficientHarmonicTerm B j bc := (sum_image hinj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub
      (fun bc _ _ => graphCoefficientHarmonicTerm_nonneg B j bc)

theorem graphTriple_harmonic_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop,
      ∀ T j : ℕ, 0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → j ≠ 0 →
      (∑ i ∈ supportedGraphTriples B T (j : ℤ),
        (coefficientWeight B (∏ p ∈ i.1, p) * coefficientWeight B (∏ p ∈ i.2.1, p) *
          coefficientWeight B (∏ p ∈ i.2.2, p)) /
            (((∏ p ∈ i.2.1, p : ℕ) : ℝ)*(∏ p ∈ i.2.2, p : ℕ))) ≤
        C*(B : ℝ)/(T : ℝ)*singularFactor 24 j := by
  obtain ⟨C,hC,hbound⟩ := graphCoefficientHarmonic_mass hFord hM
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with B hB
  intro T j hT hTs hj
  exact graphTriple_harmonic_le.trans (hB T j hT hTs hj)

end JointDickman

end OAI

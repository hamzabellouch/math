import OAI.NumberTheory.JointDickman.Counting.GraphLagSwap

namespace OAI

/-! # Both signs of the actual lag-mass bound -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem graphTriple_harmonic_signed_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop,
      ∀ T : ℕ, ∀ j : ℤ, 0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → j ≠ 0 →
      (∑ i ∈ supportedGraphTriples B T j,
        (coefficientWeight B (∏ p ∈ i.1, p) * coefficientWeight B (∏ p ∈ i.2.1, p) *
          coefficientWeight B (∏ p ∈ i.2.2, p)) /
            (((∏ p ∈ i.2.1, p : ℕ) : ℝ)*(∏ p ∈ i.2.2, p : ℕ))) ≤
        C*(B : ℝ)/(T : ℝ)*singularFactor 24 j.natAbs := by
  obtain ⟨C,hC,hbound⟩ := graphTriple_harmonic_bound hFord hM
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with B hB
  intro T j hT hTs hj
  have h := hB T j.natAbs hT hTs (Int.natAbs_ne_zero.mpr hj)
  by_cases hj0 : 0 ≤ j
  · have he : (j.natAbs : ℤ) = j := by rw [Int.natCast_natAbs, abs_of_nonneg hj0]
    simpa only [he] using h
  · have he : -(j.natAbs : ℤ) = j := by
      rw [Int.natCast_natAbs, abs_of_neg (lt_of_not_ge hj0), neg_neg]
    simpa only [he] using (graphTriple_harmonic_neg B T (j.natAbs : ℤ)).trans_le h

theorem graphLagMean_signed_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T : ℕ, ∀ j : ℤ,
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → j ≠ 0 →
      graphLagMean B T j ≤ K*(B : ℝ)*singularFactor 24 j.natAbs := by
  obtain ⟨K₁,hK₁,hmean⟩ := graphEdgeMean_bound hM
  obtain ⟨K₂,hK₂,hcoeff⟩ := graphTriple_harmonic_signed_bound hFord hM
  refine ⟨2*K₁*K₂, by positivity, ?_⟩
  filter_upwards [hmean,hcoeff,graphTriple_size_bound] with B hB hC hsize
  intro T j hT hTs hj
  let w (i : GraphCoefficientTriple) :=
    (coefficientWeight B (∏ p ∈ i.1, p) * coefficientWeight B (∏ p ∈ i.2.1, p) *
      coefficientWeight B (∏ p ∈ i.2.2, p)) /
        (((∏ p ∈ i.2.1, p : ℕ) : ℝ)*(∏ p ∈ i.2.2, p : ℕ))
  have hw (i : GraphCoefficientTriple) : 0 ≤ w i := by
    dsimp [w]
    exact div_nonneg (mul_nonneg (mul_nonneg (coefficientWeight_nonneg B _)
      (coefficientWeight_nonneg B _)) (coefficientWeight_nonneg B _)) (by positivity)
  have hsum : (∑ i ∈ coprimeGraphTriples B T j, w i) ≤
      K₂*(B : ℝ)/(T : ℝ)*singularFactor 24 j.natAbs := by
    apply (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => hw i)).trans
    exact hC T j hT hTs hj
  calc
    _ ≤ ∑ i ∈ coprimeGraphTriples B T j, (2*(T : ℝ)*K₁)*w i := by
      apply sum_le_sum
      intro i hi
      have his := (mem_filter.mp hi).1
      have hs := graphTriple_subsets (mem_filter.mp his).1
      have hp (D : Finset ℕ) (hD : D ⊆ auxiliaryPrimes B) : 0 < ∏ p ∈ D, p :=
        prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hD hp)).pos)
      have he := hB _ _ _ (hp _ hs.2.1) (hp _ hs.2.2) (hp _ hs.1)
        (hsize T hT hTs j i his)
      have hmul := mul_le_mul_of_nonneg_left he
        (show 0 ≤ (coefficientWeight B (∏ p ∈ i.1, p) *
          coefficientWeight B (∏ p ∈ i.2.1, p) * coefficientWeight B (∏ p ∈ i.2.2, p)) *
            (2*(T : ℝ)) from mul_nonneg
              (mul_nonneg (mul_nonneg (coefficientWeight_nonneg B _)
                (coefficientWeight_nonneg B _)) (coefficientWeight_nonneg B _)) (by positivity))
      convert hmul using 1; dsimp [w]; ring
    _ = (2*(T : ℝ)*K₁) * ∑ i ∈ coprimeGraphTriples B T j, w i := (mul_sum _ _ _).symm
    _ ≤ (2*(T : ℝ)*K₁) * (K₂*(B : ℝ)/(T : ℝ)*singularFactor 24 j.natAbs) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (2*K₁*K₂)*(B : ℝ)*singularFactor 24 j.natAbs := by
      have hTr : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
      field_simp

/-- All regularity parameters are bounded simultaneously. They enter
only the nonnegative weights already dominated by the same majorant. -/
theorem arithmeticLagMass_signed_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T : ℕ, ∀ j : ℤ,
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → j ≠ 0 →
      j.natAbs ≤ auxiliaryCutoff B → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ L : ℕ, ∀ τ C : ℝ,
        arithmeticLagMass B L τ C T N j ≤
          K*(B : ℝ)*singularFactor 24 j.natAbs+ε := by
  obtain ⟨K,hK,hmean⟩ := graphLagMean_signed_bound hFord hM
  refine ⟨K,hK,?_⟩
  filter_upwards [hmean,eventually_gt_atTop 0] with B hB hB0
  intro T j hT hTs hj hjB ε hε
  have ht := graphLagMajorant_tendsto (B := B) hT
    hj hjB
  have hb := hB T j hT hTs hj
  filter_upwards [ht.eventually (Iio_mem_nhds (show graphLagMean B T j <
    K*(B : ℝ)*singularFactor 24 j.natAbs+ε by linarith))] with N hN
  intro L τ C
  exact (arithmeticLagMass_le_majorant hB0 hT τ C N j).trans hN.le


end JointDickman

end OAI

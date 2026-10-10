import OAI.NumberTheory.JointDickman.Counting.GraphLagMajorant

namespace OAI

/-! # The actual graph has uniformly bounded mass at every positive lag -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem graphLagMean_positive_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T j : ℕ,
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → j ≠ 0 →
      graphLagMean B T (j : ℤ) ≤ K*(B : ℝ)*singularFactor 24 j := by
  obtain ⟨K₁,hK₁,hmean⟩ := graphEdgeMean_bound hM
  obtain ⟨K₂,hK₂,hcoeff⟩ := graphTriple_harmonic_bound hFord hM
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
  have hsum : (∑ i ∈ coprimeGraphTriples B T (j : ℤ), w i) ≤
      K₂*(B : ℝ)/(T : ℝ)*singularFactor 24 j := by
    apply (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => hw i)).trans
    exact hC T j hT hTs hj
  calc
    _ ≤ ∑ i ∈ coprimeGraphTriples B T (j : ℤ), (2*(T : ℝ)*K₁)*w i := by
      apply sum_le_sum
      intro i hi
      have his := (mem_filter.mp hi).1
      have hs := graphTriple_subsets (mem_filter.mp his).1
      have hp (D : Finset ℕ) (hD : D ⊆ auxiliaryPrimes B) : 0 < ∏ p ∈ D, p :=
        prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hD hp)).pos)
      have he := hB _ _ _ (hp _ hs.2.1) (hp _ hs.2.2) (hp _ hs.1)
        (hsize T hT hTs (j : ℤ) i his)
      have hmul := mul_le_mul_of_nonneg_left he
        (show 0 ≤ (coefficientWeight B (∏ p ∈ i.1, p) *
          coefficientWeight B (∏ p ∈ i.2.1, p) * coefficientWeight B (∏ p ∈ i.2.2, p)) *
            (2*(T : ℝ)) from mul_nonneg
              (mul_nonneg (mul_nonneg (coefficientWeight_nonneg B _)
                (coefficientWeight_nonneg B _)) (coefficientWeight_nonneg B _)) (by positivity))
      convert hmul using 1; dsimp [w]; ring
    _ = (2*(T : ℝ)*K₁) * ∑ i ∈ coprimeGraphTriples B T (j : ℤ), w i := (mul_sum _ _ _).symm
    _ ≤ (2*(T : ℝ)*K₁) * (K₂*(B : ℝ)/(T : ℝ)*singularFactor 24 j) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (2*K₁*K₂)*(B : ℝ)*singularFactor 24 j := by
      have hTr : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
      field_simp

/-- All regularity parameters are bounded simultaneously. They enter
only the nonnegative weights already dominated by the same majorant. -/
theorem arithmeticLagMass_positive_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T j : ℕ,
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → j ≠ 0 →
      j ≤ auxiliaryCutoff B → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ L : ℕ, ∀ τ C : ℝ,
        arithmeticLagMass B L τ C T N (j : ℤ) ≤
          K*(B : ℝ)*singularFactor 24 j+ε := by
  obtain ⟨K,hK,hmean⟩ := graphLagMean_positive_bound hFord hM
  refine ⟨K,hK,?_⟩
  filter_upwards [hmean,eventually_gt_atTop 0] with B hB hB0
  intro T j hT hTs hj hjB ε hε
  have ht := graphLagMajorant_tendsto (B := B) hT
    (by exact_mod_cast hj : (j : ℤ) ≠ 0) (by simpa only [Int.natAbs_natCast] using hjB)
  have hb := hB T j hT hTs hj
  filter_upwards [ht.eventually (Iio_mem_nhds (show graphLagMean B T (j : ℤ) <
    K*(B : ℝ)*singularFactor 24 j+ε by linarith))] with N hN
  intro L τ C
  exact (arithmeticLagMass_le_majorant hB0 hT τ C N (j : ℤ)).trans hN.le

end JointDickman

end OAI

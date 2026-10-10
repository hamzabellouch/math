import OAI.NumberTheory.JointDickman.Amplification.FirstPairMass

namespace OAI

/-! # The uniform first-representation mass at a fixed lag -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem halfPrimeSubsetMass_nonneg {B : ℕ} {A : Finset ℕ}
    (hA : A ∈ (auxiliaryPrimes B).powerset) :
    0 ≤ bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) A := by
  apply bernoulliSubsetMass_nonneg (mem_powerset.mp hA)
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).two_le
  exact ⟨div_nonneg (by norm_num) (by linarith),
    (div_le_one (by linarith : (0 : ℝ) < p)).mpr (by linarith)⟩

/-- The coefficient test averaged under the exact half-prime law. -/
theorem supportedEndpointTest_half_mean_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (T b j : ℕ),
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → j ≠ 0 →
      Disjoint b.primeFactors (Nat.primesLE (auxiliaryCutoff B)) →
      (∑ A ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) A*
        supportedEndpointTest B T b j (∏ p ∈ A, p)) ≤
        K/((B : ℝ)*T)*singularFactor 24 j := by
  obtain ⟨K,hK,hbound⟩ := endpointCoefficientMass_bound hFord hM
    (show (0 : ℝ) < 1/2 by norm_num) (16/5)
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 10] with B hmass hB
  intro T b j hT hTs hj hbrough
  by_cases hw : EndpointCoefficientWindow B T b
  · obtain ⟨c,hc,hlog,_,hlo,hhi⟩ := hw
    have hscale := endpointRowScale_window (by omega) hT hc hlog hlo hhi
    have hsize := endpointCoefficientWindow_size hB hTs
      (show EndpointCoefficientWindow B T b from ⟨c,hc,hlog,by assumption,hlo,hhi⟩)
    simp only [supportedEndpointTest,show EndpointCoefficientWindow B T b from
      ⟨c,hc,hlog,by assumption,hlo,hhi⟩,ite_true,endpointCoefficientTest_mean]
    exact hmass T _ j b hT hscale.1 hscale.2.2 hj hsize hbrough
  · simp only [supportedEndpointTest,hw,ite_false,mul_zero,sum_const_zero]
    exact mul_nonneg (div_nonneg hK.le (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      (zero_le_one.trans (singularFactor_one_le (by norm_num) j))

/-- Summing all first pairs costs O(Sigma(j)/T). There is no dependence
on the number of representations or on the endpoint regularity cutoffs. -/
theorem candidateFirstPairMass_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (L T H M : ℕ) (τ C : ℝ),
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
      ∀ (χ : BlockCandidateIndex M → ℝ), (∀ e, χ e ≤ 1) →
      ∀ (i t : Fin M), i < t →
        candidateFirstPairMass B L T H τ C χ i t ≤ K/(T : ℝ)*singularFactor 24 (t.val-i.val) := by
  obtain ⟨K,hK,hmass⟩ := supportedEndpointTest_half_mean_bound hFord hM
  obtain ⟨D,hD,hroot⟩ := independentRootMean_bounded hM
  refine ⟨D*K,by positivity,?_⟩
  filter_upwards [hmass,hroot,eventually_ge_atTop 10] with B hmass hroot hB
  intro L T H M τ C hT hTs χ hχ i t hit
  have hj : t.val-i.val ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hit)
  have hBr : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  let μ := bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p)
  have hμ (A : Finset ℕ) (hA : A ∈ (auxiliaryPrimes B).powerset) : 0 ≤ μ A := halfPrimeSubsetMass_nonneg hA
  have hs : 0 ≤ singularFactor 24 (t.val-i.val) :=
    zero_le_one.trans (singularFactor_one_le (by norm_num) _)
  have hfixed (A : Finset ℕ) (hA : A ∈ (auxiliaryPrimes B).powerset) :
      (∑ E ∈ (auxiliaryPrimes B).powerset, μ E*
        supportedEndpointTest B T (∏ p ∈ A, p) (t.val-i.val) (∏ p ∈ E, p)) ≤
        K/((B : ℝ)*T)*singularFactor 24 (t.val-i.val) := by
    apply hmass T _ _ hT hTs hj
    rw [Nat.primeFactors_prod (fun p hp => auxiliaryPrimes_prime B p (mem_powerset.mp hA hp))]
    exact auxiliarySubset_disjoint_small (mem_powerset.mp hA)
  calc
    _ ≤ ∑ ab ∈ (auxiliaryPrimes B).powerset.product (auxiliaryPrimes B).powerset,
        (B : ℝ)*independentRootMean B L τ C*μ ab.1*μ ab.2*
          supportedEndpointTest B T (∏ p ∈ ab.1, p) (t.val-i.val) (∏ p ∈ ab.2, p) := by
      apply sum_le_sum
      intro ab hab
      have hp := mem_product.mp hab
      split_ifs with he
      · exact candidateFirstPairMass_term_le hB hT hTs χ i t ab.1 ab.2
          (mem_powerset.mp hp.1) (mem_powerset.mp hp.2) he (hχ _)
      · exact mul_nonneg (mul_nonneg (mul_nonneg
          (mul_nonneg (Nat.cast_nonneg _) (independentRootMean_nonneg _ _ _ _))
          (hμ _ hp.1)) (hμ _ hp.2)) (supportedEndpointTest_nonneg _ _ _ _ _)
    _ = (B : ℝ)*independentRootMean B L τ C*
        ∑ A ∈ (auxiliaryPrimes B).powerset, μ A*
          ∑ E ∈ (auxiliaryPrimes B).powerset, μ E*
            supportedEndpointTest B T (∏ p ∈ A, p) (t.val-i.val) (∏ p ∈ E, p) := by
      rw [Finset.product_eq_sprod,sum_product]
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro A _
      apply sum_congr rfl
      intro E _
      ring
    _ ≤ (B : ℝ)*independentRootMean B L τ C*
        ∑ A ∈ (auxiliaryPrimes B).powerset, μ A*
          (K/((B : ℝ)*T)*singularFactor 24 (t.val-i.val)) := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (Nat.cast_nonneg B) (independentRootMean_nonneg _ _ _ _))
      apply sum_le_sum
      intro A hA
      exact mul_le_mul_of_nonneg_left (hfixed A hA) (hμ A hA)
    _ = independentRootMean B L τ C*K/(T : ℝ)*singularFactor 24 (t.val-i.val) := by
      rw [← sum_mul,bernoulliSubsetMass_sum,one_mul]
      field_simp
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hroot L τ C) hK.le) hTr.le) hs

end JointDickman

end OAI

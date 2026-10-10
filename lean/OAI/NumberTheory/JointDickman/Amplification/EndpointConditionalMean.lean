import OAI.NumberTheory.JointDickman.Amplification.EndpointRowScale

namespace OAI

/-! # Uniform mean at one independently averaged endpoint -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
noncomputable def supportedEndpointTest (B T b j a : ℕ) : ℝ :=
  if EndpointCoefficientWindow B T b then
    endpointCoefficientTest B b j (endpointRowScale T b) a else 0

theorem supportedEndpointTest_nonneg (B T b j a : ℕ) :
    0 ≤ supportedEndpointTest B T b j a := by
  unfold supportedEndpointTest
  split_ifs
  · exact endpointCoefficientTest_nonneg _ _ _ _ _
  · rfl

theorem supportedEndpointTest_ge {B T b j a c : ℕ}
    (hB : 10 ≤ B) (hT : 0 < T) (hTs : (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B))
    (hc : 0 < c) (hlog : (B : ℝ) ≤ Real.log c) (hlog' : Real.log c ≤ 2*B)
    (hlo : T*c ≤ b) (hhi : b ≤ 2*T*c) (ha : a = b+j*c)
    (hasize : a ≤ 2*T*c) :
    coefficientWeight B c ≤ supportedEndpointTest B T b j a := by
  have hw : EndpointCoefficientWindow B T b := ⟨c,hc,hlog,hlog',hlo,hhi⟩
  have hwa : EndpointCoefficientWindow B T a :=
    ⟨c,hc,hlog,hlog',by omega,hasize⟩
  rw [supportedEndpointTest,ite_eq_left hw]
  exact endpointCoefficientTest_ge (endpointRowScale_window (by omega) hT hc hlog hlo hhi).2.1
    ha (endpointCoefficientWindow_size hB hTs hwa)

/-- Uniformly in all truncations and every fixed rough first coefficient,
the averaged second endpoint contributes O(Sigma(j)/T). -/
theorem supportedEndpointTest_mean_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (L T b j : ℕ) (τ C : ℝ),
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → j ≠ 0 →
      Disjoint b.primeFactors (Nat.primesLE (auxiliaryCutoff B)) →
      (∑ S ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
        ∑ A ∈ endpointSplits B L τ C S,
          regularCoefficientWeight B L τ C (∏ p ∈ A, p)*
            regularResidueWeight B L τ C (S \ A)*
              supportedEndpointTest B T b j (∏ p ∈ A, p)) ≤
        K/(T : ℝ)*singularFactor 24 j := by
  classical
  obtain ⟨K,hK,hbound⟩ := endpointCoefficientMass_bound hFord hM
    (show (0 : ℝ) < 1/2 by norm_num) (16/5)
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 10] with B hmass hB
  intro L T b j τ C hT hTs hj hbrough
  by_cases hw : EndpointCoefficientWindow B T b
  · have hwcopy := hw
    obtain ⟨c,hc,hlog,_,hlo,hhi⟩ := hwcopy
    have hscale := endpointRowScale_window (by omega) hT hc hlog hlo hhi
    have hbsize := endpointCoefficientWindow_size hB hTs hw
    simp only [supportedEndpointTest,hw,ite_true]
    calc
      _ ≤ (B : ℝ)*endpointCoefficientMass B b j (endpointRowScale T b) :=
        independent_endpoint_coefficient_average (by omega) b j _
      _ ≤ (B : ℝ)*(K/((B : ℝ)*T)*singularFactor 24 j) :=
        mul_le_mul_of_nonneg_left
          (hmass T _ j b hT hscale.1 hscale.2.2 hj hbsize hbrough) (Nat.cast_nonneg B)
      _ = _ := by
        have hBr : (B : ℝ) ≠ 0 := by exact_mod_cast (show B ≠ 0 by omega)
        field_simp
  · simp only [supportedEndpointTest,hw,ite_false,mul_zero,sum_const_zero]
    exact mul_nonneg (div_nonneg hK.le (Nat.cast_nonneg T))
      ((singularFactor_one_le (by norm_num) j).trans' zero_le_one)

end JointDickman

end OAI

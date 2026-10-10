import OAI.NumberTheory.JointDickman.Counting.ReverseCoefficientMass
import OAI.NumberTheory.JointDickman.Amplification.EndpointRowScale

namespace OAI

/-! # Averaging the lower endpoint while the upper coefficient is fixed -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def reverseCoefficientTest (B T b j q a : ℕ) : ℝ :=
  ∑ c ∈ Ico q (4*q), if a = b-j*c ∧ T*q ≤ a ∧ (a : ℝ) ≤ Real.exp ((16/5 : ℝ)*B)
    then coefficientWeight B c else 0

theorem reverseCoefficientTest_nonneg (B T b j q a : ℕ) :
    0 ≤ reverseCoefficientTest B T b j q a := by
  apply sum_nonneg
  intro c _
  split_ifs
  · exact coefficientWeight_nonneg _ _
  · rfl

theorem reverseCoefficientTest_ge {B T b j q a c : ℕ}
    (hc : c ∈ Ico q (4*q)) (ha : a = b-j*c) (hmin : T*q ≤ a)
    (hsize : (a : ℝ) ≤ Real.exp ((16/5 : ℝ)*B)) :
    coefficientWeight B c ≤ reverseCoefficientTest B T b j q a := by
  unfold reverseCoefficientTest
  have h := single_le_sum (s := Ico q (4*q))
    (f := fun d => if a = b-j*d ∧ T*q ≤ a ∧ (a : ℝ) ≤ Real.exp ((16/5 : ℝ)*B)
      then coefficientWeight B d else 0)
    (fun d _ => by split_ifs; exact coefficientWeight_nonneg _ _; rfl) hc
  rw [ite_eq_left ⟨ha, hmin, hsize⟩] at h
  exact h

theorem reverseCoefficientTest_mean (B T b j q : ℕ) :
    (∑ A ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) A*
        reverseCoefficientTest B T b j q (∏ p ∈ A, p)) =
      reverseCoefficientMass B T b j q := by
  unfold reverseCoefficientTest reverseCoefficientMass
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  by_cases hs : T*q ≤ b-j*c ∧ (b-j*c : ℕ) ≤ Real.exp ((16/5 : ℝ)*B)
  · rw [ite_eq_left hs]
    unfold primeProductMass
    rw [sum_mul]
    apply sum_congr rfl
    intro A _
    by_cases ha : (∏ p ∈ A, p) = b-j*c
    · rw [ha]
      simp only [eq_self,true_and,hs,ite_true]
    · simp only [ha,false_and,ite_false,mul_zero,zero_mul]
  · rw [ite_eq_right hs]
    apply sum_eq_zero
    intro A _
    by_cases ha : (∏ p ∈ A, p) = b-j*c
    · rw [ha]
      simp only [eq_self,true_and,hs,ite_false,mul_zero]
    · simp only [ha,false_and,ite_false,mul_zero]

theorem independent_reverse_coefficient_average {B L : ℕ} {τ C : ℝ}
    (hB : 1 < B) (T b j q : ℕ) :
    (∑ S ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
      ∑ A ∈ endpointSplits B L τ C S,
        regularCoefficientWeight B L τ C (∏ p ∈ A, p)*
          regularResidueWeight B L τ C (S \ A)*
            reverseCoefficientTest B T b j q (∏ p ∈ A, p)) ≤
      (B : ℝ)*reverseCoefficientMass B T b j q := by
  simpa only [reverseCoefficientTest_mean] using
    independent_endpoint_split_average (L := L) (τ := τ) (C := C) hB
      (fun A => reverseCoefficientTest B T b j q (∏ p ∈ A, p))
      (fun A _ => reverseCoefficientTest_nonneg B T b j q _)

noncomputable def reverseSupportedTest (B T b j a : ℕ) : ℝ :=
  if EndpointCoefficientWindow B T b then
    reverseCoefficientTest B T b j (endpointRowScale T b) a else 0

theorem reverseSupportedTest_nonneg (B T b j a : ℕ) :
    0 ≤ reverseSupportedTest B T b j a := by
  unfold reverseSupportedTest
  split_ifs
  · exact reverseCoefficientTest_nonneg _ _ _ _ _ _
  · rfl

theorem reverseSupportedTest_ge {B T b j a c : ℕ}
    (hB : 10 ≤ B) (hT : 0 < T) (hTs : (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B))
    (hc : 0 < c) (hlog : (B : ℝ) ≤ Real.log c) (hlog' : Real.log c ≤ 2*B)
    (hlo : T*c ≤ b) (hhi : b ≤ 2*T*c) (ha : b = a+j*c) (hsmall : T*c ≤ a) :
    coefficientWeight B c ≤ reverseSupportedTest B T b j a := by
  have hw : EndpointCoefficientWindow B T b := ⟨c,hc,hlog,hlog',hlo,hhi⟩
  have hscale := endpointRowScale_window (by omega) hT hc hlog hlo hhi
  unfold reverseSupportedTest
  rw [ite_eq_left hw]
  apply reverseCoefficientTest_ge hscale.2.1
  · omega
  · exact (Nat.mul_le_mul_left T (mem_Ico.mp hscale.2.1).1).trans hsmall
  · have hab : (a : ℝ) ≤ b := by exact_mod_cast (by omega : a ≤ b)
    exact hab.trans (endpointCoefficientWindow_size hB hTs hw)

theorem reverseSupportedTest_mean_bound
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
              reverseSupportedTest B T b j (∏ p ∈ A, p)) ≤
        K/(T : ℝ)*singularFactor 24 j := by
  obtain ⟨K,hK,hbound⟩ := reverseCoefficientMass_bound hFord hM
    (show (0 : ℝ) < 1/2 by norm_num) (16/5)
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 10] with B hmass hB
  intro L T b j τ C hT hTs hj hbrough
  by_cases hw : EndpointCoefficientWindow B T b
  · have hwcopy := hw
    obtain ⟨c,hc,hlog,_,hlo,hhi⟩ := hwcopy
    have hscale := endpointRowScale_window (by omega) hT hc hlog hlo hhi
    have hbsize := endpointCoefficientWindow_size hB hTs hw
    simp only [reverseSupportedTest,hw,ite_true]
    calc
      _ ≤ (B : ℝ)*reverseCoefficientMass B T b j (endpointRowScale T b) :=
        independent_reverse_coefficient_average (by omega) T b j _
      _ ≤ (B : ℝ)*(K/((B : ℝ)*T)*singularFactor 24 j) :=
        mul_le_mul_of_nonneg_left
          (hmass T _ j b hT hscale.1 hscale.2.2 hj hbsize hbrough) (Nat.cast_nonneg B)
      _ = _ := by
        have hBr : (B : ℝ) ≠ 0 := by exact_mod_cast (show B ≠ 0 by omega)
        field_simp
  · simp only [reverseSupportedTest,hw,ite_false,mul_zero,sum_const_zero]
    exact mul_nonneg (div_nonneg hK.le (Nat.cast_nonneg T))
      ((singularFactor_one_le (by norm_num) j).trans' zero_le_one)

end JointDickman

end OAI

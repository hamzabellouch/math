import OAI.NumberTheory.JointDickman.Amplification.DyadicBoxRegularity
import OAI.NumberTheory.JointDickman.Amplification.AmplificationDyadicIdentity

namespace OAI

/-! # Exact dyadic recombination of the discarded regularity mass -/

namespace JointDickman
open Finset

open Classical in
noncomputable def discardedAmplificationTerm (B L j : ℕ) (τ C T : ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (c b a : ℕ) : ℝ :=
  if coefficientTripleRegular B L τ C a b c then 0 else
    |(B : ℝ)*amplificationArithmeticTerm B j T g h c b a|

open Classical in
noncomputable def discardedAmplificationBoxTerm (B L j : ℕ) (τ C T N : ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (c b a : ℕ) : ℝ :=
  if coefficientTripleRegular B L τ C a b c then 0 else
    |(B : ℝ)*amplificationBoxTerm B j T N g h c b a|

open Classical in
theorem discardedAmplificationBoxTerm_eq (B L j : ℕ) (τ C : ℝ) {T N : ℝ}
    (hT : 0 < T) (hN : 0 < N) (g h : (auxiliaryPrimes B → Bool) → ℝ) (c b a : ℕ) :
    discardedAmplificationBoxTerm B L j τ C T N g h c b a =
      discardedAmplificationTerm B L j τ C T g h c b a*dyadicPartitionWeight (c/(N/T)) := by
  unfold discardedAmplificationBoxTerm discardedAmplificationTerm
  rw [amplificationBoxTerm_eq B j hT hN]
  by_cases hr : coefficientTripleRegular B L τ C a b c
  · simp only [hr,ite_true,zero_mul]
  · simp only [hr,ite_false]
    rw [← mul_assoc,abs_mul,abs_of_nonneg (dyadicPartitionWeight_bounds _).1]

open Classical in
theorem discardedAmplificationBoxTerm_support (B L j : ℕ) (τ C : ℝ) {T N : ℝ}
    (hT : 0 < T) (hN : 0 < N) (g h : (auxiliaryPrimes B → Bool) → ℝ) (c b a : ℕ)
    (hn : discardedAmplificationBoxTerm B L j τ C T N g h c b a ≠ 0) :
    c ∈ Ioc ⌊(1/4 : ℝ)*(N/T)⌋₊ ⌊(17/4 : ℝ)*(N/T)⌋₊ ∧
    b ∈ Ioc ⌊(1/4 : ℝ)*N⌋₊ ⌊(17/4 : ℝ)*N⌋₊ ∧
    a ∈ Ioc ⌊(1/4 : ℝ)*N⌋₊ ⌊(17/4 : ℝ)*N⌋₊ := by
  apply amplificationBoxTerm_support B j hT hN g h
  intro hz
  exact hn (by simp [discardedAmplificationBoxTerm,hz])

open Classical in
theorem discardedAmplificationBox_sum (B L j : ℕ) (τ C T N : ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) :
    (∑ c ∈ Ioc ⌊(1/4 : ℝ)*(N/T)⌋₊ ⌊(17/4 : ℝ)*(N/T)⌋₊,
      ∑ b ∈ Ioc ⌊(1/4 : ℝ)*N⌋₊ ⌊(17/4 : ℝ)*N⌋₊,
      ∑ a ∈ Ioc ⌊(1/4 : ℝ)*N⌋₊ ⌊(17/4 : ℝ)*N⌋₊,
        discardedAmplificationBoxTerm B L j τ C T N g h c b a) =
    signedLocalRegularityError B L j τ C
      (Ico (tensorIntervalLower N) (tensorIntervalUpper N))
      (Ico (tensorIntervalLower (N/T)) (tensorIntervalUpper (N/T))) g h
      (fun a b c => amplificationBoxWeight B (Real.log (N/T)/B)
        (a/N) (b/N) (c/(N/T))) := by
  have hi (a b : ℕ) : Ico (a+1) (b+1) = Ioc a b := by
    ext n
    simp only [mem_Ico,mem_Ioc]
    omega
  unfold signedLocalRegularityError
  simp only [tensorIntervalLower,tensorIntervalUpper,hi]
  rw [sum_comm]
  simp_rw [sum_comm (s := Ioc ⌊(1/4 : ℝ)*(N/T)⌋₊ ⌊(17/4 : ℝ)*(N/T)⌋₊)
    (t := Ioc ⌊(1/4 : ℝ)*N⌋₊ ⌊(17/4 : ℝ)*N⌋₊)]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro c _
  unfold discardedAmplificationBoxTerm amplificationBoxTerm
  by_cases hr : coefficientTripleRegular B L τ C a b c
  · rw [ite_eq_left hr,ite_eq_right (show ¬ (a = b+j*c ∧
        ¬ coefficientTripleRegular B L τ C a b c) from fun hh => hh.2 hr)]
  · rw [ite_eq_right hr]
    by_cases he : a = b+j*c
    · rw [ite_eq_left he,ite_eq_left ⟨he,hr⟩]
      congr 1
      ring
    · rw [ite_eq_right he,ite_eq_right (fun hh => he hh.1)]
      simp only [mul_zero,abs_zero]

open Classical in
theorem discarded_amplification_dyadic_identity {B : ℕ} (hB : 30 ≤ B) {T : ℝ}
    (hT : 1 ≤ T) (hlogT : Real.log T ≤ (B : ℝ)/10) (L j U V : ℕ) (τ C : ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (hU : ∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
      ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U)
    (hV : ∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
      ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊ ≤ V) :
    (∑ c ∈ Ioc 0 V, ∑ b ∈ Ioc 0 U, ∑ a ∈ Ioc 0 U,
      discardedAmplificationTerm B L j τ C T g h c b a) =
    ∑ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
      signedLocalRegularityError B L j τ C
        (Ico (tensorIntervalLower (Real.exp ((k : ℝ)*Real.log 2)))
          (tensorIntervalUpper (Real.exp ((k : ℝ)*Real.log 2))))
        (Ico (tensorIntervalLower (Real.exp ((k : ℝ)*Real.log 2)/T))
          (tensorIntervalUpper (Real.exp ((k : ℝ)*Real.log 2)/T))) g h
        (fun a b c => amplificationBoxWeight B (Real.log (Real.exp ((k : ℝ)*Real.log 2)/T)/B)
          (a/Real.exp ((k : ℝ)*Real.log 2)) (b/Real.exp ((k : ℝ)*Real.log 2))
          (c/(Real.exp ((k : ℝ)*Real.log 2)/T))) := by
  have hTpos := lt_of_lt_of_le zero_lt_one hT
  let S := dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T)
  obtain ⟨hLU,_,hbracket⟩ := dyadic_scale_window hB hT hlogT
  symm
  simp_rw [← discardedAmplificationBox_sum]
  change (∑ k ∈ S, ∑ c ∈ _, ∑ b ∈ _, ∑ a ∈ _,
    discardedAmplificationBoxTerm B L j τ C T (Real.exp ((k : ℝ)*Real.log 2)) g h c b a) = _
  calc
    _ = ∑ k ∈ S, ∑ c ∈ Ioc 0 V, ∑ b ∈ Ioc 0 U, ∑ a ∈ Ioc 0 U,
        discardedAmplificationBoxTerm B L j τ C T (Real.exp ((k : ℝ)*Real.log 2)) g h c b a := by
      apply sum_congr rfl
      intro k hk
      apply finite_triple_sum_extend
      · intro n hn
        obtain ⟨hnl,hnu⟩ := mem_Ioc.mp hn
        exact mem_Ioc.mpr ⟨Nat.lt_of_le_of_lt (Nat.zero_le _) hnl,hnu.trans (hU k hk)⟩
      · intro n hn
        obtain ⟨hnl,hnu⟩ := mem_Ioc.mp hn
        exact mem_Ioc.mpr ⟨Nat.lt_of_le_of_lt (Nat.zero_le _) hnl,hnu.trans (hV k hk)⟩
      · exact discardedAmplificationBoxTerm_support B L j τ C hTpos (Real.exp_pos _) g h
    _ = ∑ c ∈ Ioc 0 V, ∑ b ∈ Ioc 0 U, ∑ a ∈ Ioc 0 U,
        ∑ k ∈ S, discardedAmplificationBoxTerm B L j τ C T
          (Real.exp ((k : ℝ)*Real.log 2)) g h c b a :=
      sum_triple_interchange S (Ioc 0 U) (Ioc 0 V) _
    _ = _ := by
      apply sum_congr rfl
      intro c hc
      apply sum_congr rfl
      intro b _
      apply sum_congr rfl
      intro a _
      simp_rw [discardedAmplificationBoxTerm_eq B L j τ C hTpos (Real.exp_pos _) g h c b a,
        div_div_eq_mul_div]
      rw [← mul_sum]
      by_cases he : discardedAmplificationTerm B L j τ C T g h c b a = 0
      · simp [he]
      · have harith : amplificationArithmeticTerm B j T g h c b a ≠ 0 := by
          intro hz
          exact he (by simp [discardedAmplificationTerm,hz])
        have hBp : 0 < B := lt_of_lt_of_le (by norm_num) hB
        obtain ⟨hlo,hhi⟩ := amplificationArithmeticTerm_log_support hBp j T g h c b a harith
        have hcp : (0 : ℝ) < c := by exact_mod_cast (mem_Ioc.mp hc).1
        obtain ⟨hcl,hcu⟩ := hbracket c hcp hlo hhi
        rw [geometric_dyadic_partition hLU (c*T) hcl hcu,mul_one]

end JointDickman

end OAI

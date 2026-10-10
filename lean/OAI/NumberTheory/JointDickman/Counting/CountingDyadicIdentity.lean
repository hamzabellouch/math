import OAI.NumberTheory.JointDickman.Counting.CountingBoxFeatures
import OAI.NumberTheory.JointDickman.Amplification.AmplificationDyadicIdentity

namespace OAI

/-! # Recover the unpartitioned arithmetic sum with its counting ramp -/

namespace JointDickman
open Finset

theorem normalized_counting_ratio {N T : ℝ} (hN : N ≠ 0) (hT : T ≠ 0) (b c : ℝ) :
    (b/N)/(c/(N/T)) = b/(T*c) := by
  by_cases hc : c = 0
  · simp [hc]
  · field_simp [hN,hT,hc]

noncomputable def rampedAmplificationArithmeticSum (B j : ℕ) (T : ℝ) (U V : ℕ)
    (δ σ : ℝ) (g h : (auxiliaryPrimes B → Bool) → ℝ) : ℝ :=
  B*∑ c ∈ Ioc 0 V, ∑ b ∈ Ioc 0 U, ∑ a ∈ Ioc 0 U,
    amplificationArithmeticTerm B j T g h c b a*countingRamp δ σ (b/(T*c))

theorem counting_dyadic_identity {B : ℕ} (hB : 30 ≤ B) {T : ℝ}
    (hT : 1 ≤ T) (hlogT : Real.log T ≤ (B : ℝ)/10) (j U V : ℕ) (δ σ : ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (hU : ∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
      ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U)
    (hV : ∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
      ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊ ≤ V) :
    geometricSmoothArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T (Real.log 2)
      (dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T))
      (fun k x y z => countingBoxWeight B δ (Real.log (Real.exp ((k : ℝ)*Real.log 2)/T)/B) σ x y z)
      g h = rampedAmplificationArithmeticSum B j T U V δ σ g h := by
  have hTpos := lt_of_lt_of_le zero_lt_one hT
  let S := dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T)
  obtain ⟨hLU,_,hbracket⟩ := dyadic_scale_window hB hT hlogT
  unfold geometricSmoothArithmeticSum rampedAmplificationArithmeticSum
  congr 1
  have hratio (k : ℤ) (b c : ℕ) :
      ((b : ℝ)/Real.exp ((k : ℝ)*Real.log 2))/(c/(Real.exp ((k : ℝ)*Real.log 2)/T)) = b/(T*c) :=
    normalized_counting_ratio (Real.exp_pos _).ne' hTpos.ne' _ _
  simp only [countingBoxWeight, hratio]
  have hfactor (c b a : ℕ) (k : ℤ) :
      (if a = b+j*c then
        signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) a*
        signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) h) b*
        coefficientWeight B c*
        (amplificationBoxWeight B (Real.log (Real.exp ((k : ℝ)*Real.log 2)/T)/B)
          (a/Real.exp ((k : ℝ)*Real.log 2)) (b/Real.exp ((k : ℝ)*Real.log 2))
          (c/(Real.exp ((k : ℝ)*Real.log 2)/T))*countingRamp δ σ (b/(T*c))) else 0) =
      amplificationBoxTerm B j T (Real.exp ((k : ℝ)*Real.log 2)) g h c b a*
        countingRamp δ σ (b/(T*c)) := by
    unfold amplificationBoxTerm
    split_ifs <;> ring
  simp only [hfactor]
  change (∑ k ∈ S,
      ∑ c ∈ Ioc ⌊(1/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊
        ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊,
      ∑ b ∈ Ioc ⌊(1/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊
        ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊,
      ∑ a ∈ Ioc ⌊(1/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊
        ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊,
        (amplificationBoxTerm B j T (Real.exp ((k : ℝ)*Real.log 2)) g h c b a*countingRamp δ σ (b/(T*c)))) = _
  calc
    _ = ∑ k ∈ S, ∑ c ∈ Ioc 0 V, ∑ b ∈ Ioc 0 U, ∑ a ∈ Ioc 0 U,
        (amplificationBoxTerm B j T (Real.exp ((k : ℝ)*Real.log 2)) g h c b a*countingRamp δ σ (b/(T*c))) := by
      apply sum_congr rfl
      intro k hk
      apply finite_triple_sum_extend
      · intro n hn
        obtain ⟨hnl,hnu⟩ := mem_Ioc.mp hn
        exact mem_Ioc.mpr ⟨Nat.lt_of_le_of_lt (Nat.zero_le _) hnl,hnu.trans (hU k hk)⟩
      · intro n hn
        obtain ⟨hnl,hnu⟩ := mem_Ioc.mp hn
        exact mem_Ioc.mpr ⟨Nat.lt_of_le_of_lt (Nat.zero_le _) hnl,hnu.trans (hV k hk)⟩
      · intro c b a hf
        exact amplificationBoxTerm_support B j hTpos (Real.exp_pos _) g h c b a (left_ne_zero_of_mul hf)
    _ = ∑ c ∈ Ioc 0 V, ∑ b ∈ Ioc 0 U, ∑ a ∈ Ioc 0 U,
        ∑ k ∈ S, (amplificationBoxTerm B j T (Real.exp ((k : ℝ)*Real.log 2)) g h c b a*countingRamp δ σ (b/(T*c))) :=
      sum_triple_interchange S (Ioc 0 U) (Ioc 0 V) _
    _ = _ := by
      apply sum_congr rfl
      intro c hc
      apply sum_congr rfl
      intro b _
      apply sum_congr rfl
      intro a _
      simp_rw [amplificationBoxTerm_eq B j hTpos (Real.exp_pos _) g h c b a,div_div_eq_mul_div]
      rw [show (∑ k ∈ S, amplificationArithmeticTerm B j T g h c b a*
          dyadicPartitionWeight ((c : ℝ)*T/Real.exp ((k : ℝ)*Real.log 2))*countingRamp δ σ (b/(T*c))) =
          (amplificationArithmeticTerm B j T g h c b a*
            ∑ k ∈ S, dyadicPartitionWeight ((c : ℝ)*T/Real.exp ((k : ℝ)*Real.log 2)))*countingRamp δ σ (b/(T*c)) by simp only [mul_sum, sum_mul]]
      by_cases he : amplificationArithmeticTerm B j T g h c b a = 0
      · simp [he]
      · have hBp : 0 < B := lt_of_lt_of_le (by norm_num) hB
        obtain ⟨hlo,hhi⟩ := amplificationArithmeticTerm_log_support hBp j T g h c b a he
        have hcp : (0 : ℝ) < c := by exact_mod_cast (mem_Ioc.mp hc).1
        obtain ⟨hcl,hcu⟩ := hbracket c hcp hlo hhi
        rw [geometric_dyadic_partition hLU (c*T) hcl hcu,mul_one]

end JointDickman

end OAI

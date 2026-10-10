import OAI.NumberTheory.JointDickman.Amplification.AmplificationBoxSupport
import OAI.NumberTheory.JointDickman.Counting.DyadicScaleWindow

namespace OAI

/-! # Exact reconstruction of the unpartitioned amplification triple sum -/

namespace JointDickman
open Finset

noncomputable def amplificationArithmeticSum (B j : ℕ) (T : ℝ) (U V : ℕ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) : ℝ :=
  B*∑ c ∈ Ioc 0 V, ∑ b ∈ Ioc 0 U, ∑ a ∈ Ioc 0 U,
    amplificationArithmeticTerm B j T g h c b a

theorem sum_triple_interchange {ι α β : Type*} (S : Finset ι) (A : Finset α) (C : Finset β)
    (f : ι → β → α → α → ℝ) :
    (∑ k ∈ S, ∑ c ∈ C, ∑ b ∈ A, ∑ a ∈ A, f k c b a) =
      ∑ c ∈ C, ∑ b ∈ A, ∑ a ∈ A, ∑ k ∈ S, f k c b a := by
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  exact sum_comm

theorem amplification_dyadic_identity {B : ℕ} (hB : 30 ≤ B) {T : ℝ}
    (hT : 1 ≤ T) (hlogT : Real.log T ≤ (B : ℝ)/10) (j U V : ℕ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (hU : ∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
      ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U)
    (hV : ∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
      ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊ ≤ V) :
    geometricSmoothArithmeticSum B j (1/4) (17/4) (1/4) (17/4) T (Real.log 2)
      (dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T))
      (fun k x y z => amplificationBoxWeight B (Real.log (Real.exp ((k : ℝ)*Real.log 2)/T)/B) x y z)
      g h = amplificationArithmeticSum B j T U V g h := by
  have hTpos := lt_of_lt_of_le zero_lt_one hT
  let S := dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T)
  obtain ⟨hLU,_,hbracket⟩ := dyadic_scale_window hB hT hlogT
  unfold geometricSmoothArithmeticSum amplificationArithmeticSum
  congr 1
  change (∑ k ∈ S,
      ∑ c ∈ Ioc ⌊(1/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊
        ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊,
      ∑ b ∈ Ioc ⌊(1/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊
        ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊,
      ∑ a ∈ Ioc ⌊(1/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊
        ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊,
        amplificationBoxTerm B j T (Real.exp ((k : ℝ)*Real.log 2)) g h c b a) = _
  calc
    _ = ∑ k ∈ S, ∑ c ∈ Ioc 0 V, ∑ b ∈ Ioc 0 U, ∑ a ∈ Ioc 0 U,
        amplificationBoxTerm B j T (Real.exp ((k : ℝ)*Real.log 2)) g h c b a := by
      apply sum_congr rfl
      intro k hk
      apply finite_triple_sum_extend
      · intro n hn
        obtain ⟨hnl,hnu⟩ := mem_Ioc.mp hn
        exact mem_Ioc.mpr ⟨Nat.lt_of_le_of_lt (Nat.zero_le _) hnl,hnu.trans (hU k hk)⟩
      · intro n hn
        obtain ⟨hnl,hnu⟩ := mem_Ioc.mp hn
        exact mem_Ioc.mpr ⟨Nat.lt_of_le_of_lt (Nat.zero_le _) hnl,hnu.trans (hV k hk)⟩
      · exact amplificationBoxTerm_support B j hTpos (Real.exp_pos _) g h
    _ = ∑ c ∈ Ioc 0 V, ∑ b ∈ Ioc 0 U, ∑ a ∈ Ioc 0 U,
        ∑ k ∈ S, amplificationBoxTerm B j T (Real.exp ((k : ℝ)*Real.log 2)) g h c b a :=
      sum_triple_interchange S (Ioc 0 U) (Ioc 0 V) _
    _ = _ := by
      apply sum_congr rfl
      intro c hc
      apply sum_congr rfl
      intro b _
      apply sum_congr rfl
      intro a _
      simp_rw [amplificationBoxTerm_eq B j hTpos (Real.exp_pos _) g h c b a,div_div_eq_mul_div]
      rw [← mul_sum]
      by_cases he : amplificationArithmeticTerm B j T g h c b a = 0
      · simp [he]
      · have hBp : 0 < B := lt_of_lt_of_le (by norm_num) hB
        obtain ⟨hlo,hhi⟩ := amplificationArithmeticTerm_log_support hBp j T g h c b a he
        have hcp : (0 : ℝ) < c := by exact_mod_cast (mem_Ioc.mp hc).1
        obtain ⟨hcl,hcu⟩ := hbracket c hcp hlo hhi
        rw [geometric_dyadic_partition hLU (c*T) hcl hcu,mul_one]

end JointDickman

end OAI

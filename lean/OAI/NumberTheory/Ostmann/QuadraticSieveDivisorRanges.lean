import OAI.NumberTheory.Ostmann.QuadraticSieveGcdSeparationBlocks

namespace OAI

namespace Ostmann.QuadraticSieve

theorem divisor_rectangle_norm_sq_le (D₁ D₂ V S T : Finset ℕ) (a b : ℕ → ℂ) (N : ℕ)
    (hD₁ : ∀ d ∈ D₁, 0 < d) (hD₂ : ∀ d ∈ D₂, 0 < d)
    (hV : ∀ v ∈ V, Odd v)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N ∧ Odd n)
    (hT : ∀ t ∈ T, 0 < t ∧ t ≤ N ∧ Odd t) :
    (∑ e ∈ D₁ ×ˢ D₂, ∑ v ∈ V,
      ‖coprimeDivisorJacobiRow S T a b e.1 e.2 (v : ℤ)‖) ^ 2 ≤
      4 * (D₁.card : ℝ) * (D₂.card : ℝ) * quotientNormMax V S D₁ * quotientNormMax V T D₂ *
        (∑ d ∈ D₁, divisorWeightedEnergy S d a) *
        (∑ d ∈ D₂, divisorWeightedEnergy T d b) := by
  have hA0 := quotientNormMax_nonneg V S D₁
  have hB0 := quotientNormMax_nonneg V T D₂
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (D₁ ×ˢ D₂)
    (f := fun e => 2 * quotientNormMax V S D₁ * divisorWeightedEnergy S e.1 a)
    (g := fun e => 2 * quotientNormMax V T D₂ * divisorWeightedEnergy T e.2 b)
    (r := fun e => ∑ v ∈ V, ‖coprimeDivisorJacobiRow S T a b e.1 e.2 (v : ℤ)‖)
    (fun _ _ => mul_nonneg (mul_nonneg (by norm_num) hA0) (divisorWeightedEnergy_nonneg _ _ _))
    (fun _ _ => mul_nonneg (mul_nonneg (by norm_num) hB0) (divisorWeightedEnergy_nonneg _ _ _))
    (fun e he => by
      obtain ⟨he₁, he₂⟩ := Finset.mem_product.mp he
      let : NeZero e.1 := ⟨(hD₁ e.1 he₁).ne'⟩
      let : NeZero e.2 := ⟨(hD₂ e.2 he₂).ne'⟩
      apply (coprimeDivisorJacobiRow_norm_sq_le V S T a b e.1 e.2 N hV hS hT).trans
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (quadraticNorm_le_quotientNormMax V S D₁ he₁) (by norm_num))
          (divisorWeightedEnergy_nonneg _ _ _)
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (quadraticNorm_le_quotientNormMax V T D₂ he₂) (by norm_num))
          (divisorWeightedEnergy_nonneg _ _ _)
      · exact mul_nonneg (mul_nonneg (by norm_num) (quadraticNorm_nonneg _ _))
          (divisorWeightedEnergy_nonneg _ _ _)
      · exact mul_nonneg (mul_nonneg (by norm_num) hA0) (divisorWeightedEnergy_nonneg _ _ _))
  have hfirst : (∑ e ∈ D₁ ×ˢ D₂,
      2 * quotientNormMax V S D₁ * divisorWeightedEnergy S e.1 a) =
      (D₂.card : ℝ) * (2 * quotientNormMax V S D₁) *
        ∑ d ∈ D₁, divisorWeightedEnergy S d a := by
    rw [Finset.sum_product]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    ring
  have hsecond : (∑ e ∈ D₁ ×ˢ D₂,
      2 * quotientNormMax V T D₂ * divisorWeightedEnergy T e.2 b) =
      (D₁.card : ℝ) * (2 * quotientNormMax V T D₂) *
        ∑ d ∈ D₂, divisorWeightedEnergy T d b := by
    rw [Finset.sum_product]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    ring
  rw [hfirst, hsecond] at hcs
  convert hcs using 1
  ring

theorem divisor_rectangle_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D₁ D₂ V S T : Finset ℕ) (a b : ℕ → ℂ) (N L₁ L₂ : ℕ),
      0 < L₁ → 0 < L₂ → (∀ d ∈ D₁, L₁ ≤ d) → (∀ d ∈ D₂, L₂ ≤ d) →
      (∀ v ∈ V, Odd v) → S ⊆ oddSquarefreeUpTo N → T ⊆ oddSquarefreeUpTo N →
      (∑ e ∈ D₁ ×ˢ D₂, ∑ v ∈ V,
        ‖coprimeDivisorJacobiRow S T a b e.1 e.2 (v : ℤ)‖) ^ 2 ≤
        C * (N : ℝ) ^ ε * (D₁.card : ℝ) * (D₂.card : ℝ) *
          quadraticNorm V (oddSquarefreeUpTo (N / L₁)) *
          quadraticNorm V (oddSquarefreeUpTo (N / L₂)) *
          coefficientEnergy S a * coefficientEnergy T b := by
  obtain ⟨C,hC,hdiv⟩ := sum_divisorWeightedEnergy_le_rpow (ε / 2) (by positivity)
  refine ⟨4 * C ^ 2, by positivity, ?_⟩
  intro D₁ D₂ V S T a b N L₁ L₂ hL₁ hL₂ hD₁ hD₂ hV hS hT
  have hS' (n) (hn : n ∈ S) : 0 < n ∧ n ≤ N ∧ Odd n := by
    obtain ⟨hp,hu,ho,hs⟩ := mem_oddSquarefreeUpTo.mp (hS hn)
    exact ⟨hp,hu,ho⟩
  have hT' (t) (ht : t ∈ T) : 0 < t ∧ t ≤ N ∧ Odd t := by
    obtain ⟨hp,hu,ho,hs⟩ := mem_oddSquarefreeUpTo.mp (hT ht)
    exact ⟨hp,hu,ho⟩
  have hQA := quotientNormMax_le_oddSquarefreeUpTo V hS hL₁ hD₁
  have hQB := quotientNormMax_le_oddSquarefreeUpTo V hT hL₂ hD₂
  have hEA := hdiv N D₁ S a (fun n hn => ⟨(hS' n hn).1,(hS' n hn).2.1⟩)
  have hEB := hdiv N D₂ T b (fun t ht => ⟨(hT' t ht).1,(hT' t ht).2.1⟩)
  have hQA0 := quotientNormMax_nonneg V S D₁
  have hQB0 := quotientNormMax_nonneg V T D₂
  have hQA1 := quadraticNorm_nonneg V (oddSquarefreeUpTo (N / L₁))
  have hQB1 := quadraticNorm_nonneg V (oddSquarefreeUpTo (N / L₂))
  have hEA0 : 0 ≤ ∑ d ∈ D₁, divisorWeightedEnergy S d a :=
    Finset.sum_nonneg (fun _ _ => divisorWeightedEnergy_nonneg _ _ _)
  have hEB0 : 0 ≤ ∑ d ∈ D₂, divisorWeightedEnergy T d b :=
    Finset.sum_nonneg (fun _ _ => divisorWeightedEnergy_nonneg _ _ _)
  have hEa := coefficientEnergy_nonneg S a
  have hEb := coefficientEnergy_nonneg T b
  have hpow : ((N : ℝ) ^ (ε / 2)) ^ 2 = (N : ℝ) ^ ε := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    congr 1
    ring
  apply (divisor_rectangle_norm_sq_le D₁ D₂ V S T a b N
    (fun d hd => hL₁.trans_le (hD₁ d hd)) (fun d hd => hL₂.trans_le (hD₂ d hd)) hV hS' hT').trans
  calc
    _ ≤ 4 * (D₁.card : ℝ) * (D₂.card : ℝ) *
        quadraticNorm V (oddSquarefreeUpTo (N / L₁)) *
        quadraticNorm V (oddSquarefreeUpTo (N / L₂)) *
        (C * (N : ℝ) ^ (ε / 2) * coefficientEnergy S a) *
        (C * (N : ℝ) ^ (ε / 2) * coefficientEnergy T b) := by
      gcongr
    _ = (4 * C ^ 2) * ((N : ℝ) ^ (ε / 2)) ^ 2 * (D₁.card : ℝ) * (D₂.card : ℝ) *
        quadraticNorm V (oddSquarefreeUpTo (N / L₁)) *
        quadraticNorm V (oddSquarefreeUpTo (N / L₂)) *
        coefficientEnergy S a * coefficientEnergy T b := by ring
    _ = _ := by rw [hpow]

end Ostmann.QuadraticSieve

end OAI

import OAI.NumberTheory.Ostmann.QuadraticSieveGcdSeparationProduct
import OAI.NumberTheory.Ostmann.QuadraticSieveNormSupport

namespace OAI

namespace Ostmann.QuadraticSieve

noncomputable def divisorPairJacobiRow (E : Finset (ℕ × ℕ))
    (S T : Finset ℕ) (a b : ℕ → ℂ) (m : ℤ) : ℂ :=
  ∑ e ∈ E, coprimeDivisorJacobiRow S T a b e.1 e.2 m

theorem divisorPairJacobiRow_norm_sq_le (E : Finset (ℕ × ℕ))
    (V S T : Finset ℕ) (a b : ℕ → ℂ) (d N : ℕ)
    (hE : E ⊆ d.divisorsAntidiagonal)
    (hV : ∀ v ∈ V, Odd v)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N ∧ Odd n)
    (hT : ∀ t ∈ T, 0 < t ∧ t ≤ N ∧ Odd t) :
    (∑ v ∈ V, ‖divisorPairJacobiRow E S T a b (v : ℤ)‖) ^ 2 ≤
      (∑ e ∈ E, 2 * quadraticNorm V (quotientSupport S e.1) * divisorWeightedEnergy S e.1 a) *
      (∑ e ∈ E, 2 * quadraticNorm V (quotientSupport T e.2) * divisorWeightedEnergy T e.2 b) := by
  have htri : (∑ v ∈ V, ‖divisorPairJacobiRow E S T a b (v : ℤ)‖) ≤
      ∑ e ∈ E, ∑ v ∈ V, ‖coprimeDivisorJacobiRow S T a b e.1 e.2 (v : ℤ)‖ := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum (fun v hv => norm_sum_le _ _)
  apply (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) htri 2).trans
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul E
    (fun _ _ => mul_nonneg (mul_nonneg (by norm_num) (quadraticNorm_nonneg _ _))
      (divisorWeightedEnergy_nonneg _ _ _))
    (fun _ _ => mul_nonneg (mul_nonneg (by norm_num) (quadraticNorm_nonneg _ _))
      (divisorWeightedEnergy_nonneg _ _ _))
  intro e he
  have he' := Nat.mem_divisorsAntidiagonal.mp (hE he)
  have hmul : e.1 * e.2 ≠ 0 := he'.1 ▸ he'.2
  let : NeZero e.1 := ⟨(mul_ne_zero_iff.mp hmul).1⟩
  let : NeZero e.2 := ⟨(mul_ne_zero_iff.mp hmul).2⟩
  exact coprimeDivisorJacobiRow_norm_sq_le V S T a b e.1 e.2 N hV hS hT

theorem sum_divisorPairWeightedEnergy_le (E : Finset (ℕ × ℕ))
    (S : Finset ℕ) (a : ℕ → ℂ) (d : ℕ) (hE : E ⊆ d.divisorsAntidiagonal) :
    (∑ e ∈ E, divisorWeightedEnergy S e.1 a) ≤ ∑ e ∈ d.divisors, divisorWeightedEnergy S e a := by
  calc
    _ ≤ ∑ e ∈ d.divisorsAntidiagonal, divisorWeightedEnergy S e.1 a :=
      Finset.sum_le_sum_of_subset_of_nonneg hE (fun e he hn => divisorWeightedEnergy_nonneg _ _ _)
    _ = _ := Nat.sum_divisorsAntidiagonal (fun e _ => divisorWeightedEnergy S e a)

theorem sum_divisorPairWeightedEnergy_snd_le (E : Finset (ℕ × ℕ))
    (S : Finset ℕ) (a : ℕ → ℂ) (d : ℕ) (hE : E ⊆ d.divisorsAntidiagonal) :
    (∑ e ∈ E, divisorWeightedEnergy S e.2 a) ≤ ∑ e ∈ d.divisors, divisorWeightedEnergy S e a := by
  calc
    _ ≤ ∑ e ∈ d.divisorsAntidiagonal, divisorWeightedEnergy S e.2 a :=
      Finset.sum_le_sum_of_subset_of_nonneg hE (fun e he hn => divisorWeightedEnergy_nonneg _ _ _)
    _ = _ := Nat.sum_divisorsAntidiagonal' (fun _ e => divisorWeightedEnergy S e a)

theorem quotientNormMax_le_oddSquarefreeUpTo (V : Finset ℕ) {S D : Finset ℕ} {U L : ℕ}
    (hS : S ⊆ oddSquarefreeUpTo U) (hL : 0 < L) (hD : ∀ d ∈ D, L ≤ d) :
    quotientNormMax V S D ≤ quadraticNorm V (oddSquarefreeUpTo (U / L)) := by
  have h : (D.sup (fun d => (⟨quadraticNorm V (quotientSupport S d),
      quadraticNorm_nonneg _ _⟩ : NNReal))) ≤
      (⟨quadraticNorm V (oddSquarefreeUpTo (U / L)), quadraticNorm_nonneg _ _⟩ : NNReal) := by
    apply Finset.sup_le
    intro d hd
    change quadraticNorm V (quotientSupport S d) ≤ quadraticNorm V (oddSquarefreeUpTo (U / L))
    apply quadraticNorm_mono_columns
    intro n hn
    obtain ⟨hn1, hnU, hno, hnsq⟩ := mem_oddSquarefreeUpTo.mp
      (quotientSupport_subset_oddSquarefreeUpTo hS hn)
    exact mem_oddSquarefreeUpTo.mpr ⟨hn1, hnU.trans (Nat.div_le_div_left (hD d hd) hL), hno, hnsq⟩
  exact_mod_cast h

theorem divisorPairJacobiRow_norm_sq_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : Finset (ℕ × ℕ)) (V S T : Finset ℕ)
      (a b : ℕ → ℂ) (d N : ℕ), E ⊆ d.divisorsAntidiagonal →
      (∀ v ∈ V, Odd v) → (∀ n ∈ S, 0 < n ∧ n ≤ N ∧ Odd n) →
      (∀ t ∈ T, 0 < t ∧ t ≤ N ∧ Odd t) →
      (∑ v ∈ V, ‖divisorPairJacobiRow E S T a b (v : ℤ)‖) ^ 2 ≤
        C * (N : ℝ) ^ ε * quotientNormMax V S (E.image Prod.fst) *
          quotientNormMax V T (E.image Prod.snd) * coefficientEnergy S a * coefficientEnergy T b := by
  classical
  obtain ⟨C, hC, hdiv⟩ := sum_divisorWeightedEnergy_le_rpow (ε / 2) (by positivity)
  refine ⟨4 * C ^ 2, by positivity, ?_⟩
  intro E V S T a b d N hE hV hS hT
  have hA : (∑ e ∈ E, 2 * quadraticNorm V (quotientSupport S e.1) * divisorWeightedEnergy S e.1 a) ≤
      2 * quotientNormMax V S (E.image Prod.fst) *
        (C * (N : ℝ) ^ (ε / 2) * coefficientEnergy S a) := by
    calc
      _ ≤ 2 * quotientNormMax V S (E.image Prod.fst) *
          ∑ e ∈ E, divisorWeightedEnergy S e.1 a := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro e he
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (quadraticNorm_le_quotientNormMax V S _ (Finset.mem_image_of_mem Prod.fst he))
          (by norm_num)) (divisorWeightedEnergy_nonneg _ _ _)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((sum_divisorPairWeightedEnergy_le E S a d hE).trans
          (hdiv N d.divisors S a (fun n hn => ⟨(hS n hn).1, (hS n hn).2.1⟩)))
        (mul_nonneg (by norm_num) (quotientNormMax_nonneg _ _ _))
  have hB : (∑ e ∈ E, 2 * quadraticNorm V (quotientSupport T e.2) * divisorWeightedEnergy T e.2 b) ≤
      2 * quotientNormMax V T (E.image Prod.snd) *
        (C * (N : ℝ) ^ (ε / 2) * coefficientEnergy T b) := by
    calc
      _ ≤ 2 * quotientNormMax V T (E.image Prod.snd) *
          ∑ e ∈ E, divisorWeightedEnergy T e.2 b := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro e he
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (quadraticNorm_le_quotientNormMax V T _ (Finset.mem_image_of_mem Prod.snd he))
          (by norm_num)) (divisorWeightedEnergy_nonneg _ _ _)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((sum_divisorPairWeightedEnergy_snd_le E T b d hE).trans
          (hdiv N d.divisors T b (fun n hn => ⟨(hT n hn).1, (hT n hn).2.1⟩)))
        (mul_nonneg (by norm_num) (quotientNormMax_nonneg _ _ _))
  have hA0 : 0 ≤ ∑ e ∈ E,
      2 * quadraticNorm V (quotientSupport S e.1) * divisorWeightedEnergy S e.1 a :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (mul_nonneg (by norm_num) (quadraticNorm_nonneg _ _))
      (divisorWeightedEnergy_nonneg _ _ _))
  have hB0 : 0 ≤ ∑ e ∈ E,
      2 * quadraticNorm V (quotientSupport T e.2) * divisorWeightedEnergy T e.2 b :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (mul_nonneg (by norm_num) (quadraticNorm_nonneg _ _))
      (divisorWeightedEnergy_nonneg _ _ _))
  have hpow : ((N : ℝ) ^ (ε / 2)) ^ 2 = (N : ℝ) ^ ε := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    congr 1
    ring
  apply (divisorPairJacobiRow_norm_sq_le E V S T a b d N hE hV hS hT).trans
  calc
    _ ≤ (2 * quotientNormMax V S (E.image Prod.fst) *
        (C * (N : ℝ) ^ (ε / 2) * coefficientEnergy S a)) *
        (2 * quotientNormMax V T (E.image Prod.snd) *
        (C * (N : ℝ) ^ (ε / 2) * coefficientEnergy T b)) :=
      mul_le_mul hA hB hB0 (hA0.trans hA)
    _ = (4 * C ^ 2) * ((N : ℝ) ^ (ε / 2)) ^ 2 *
        quotientNormMax V S (E.image Prod.fst) * quotientNormMax V T (E.image Prod.snd) *
        coefficientEnergy S a * coefficientEnergy T b := by ring
    _ = _ := by rw [hpow]

end Ostmann.QuadraticSieve

end OAI

import OAI.NumberTheory.Ostmann.QuadraticSieveGcdSeparationBlocks

namespace OAI

namespace Ostmann.QuadraticSieve

theorem exists_max_paired_quotientNorm (V S T : Finset ℕ) {d : ℕ} (hd : d ≠ 0) :
    ∃ e ∈ d.divisorsAntidiagonal, ∀ f ∈ d.divisorsAntidiagonal,
      quadraticNorm V (quotientSupport S f.1) * quadraticNorm V (quotientSupport T f.2) ≤
        quadraticNorm V (quotientSupport S e.1) * quadraticNorm V (quotientSupport T e.2) := by
  have hne : d.divisorsAntidiagonal.Nonempty :=
    ⟨(1, d), Nat.mem_divisorsAntidiagonal.mpr ⟨one_mul d, hd⟩⟩
  exact Finset.exists_max_image d.divisorsAntidiagonal (fun e =>
    quadraticNorm V (quotientSupport S e.1) * quadraticNorm V (quotientSupport T e.2)) hne

theorem coprimeProductDivisorJacobiRow_norm_sq_le_paired
    (V S T : Finset ℕ) (a b : ℕ → ℂ) (d N : ℕ) (hd : d ≠ 0)
    (hV : ∀ v ∈ V, Odd v)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N ∧ Odd n)
    (hT : ∀ t ∈ T, 0 < t ∧ t ≤ N ∧ Odd t) :
    ∃ e ∈ d.divisorsAntidiagonal,
      (∑ v ∈ V, ‖coprimeProductDivisorJacobiRow S T a b d (v : ℤ)‖) ^ 2 ≤
        4 * (quadraticNorm V (quotientSupport S e.1) *
          quadraticNorm V (quotientSupport T e.2)) *
          (∑ f ∈ d.divisors, divisorWeightedEnergy S f a) *
          (∑ f ∈ d.divisors, divisorWeightedEnergy T f b) := by
  obtain ⟨e, he, hmax⟩ := exists_max_paired_quotientNorm V S T hd
  refine ⟨e, he, ?_⟩
  let K := quadraticNorm V (quotientSupport S e.1) * quadraticNorm V (quotientSupport T e.2)
  have hK : 0 ≤ K := mul_nonneg (quadraticNorm_nonneg _ _) (quadraticNorm_nonneg _ _)
  have htri : (∑ v ∈ V, ‖coprimeProductDivisorJacobiRow S T a b d (v : ℤ)‖) ≤
      ∑ f ∈ d.divisorsAntidiagonal,
        ∑ v ∈ V, ‖coprimeDivisorJacobiRow S T a b f.1 f.2 (v : ℤ)‖ := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro v hv
    rw [coprimeProductDivisorJacobiRow_eq S T a b d hd]
    exact norm_sum_le _ _
  apply (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) htri 2).trans
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul d.divisorsAntidiagonal
    (f := fun f => 4 * K * divisorWeightedEnergy S f.1 a)
    (g := fun f => divisorWeightedEnergy T f.2 b)
    (r := fun f => ∑ v ∈ V, ‖coprimeDivisorJacobiRow S T a b f.1 f.2 (v : ℤ)‖)
    (fun _ _ => mul_nonneg (mul_nonneg (by norm_num) hK) (divisorWeightedEnergy_nonneg _ _ _))
    (fun _ _ => divisorWeightedEnergy_nonneg _ _ _)
    (fun f hf => by
      have hf' := Nat.mem_divisorsAntidiagonal.mp hf
      have hmul : f.1 * f.2 ≠ 0 := hf'.1 ▸ hd
      let : NeZero f.1 := ⟨(mul_ne_zero_iff.mp hmul).1⟩
      let : NeZero f.2 := ⟨(mul_ne_zero_iff.mp hmul).2⟩
      apply (coprimeDivisorJacobiRow_norm_sq_le V S T a b f.1 f.2 N hV hS hT).trans
      calc
        _ = 4 * (quadraticNorm V (quotientSupport S f.1) *
            quadraticNorm V (quotientSupport T f.2)) *
            (divisorWeightedEnergy S f.1 a * divisorWeightedEnergy T f.2 b) := by ring
        _ ≤ 4 * K * (divisorWeightedEnergy S f.1 a * divisorWeightedEnergy T f.2 b) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hmax f hf) (by norm_num))
            (mul_nonneg (divisorWeightedEnergy_nonneg _ _ _) (divisorWeightedEnergy_nonneg _ _ _))
        _ = _ := by ring)
  rw [← Finset.mul_sum,
    Nat.sum_divisorsAntidiagonal (fun f _ => divisorWeightedEnergy S f a),
    Nat.sum_divisorsAntidiagonal' (fun _ f => divisorWeightedEnergy T f b)] at hcs
  exact hcs

theorem exists_gcd_separation_scales (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V S T : Finset ℕ) (a b : ℕ → ℂ) (d N : ℕ),
      d ≠ 0 → (∀ v ∈ V, Odd v) → S ⊆ oddSquarefreeUpTo N → T ⊆ oddSquarefreeUpTo N →
      ∃ d₁ d₂ : ℕ, 0 < d₁ ∧ 0 < d₂ ∧ d₁ * d₂ = d ∧
        (∑ v ∈ V, ‖coprimeProductDivisorJacobiRow S T a b d (v : ℤ)‖) ^ 2 ≤
          C * (N : ℝ) ^ ε * quadraticNorm V (oddSquarefreeUpTo (N / d₁)) *
            quadraticNorm V (oddSquarefreeUpTo (N / d₂)) *
            coefficientEnergy S a * coefficientEnergy T b := by
  obtain ⟨C, hC, hdiv⟩ := sum_divisorWeightedEnergy_le_rpow (ε / 2) (by positivity)
  refine ⟨4 * C ^ 2, by positivity, ?_⟩
  intro V S T a b d N hd hV hS hT
  have hS' : ∀ n ∈ S, 0 < n ∧ n ≤ N ∧ Odd n := by
    intro n hn
    obtain ⟨hn1, hnN, hno, _⟩ := mem_oddSquarefreeUpTo.mp (hS hn)
    exact ⟨hn1, hnN, hno⟩
  have hT' : ∀ t ∈ T, 0 < t ∧ t ≤ N ∧ Odd t := by
    intro t ht
    obtain ⟨ht1, htN, hto, _⟩ := mem_oddSquarefreeUpTo.mp (hT ht)
    exact ⟨ht1, htN, hto⟩
  obtain ⟨e, he, hle⟩ := coprimeProductDivisorJacobiRow_norm_sq_le_paired V S T a b d N hd hV hS' hT'
  have he' := Nat.mem_divisorsAntidiagonal.mp he
  have hmul : e.1 * e.2 ≠ 0 := he'.1 ▸ hd
  refine ⟨e.1, e.2, Nat.pos_of_ne_zero (mul_ne_zero_iff.mp hmul).1,
    Nat.pos_of_ne_zero (mul_ne_zero_iff.mp hmul).2, he'.1, ?_⟩
  have hA := hdiv N d.divisors S a (fun n hn => ⟨(hS' n hn).1, (hS' n hn).2.1⟩)
  have hB := hdiv N d.divisors T b (fun n hn => ⟨(hT' n hn).1, (hT' n hn).2.1⟩)
  have hA0 : 0 ≤ ∑ f ∈ d.divisors, divisorWeightedEnergy S f a :=
    Finset.sum_nonneg (fun _ _ => divisorWeightedEnergy_nonneg _ _ _)
  have hB0 : 0 ≤ ∑ f ∈ d.divisors, divisorWeightedEnergy T f b :=
    Finset.sum_nonneg (fun _ _ => divisorWeightedEnergy_nonneg _ _ _)
  have hpow : ((N : ℝ) ^ (ε / 2)) ^ 2 = (N : ℝ) ^ ε := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    congr 1
    ring
  have hQA := quadraticNorm_mono_columns V (quotientSupport_subset_oddSquarefreeUpTo hS (d := e.1))
  have hQB := quadraticNorm_mono_columns V (quotientSupport_subset_oddSquarefreeUpTo hT (d := e.2))
  apply hle.trans
  calc
    _ ≤ 4 * (quadraticNorm V (quotientSupport S e.1) * quadraticNorm V (quotientSupport T e.2)) *
        ((C * (N : ℝ) ^ (ε / 2) * coefficientEnergy S a) *
          (C * (N : ℝ) ^ (ε / 2) * coefficientEnergy T b)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hA hB hB0 (hA0.trans hA))
        (mul_nonneg (by norm_num) (mul_nonneg (quadraticNorm_nonneg _ _) (quadraticNorm_nonneg _ _)))
    _ = (4 * C ^ 2) * (N : ℝ) ^ ε *
        (quadraticNorm V (quotientSupport S e.1) * quadraticNorm V (quotientSupport T e.2)) *
        coefficientEnergy S a * coefficientEnergy T b := by
      rw [← hpow]
      ring
    _ ≤ _ := by
      have hQ := mul_le_mul hQA hQB (quadraticNorm_nonneg _ _) (quadraticNorm_nonneg _ _)
      have hE0 : 0 ≤ coefficientEnergy S a * coefficientEnergy T b :=
        mul_nonneg (coefficientEnergy_nonneg _ _) (coefficientEnergy_nonneg _ _)
      have hconst : 0 ≤ (4 * C ^ 2) * (N : ℝ) ^ ε := by positivity
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQ hconst) hE0
      simpa only [mul_assoc] using hh

end Ostmann.QuadraticSieve

end OAI

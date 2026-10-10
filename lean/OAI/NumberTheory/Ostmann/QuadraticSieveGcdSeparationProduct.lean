import OAI.NumberTheory.Ostmann.QuadraticSieveGcdSeparationBound
import OAI.NumberTheory.Ostmann.QuadraticSieveGcdSeparationDivisors

namespace OAI

namespace Ostmann.QuadraticSieve

noncomputable def coprimeProductDivisorJacobiRow (S T : Finset ℕ) (a b : ℕ → ℂ)
    (d : ℕ) (m : ℤ) : ℂ :=
  ∑ n ∈ S, ∑ t ∈ T,
    if n.Coprime t ∧ d ∣ n * t then a n * b t * (jacobiSym m (n * t) : ℂ) else 0

theorem coprimeProductDivisorJacobiRow_eq (S T : Finset ℕ) (a b : ℕ → ℂ)
    (d : ℕ) (hd : d ≠ 0) (m : ℤ) :
    coprimeProductDivisorJacobiRow S T a b d m =
      ∑ e ∈ d.divisorsAntidiagonal, coprimeDivisorJacobiRow S T a b e.1 e.2 m :=
  coprime_product_divisor_partition S T _ d hd

noncomputable def divisorNormEnergy (V S : Finset ℕ) (d : ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ e ∈ d.divisors,
    2 * quadraticNorm V (quotientSupport S e) * divisorWeightedEnergy S e a

lemma divisorNormEnergy_nonneg (V S : Finset ℕ) (d : ℕ) (a : ℕ → ℂ) :
    0 ≤ divisorNormEnergy V S d a :=
  Finset.sum_nonneg (fun e he => mul_nonneg
    (mul_nonneg (by norm_num) (quadraticNorm_nonneg _ _))
    (divisorWeightedEnergy_nonneg _ _ _))

theorem coprimeProductDivisorJacobiRow_norm_sq_le
    (V S T : Finset ℕ) (a b : ℕ → ℂ) (d N : ℕ) (hd : d ≠ 0)
    (hV : ∀ v ∈ V, Odd v)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N ∧ Odd n)
    (hT : ∀ t ∈ T, 0 < t ∧ t ≤ N ∧ Odd t) :
    (∑ v ∈ V, ‖coprimeProductDivisorJacobiRow S T a b d (v : ℤ)‖) ^ 2 ≤
      divisorNormEnergy V S d a * divisorNormEnergy V T d b := by
  have htri : (∑ v ∈ V, ‖coprimeProductDivisorJacobiRow S T a b d (v : ℤ)‖) ≤
      ∑ e ∈ d.divisorsAntidiagonal,
        ∑ v ∈ V, ‖coprimeDivisorJacobiRow S T a b e.1 e.2 (v : ℤ)‖ := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro v hv
    rw [coprimeProductDivisorJacobiRow_eq S T a b d hd]
    exact norm_sum_le _ _
  apply (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) htri 2).trans
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul d.divisorsAntidiagonal
    (f := fun e => 2 * quadraticNorm V (quotientSupport S e.1) * divisorWeightedEnergy S e.1 a)
    (g := fun e => 2 * quadraticNorm V (quotientSupport T e.2) * divisorWeightedEnergy T e.2 b)
    (r := fun e => ∑ v ∈ V, ‖coprimeDivisorJacobiRow S T a b e.1 e.2 (v : ℤ)‖)
    (fun _ _ => mul_nonneg (mul_nonneg (by norm_num) (quadraticNorm_nonneg _ _))
      (divisorWeightedEnergy_nonneg _ _ _))
    (fun _ _ => mul_nonneg (mul_nonneg (by norm_num) (quadraticNorm_nonneg _ _))
      (divisorWeightedEnergy_nonneg _ _ _)) (fun e he => by
        have hmul : e.1 * e.2 ≠ 0 := by
          rw [(Nat.mem_divisorsAntidiagonal.mp he).1]
          exact hd
        let : NeZero e.1 := ⟨(mul_ne_zero_iff.mp hmul).1⟩
        let : NeZero e.2 := ⟨(mul_ne_zero_iff.mp hmul).2⟩
        exact coprimeDivisorJacobiRow_norm_sq_le V S T a b e.1 e.2 N hV hS hT)
  rw [Nat.sum_divisorsAntidiagonal (fun e _ =>
      2 * quadraticNorm V (quotientSupport S e) * divisorWeightedEnergy S e a),
    Nat.sum_divisorsAntidiagonal' (fun _ e =>
      2 * quadraticNorm V (quotientSupport T e) * divisorWeightedEnergy T e b)] at hcs
  exact hcs

noncomputable def quotientNormMax (V S D : Finset ℕ) : ℝ :=
  ((D.sup (fun d => (⟨quadraticNorm V (quotientSupport S d),
    quadraticNorm_nonneg _ _⟩ : NNReal)) : NNReal) : ℝ)

lemma quotientNormMax_nonneg (V S D : Finset ℕ) : 0 ≤ quotientNormMax V S D :=
  NNReal.coe_nonneg _

lemma quadraticNorm_le_quotientNormMax (V S D : Finset ℕ) {d : ℕ} (hd : d ∈ D) :
    quadraticNorm V (quotientSupport S d) ≤ quotientNormMax V S D := by
  exact_mod_cast Finset.le_sup (f := fun d => (⟨quadraticNorm V (quotientSupport S d),
    quadraticNorm_nonneg _ _⟩ : NNReal)) hd

lemma divisorNormEnergy_le (V S : Finset ℕ) (d : ℕ) (a : ℕ → ℂ) :
    divisorNormEnergy V S d a ≤ 2 * quotientNormMax V S d.divisors *
      ∑ e ∈ d.divisors, divisorWeightedEnergy S e a := by
  unfold divisorNormEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (quadraticNorm_le_quotientNormMax V S d.divisors he)
      (by norm_num)) (divisorWeightedEnergy_nonneg _ _ _)

theorem coprimeProductDivisorJacobiRow_norm_sq_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V S T : Finset ℕ) (a b : ℕ → ℂ) (d N : ℕ),
      d ≠ 0 → (∀ v ∈ V, Odd v) →
      (∀ n ∈ S, 0 < n ∧ n ≤ N ∧ Odd n) →
      (∀ t ∈ T, 0 < t ∧ t ≤ N ∧ Odd t) →
      (∑ v ∈ V, ‖coprimeProductDivisorJacobiRow S T a b d (v : ℤ)‖) ^ 2 ≤
        C * (N : ℝ) ^ ε * quotientNormMax V S d.divisors *
          quotientNormMax V T d.divisors * coefficientEnergy S a * coefficientEnergy T b := by
  obtain ⟨C, hC, hdiv⟩ := sum_divisorWeightedEnergy_le_rpow (ε / 2) (by positivity)
  refine ⟨4 * C ^ 2, by positivity, ?_⟩
  intro V S T a b d N hd hV hS hT
  have hA := (divisorNormEnergy_le V S d a).trans
    (mul_le_mul_of_nonneg_left
      (hdiv N d.divisors S a (fun n hn => ⟨(hS n hn).1, (hS n hn).2.1⟩))
      (mul_nonneg (by norm_num) (quotientNormMax_nonneg _ _ _)))
  have hB := (divisorNormEnergy_le V T d b).trans
    (mul_le_mul_of_nonneg_left
      (hdiv N d.divisors T b (fun n hn => ⟨(hT n hn).1, (hT n hn).2.1⟩))
      (mul_nonneg (by norm_num) (quotientNormMax_nonneg _ _ _)))
  have hpow : ((N : ℝ) ^ (ε / 2)) ^ 2 = (N : ℝ) ^ ε := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    congr 1
    ring
  apply (coprimeProductDivisorJacobiRow_norm_sq_le V S T a b d N hd hV hS hT).trans
  calc
    _ ≤ (2 * quotientNormMax V S d.divisors *
        (C * (N : ℝ) ^ (ε / 2) * coefficientEnergy S a)) *
        (2 * quotientNormMax V T d.divisors *
        (C * (N : ℝ) ^ (ε / 2) * coefficientEnergy T b)) :=
      mul_le_mul hA hB (divisorNormEnergy_nonneg _ _ _ _)
        ((divisorNormEnergy_nonneg _ _ _ _).trans hA)
    _ = (4 * C ^ 2) * ((N : ℝ) ^ (ε / 2)) ^ 2 *
        quotientNormMax V S d.divisors * quotientNormMax V T d.divisors *
        coefficientEnergy S a * coefficientEnergy T b := by ring
    _ = _ := by rw [hpow]

end Ostmann.QuadraticSieve

end OAI

import OAI.NumberTheory.DirichletL.Moments.ProductCRT

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentPartition
open CenteredMomentCorrelation CenteredMomentCommonSupport

section Domain
variable {A : Type*} [CommRing A]
theorem fullModulusCorrelation_swap (u v h : A)
    [Fintype (Residue u)] [Fintype (Residue v)]
    (χ : MulChar (Residue u) ℂ) (ψ : MulChar (Residue v) ℂ) :
    fullModulusCorrelation u v χ ψ h = star (fullModulusCorrelation v u ψ χ (-h)) := by
  simp only [fullModulusCorrelation, fullCorrelation, star_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have he : u * v ∣ v * x - u * y - h ↔ v * u ∣ u * y - v * x - (-h) := by
    rw [mul_comm v u, show u * y - v * x - (-h) = -(v * x - u * y - h) by ring,
      dvd_neg]
  simp only [scaledResidue_congruence]
  by_cases hc : u * v ∣ v * x - u * y - h
  · simp only [hc, he.mp hc, ite_true, star_mul, star_star]
  · simp only [hc, (not_congr he).mp hc, ite_false, star_zero]
end Domain

open ActualEisensteinCubic ConcreteTraceCRT CanonicalQuadraticSieve
open CenteredMomentSupportedCorrelation CenteredMomentUnequal CenteredMomentLocal
open CenteredMomentProductCRT
open ConcretePrimeRowBridge hiding O
local notation "O" => ActualEisensteinCubic.O

theorem actualCorrelation_norm_swap (u v : O)
    (hu : Supported (Ideal.span {u})) (hv : Supported (Ideal.span {v})) (h : O) :
    ‖actualCorrelation u v hu hv h‖ = ‖actualCorrelation v u hv hu (-h)‖ := by
  let := finite_quotient_span (supported_element_ne_zero u hu)
  let := finite_quotient_span (supported_element_ne_zero v hv)
  let : Fintype (Residue u) := Fintype.ofFinite _
  let : Fintype (Residue v) := Fintype.ofFinite _
  change ‖fullModulusCorrelation u v _ _ h‖ = ‖fullModulusCorrelation v u _ _ (-h)‖
  rw [fullModulusCorrelation_swap, norm_star]

theorem prime_power_norm_le_min (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    {c d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d) (k : O) :
    ‖actualCorrelation (p ^ c) (p ^ d) (supported_power p hp c) (supported_power p hp d)
      (p ^ min c d * k)‖ ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ min c d := by
  rcases lt_trichotomy c d with hcd | heq | hdc
  · have he : c + (d - c) = d := Nat.add_sub_of_le hcd.le
    have h := unequal_prime_power_norm_le p hp hg hc (show 1 ≤ d - c by omega) (-k)
    rw [actualCorrelation_norm_swap]
    simpa only [← pow_add, he, min_eq_left hcd.le, mul_neg] using h
  · subst d
    simpa only [min_self] using equal_prime_power_norm_le p hp hg hchar hc k
  · have he : d + (c - d) = c := Nat.add_sub_of_le hdc.le
    have h := unequal_prime_power_norm_le p hp hg hd (show 1 ≤ c - d by omega) k
    simpa only [← pow_add, he, min_eq_right hdc.le] using h

theorem prime_power_partition_norm_le (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    {c d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d) (k : O) (save : Prop) [Decidable save]
    (hsave : save → c = d ∧ ¬ 6 ∣ c ∧ ¬ p ∣ k) :
    ‖actualCorrelation (p ^ c) (p ^ d) (supported_power p hp c) (supported_power p hp d)
      (p ^ min c d * k)‖ ≤
      (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (min c d - if save then 1 else 0) := by
  by_cases hs : save
  · obtain ⟨rfl, hc6, hk⟩ := hsave hs
    simp only [min_self, ite_eq_left hs]
    exact (equal_prime_power_unit_norm p hp hg hchar hc hc6 k hk).le
  · simpa only [ite_eq_right hs, Nat.sub_zero] using prime_power_norm_le_min p hp hg hchar hc hd k

section Product
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem supported_product (a : ι → O) (ha : ∀ i, Supported (Ideal.span {a i})) :
    Supported (Ideal.span {∏ i, a i}) := by
  have hs (S : Finset ι) : Supported (Ideal.span {∏ i ∈ S, a i}) := by
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, Ideal.span_singleton_one]
      rw [← Ideal.one_eq_top]
      change Supported (1 : Ideal O)
      refine ⟨one_ne_zero, ?_⟩
      intro P hP
      simp only [UniqueFactorizationMonoid.normalizedFactors_one,
        Multiset.notMem_zero] at hP
    | @insert i S hi ih =>
      rw [Finset.prod_insert hi]
      exact supported_mul_elements _ _ (ha i) ih
  exact hs Finset.univ

def partitionNormalizer (p : ι → O) (c d : ι → ℕ) (U : Finset ι) : ℝ :=
  ∏ i, (Ideal.absNorm (Ideal.span {p i}) : ℝ) ^ (min (c i) (d i) - if i ∈ U then 1 else 0)

def dividedFrequency (p : ι → O) (c d : ι → ℕ) (w : O) (i : ι) : O :=
  cofactor (fun j => p j ^ min (c j) (d j)) i * w

theorem commonFrequency_factor (p : ι → O) (c d : ι → ℕ) (w : O) (i : ι) :
    (∏ j, p j ^ min (c j) (d j)) * w = p i ^ min (c i) (d i) * dividedFrequency p c d w i := by
  rw [dividedFrequency, ← mul_assoc, factor_mul_cofactor (fun j => p j ^ min (c j) (d j)) i]

theorem actual_partition_norm_le (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, Supported (Ideal.span {p i}))
    (hg : ∀ i, goodLambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime p))
    (c d : ι → ℕ) (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i)
    (U : Finset ι) (w : O)
    (hU : ∀ i ∈ U, c i = d i ∧ ¬ 6 ∣ c i ∧ ¬ p i ∣ dividedFrequency p c d w i) :
    ‖actualCorrelation (∏ i, p i ^ c i) (∏ i, p i ^ d i)
      (supported_product _ (fun i => supported_power (p i) (hp i) (c i)))
      (supported_product _ (fun i => supported_power (p i) (hp i) (d i)))
      ((∏ i, p i ^ min (c i) (d i)) * w)‖ ≤ partitionNormalizer p c d U := by
  have hca : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i ^ c i})) := by
    intro i j hij
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    exact (hcop hij).pow
  have hcb : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i ^ d i})) := by
    intro i j hij
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    exact (hcop hij).pow
  have hcab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i ^ c i * p i ^ d i})) := by
    intro i j hij
    dsimp only [Function.onFun]
    rw [← pow_add, ← pow_add]
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    exact (hcop hij).pow
  rw [actualCorrelation_product_norm (fun i => p i ^ c i) (fun i => p i ^ d i)
    (fun i => supported_power (p i) (hp i) (c i))
    (fun i => supported_power (p i) (hp i) (d i))
    (supported_product _ (fun i => supported_power (p i) (hp i) (c i)))
    (supported_product _ (fun i => supported_power (p i) (hp i) (d i))) hca hcb hcab]
  unfold partitionNormalizer
  apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
  rw [commonFrequency_factor p c d w i]
  exact prime_power_partition_norm_le (p i) (hp i) (hg i) (hchar i) (hc i) (hd i)
    (dividedFrequency p c d w i) (i ∈ U) (hU i)

theorem normalized_partition_norm_le_one (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, Supported (Ideal.span {p i}))
    (hg : ∀ i, goodLambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime p))
    (c d : ι → ℕ) (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i)
    (U : Finset ι) (part : O → Prop) (w : O)
    (hpart : part w → ∀ i ∈ U, c i = d i ∧ ¬ 6 ∣ c i ∧ ¬ p i ∣ dividedFrequency p c d w i) :
    ‖if part w then
      actualCorrelation (∏ i, p i ^ c i) (∏ i, p i ^ d i)
        (supported_product _ (fun i => supported_power (p i) (hp i) (c i)))
        (supported_product _ (fun i => supported_power (p i) (hp i) (d i)))
        ((∏ i, p i ^ min (c i) (d i)) * w) / (partitionNormalizer p c d U : ℂ)
      else 0‖ ≤ 1 := by
  by_cases hw : part w
  · rw [ite_eq_left hw, norm_div, Complex.norm_real]
    have hN : 0 < partitionNormalizer p c d U := by
      unfold partitionNormalizer
      apply Finset.prod_pos
      intro i hi
      apply pow_pos
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1)
    rw [Real.norm_of_nonneg hN.le]
    exact (div_le_one hN).mpr (actual_partition_norm_le p hp hg hchar hcop c d hc hd U w (hpart hw))
  · simp only [ite_eq_right hw, norm_zero, zero_le_one]

end Product

end SevenEighths.CenteredMomentPartition

end

end OAI

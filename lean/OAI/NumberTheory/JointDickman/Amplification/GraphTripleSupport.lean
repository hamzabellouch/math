import OAI.NumberTheory.JointDickman.Counting.GraphCoefficientReindex

namespace OAI

/-! # Only supported coprime coefficient triples contribute to a lag -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem graphTripleWeight_nonzero_supported {B L T : ℕ} (hB : 0 < B) (hT : 0 < T)
    (τ C : ℝ) {i : GraphCoefficientTriple} {j : ℤ}
    (hi : i ∈ arithmeticGraphTriples B T) (hlag : graphTripleLag i = j)
    {n : ℕ} (hw : graphTripleWeight B L τ C T i n ≠ 0) :
    i ∈ supportedGraphTriples B T j := by
  classical
  let a := ∏ p ∈ i.2.1, p
  let b := ∏ p ∈ i.2.2, p
  let c := ∏ p ∈ i.1, p
  have hzero (hu : amplificationOuterWeight B c = 0) : False := by
    apply hw
    simp only [graphTripleWeight, arithmeticGraphPairWeight]
    change (amplificationOuterWeight B c * _ * _) * _ * _ = 0
    rw [hu, zero_mul, zero_mul, zero_mul, zero_mul]
  have hza (hu : amplificationInnerWeight T a c = 0) : False := by
    apply hw
    simp only [graphTripleWeight, arithmeticGraphPairWeight]
    change _ * (_ * _ * amplificationInnerWeight T a c) * _ = 0
    rw [hu, mul_zero, mul_zero, zero_mul]
  have hzb (hu : amplificationInnerWeight T b c = 0) : False := by
    apply hw
    simp only [graphTripleWeight, arithmeticGraphPairWeight]
    change _ * (_ * _ * amplificationInnerWeight T b c) = 0
    rw [hu, mul_zero, mul_zero]
  have hpa : (a,c) ∈ amplificationCoefficientPairs B T := by
    by_contra hn
    have hs := amplificationSmoothWeight_support hB hT a c hn
    exact (mul_ne_zero hzero hza) hs
  have hpb : (b,c) ∈ amplificationCoefficientPairs B T := by
    by_contra hn
    have hs := amplificationSmoothWeight_support hB hT b c hn
    exact (mul_ne_zero hzero hzb) hs
  exact mem_filter.mpr ⟨hi,hlag,hpa,hpb⟩

theorem graphTriple_edge_coprime {B T N : ℕ} {i : GraphCoefficientTriple}
    (hi : i ∈ arithmeticGraphTriples B T) {n : ℕ} (hn : n ∈ graphTripleEdges N i) :
    (∏ p ∈ i.2.1, p).Coprime (∏ p ∈ i.1, p) := by
  classical
  have hs := graphTriple_subsets hi
  have ha : 0 < ∏ p ∈ i.2.1, p :=
    prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hs.2.1 hp)).pos)
  have hc : 0 < ∏ p ∈ i.1, p :=
    prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hs.1 hp)).pos)
  have hg := (mem_filter.mp hi).2
  have hm := (divisorEdge_inverse_mem ha hc hg.2.2.2.1 hg.2.2.2.2 hn).1
  exact (coprime_of_divisor_linear_succ (mem_filter.mp hm).2.2.2.1).1

open Classical in
noncomputable def coprimeGraphTriples (B T : ℕ) (j : ℤ) : Finset GraphCoefficientTriple :=
  (supportedGraphTriples B T j).filter fun i =>
    (∏ p ∈ i.2.1, p).Coprime (∏ p ∈ i.1, p)

theorem graphTriple_size_bound :
    ∀ᶠ B : ℕ in atTop, ∀ T : ℕ, 0 < T →
      (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → ∀ j : ℤ,
      ∀ i ∈ supportedGraphTriples B T j,
        ((∏ p ∈ i.2.1, p : ℕ) : ℝ)*(∏ p ∈ i.2.2, p : ℕ)*(∏ p ∈ i.1, p : ℕ) ≤
          Real.exp (10*(B : ℝ)) := by
  filter_upwards [amplificationCoefficientPairs_size] with B hB
  intro T hT hTs j i hi
  have h := (mem_filter.mp hi).2
  have ha := hB T _ _ hT hTs h.2.1
  have hb := hB T _ _ hT hTs h.2.2
  calc
    _ ≤ Real.exp ((16/5 : ℝ)*B)*Real.exp ((16/5 : ℝ)*B)*Real.exp ((16/5 : ℝ)*B) := by
      gcongr
      exacts [ha.1, hb.1, ha.2]
    _ = Real.exp ((48/5 : ℝ)*B) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (10*(B : ℝ)) := Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) B])

end JointDickman

end OAI

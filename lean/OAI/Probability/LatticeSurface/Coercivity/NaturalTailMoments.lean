import Mathlib

namespace OAI

open MeasureTheory

open scoped NNReal ENNReal

namespace SparseHoles

lemma polynomial_geometric_summable (q : ℕ) :
    Summable (fun n : ℕ => (n+1:ℝ)^q*(1/4:ℝ)^n) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one q (r := (1/4:ℝ)) (by norm_num)
  have hh : Summable (fun n : ℕ => (n+1:ℝ)^q*(1/4:ℝ)^(n+1)) := by
    simpa only [Nat.cast_add,Nat.cast_one] using (summable_nat_add_iff 1).2 h
  have he : (fun n : ℕ => 4*((n+1:ℝ)^q*(1/4:ℝ)^(n+1))) =
      (fun n : ℕ => (n+1:ℝ)^q*(1/4:ℝ)^n) := by
    funext n
    rw [pow_succ]
    ring
  rw [← he]
  exact hh.mul_left 4

lemma polynomial_geometric_finite (q : ℕ) :
    (∑' n : ℕ, ((n+1:ℕ):ENNReal)^q*(1/4:ENNReal)^n) ≠ ⊤ := by
  have hs := polynomial_geometric_summable q
  have hn : ∀ n : ℕ, 0 ≤ (n+1:ℝ)^q*(1/4:ℝ)^n := by intro n;positivity
  have he (n : ℕ) : ((n+1:ℕ):ENNReal)^q*(1/4:ENNReal)^n =
      ENNReal.ofReal ((n+1:ℝ)^q*(1/4:ℝ)^n) := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofReal (hn n),ENNReal.toReal_add]
  simp_rw [he]
  exact hs.tsum_ofReal_ne_top

lemma natural_tail_moments (q : ℕ) : ∃ C : ℝ≥0, ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d : Ω → ℕ), Measurable d →
    (∀ r : ℕ, μ {ω | 2*r+2 ≤ d ω} ≤ 100*(1/4:ENNReal)^r) →
    (∫⁻ ω, ((d ω+1:ℕ):ENNReal)^q ∂μ) ≤ C := by
  let C : ENNReal := 400*3^q * ∑' n : ℕ,((n+1:ℕ):ENNReal)^q*(1/4:ENNReal)^n
  have hC : C ≠ ⊤ := by
    have ht := polynomial_geometric_finite q
    dsimp [C]
    finiteness
  refine ⟨C.toNNReal,?_⟩
  intro Ω _ μ _ d hd ht
  rw [ENNReal.coe_toNNReal hC]
  let D : Ω → ℕ := fun ω => d ω/2
  have hD : Measurable D := (measurable_of_countable (fun n : ℕ => n/2)).comp hd
  have hdist (n : ℕ) : μ {ω | D ω=n} ≤ 400*(1/4:ENNReal)^n := by
    cases n with
    | zero => exact prob_le_one.trans (by norm_num)
    | succ m =>
      have hs : {ω | D ω=m+1} ⊆ {ω | 2*m+2≤d ω} := by intro ω hω;change d ω/2=m+1 at hω;change 2*m+2≤d ω;omega
      refine ((measure_mono hs).trans (ht m)).trans_eq ?_
      rw [pow_succ]
      have he : (400:ENNReal)*(1/4)=100 := by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        norm_num
      rw [← he];ring
  have hpoint (ω : Ω) : ((d ω+1:ℕ):ENNReal)^q ≤ 3^q*((D ω+1:ℕ):ENNReal)^q := by
    rw [← mul_pow]
    apply pow_le_pow_left'
    have hn : d ω+1 ≤ 3*(D ω+1) := by dsimp [D];omega
    exact_mod_cast hn
  calc
    _ ≤ ∫⁻ ω,3^q*((D ω+1:ℕ):ENNReal)^q ∂μ := lintegral_mono hpoint
    _ = ∫⁻ n : ℕ,3^q*((n+1:ℕ):ENNReal)^q ∂(μ.map D) := (lintegral_map (μ := μ) (f := fun n : ℕ => (3:ENNReal)^q*((n+1:ℕ):ENNReal)^q) (measurable_of_countable _) hD).symm
    _ = ∑' n : ℕ,(3^q*((n+1:ℕ):ENNReal)^q)*(μ.map D) {n} := lintegral_countable' _
    _ = ∑' n : ℕ,(3^q*((n+1:ℕ):ENNReal)^q)*μ {ω | D ω=n} := by
      apply tsum_congr
      intro n
      rw [Measure.map_apply hD (measurableSet_singleton n)]
      rfl
    _ ≤ ∑' n : ℕ,(3^q*((n+1:ℕ):ENNReal)^q)*(400*(1/4:ENNReal)^n) := by
      apply ENNReal.tsum_le_tsum
      intro n
      gcongr
      exact hdist n
    _ = C := by
      dsimp only [C]
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro n
      ring

end SparseHoles

end OAI

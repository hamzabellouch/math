import OAI.Combinatorics.GraphThreshold.BernoulliCoupling
import OAI.Combinatorics.GraphThreshold.AdaptiveTrials
import OAI.Combinatorics.GraphThreshold.GraphProbability

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace LeanBlast.SecondKahnKalai

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem bernoulli_union_product (p q : ℝ) (f : X → Bool → ℝ) :
    bernoulliExpectation p (fun U => bernoulliExpectation q
      (fun V => ∏ x, f x (decide (x ∈ U ∪ V)))) =
      ∏ x, ((p + q - p * q) * f x true + (1 - (p + q - p * q)) * f x false) := by
  have hi (U : Finset X) :
      bernoulliExpectation q (fun V => ∏ x, f x (decide (x ∈ U ∪ V))) =
        ∏ x, (q * f x true + (1 - q) * f x (decide (x ∈ U))) := by
    have hfun : (fun V : Finset X => ∏ x, f x (decide (x ∈ U ∪ V))) =
        (fun V => ∏ x, f x (decide (x ∈ U) || decide (x ∈ V))) := by
      funext V
      apply Finset.prod_congr rfl
      intro x _
      by_cases hu : x ∈ U <;> by_cases hv : x ∈ V <;> simp [Finset.mem_union, hu, hv]
    rw [hfun]
    simpa using
      bernoulliExpectation_product q (fun x b => f x (decide (x ∈ U) || b))
  calc
    _ = bernoulliExpectation p (fun U =>
        ∏ x, (q * f x true + (1 - q) * f x (decide (x ∈ U)))) :=
      bernoulliExpectation_congr p hi
    _ = _ := by
      rw [bernoulliExpectation_product p (fun x b => q * f x true + (1 - q) * f x b)]
      apply Finset.prod_congr rfl
      intro x _
      ring

theorem bernoulli_union_mass (p q : ℝ) (Y : Finset X) :
    bernoulliExpectation p (fun U => bernoulliExpectation q
      (fun V => if U ∪ V = Y then 1 else 0)) = bernoulliWeight (p + q - p * q) Y := by
  let f : X → Bool → ℝ := fun x b => if (b = true ↔ x ∈ Y) then 1 else 0
  have hi (U V : Finset X) :
      (if U ∪ V = Y then (1 : ℝ) else 0) = ∏ x, f x (decide (x ∈ U ∪ V)) := by
    simpa [f] using finset_eq_indicator_product (U ∪ V) Y
  calc
    _ = bernoulliExpectation p (fun U => bernoulliExpectation q
        (fun V => ∏ x, f x (decide (x ∈ U ∪ V)))) :=
      bernoulliExpectation_congr p fun U => bernoulliExpectation_congr q (hi U)
    _ = _ := by
      rw [bernoulli_union_product]
      apply Finset.prod_congr rfl
      intro x _
      by_cases hy : x ∈ Y <;> simp [f, hy]

/-- The union of two independent Bernoulli subsets has the stated Bernoulli law. -/
theorem bernoulliExpectation_union (p q : ℝ) (F : Finset X → ℝ) :
    bernoulliExpectation p (fun U => bernoulliExpectation q (fun V => F (U ∪ V))) =
      bernoulliExpectation (p + q - p * q) F := by
  calc
    _ = bernoulliExpectation p (fun U => ∑ Y : Finset X,
        bernoulliExpectation q (fun V => if U ∪ V = Y then 1 else 0) * F Y) :=
      bernoulliExpectation_congr p fun U =>
        bernoulliExpectation_pushforward q (fun V => U ∪ V) F
    _ = ∑ Y : Finset X, bernoulliExpectation p (fun U =>
        bernoulliExpectation q (fun V => if U ∪ V = Y then 1 else 0) * F Y) :=
      bernoulliExpectation_sum p _
    _ = ∑ Y : Finset X, bernoulliWeight (p + q - p * q) Y * F Y := by
      apply Finset.sum_congr rfl
      intro Y _
      have hfactor : bernoulliExpectation p (fun U =>
          bernoulliExpectation q (fun V => if U ∪ V = Y then 1 else 0) * F Y) =
          bernoulliExpectation p (fun U =>
            bernoulliExpectation q (fun V => if U ∪ V = Y then 1 else 0)) * F Y := by
        simp only [bernoulliExpectation, Finset.sum_mul, mul_assoc]
      rw [hfactor, bernoulli_union_mass]
    _ = _ := rfl

omit [Fintype X] in
theorem biUnion_fin_cons {n : ℕ} (A : Finset X) (draws : Fin n → Finset X) :
    Finset.univ.biUnion (Fin.cases A draws) = A ∪ Finset.univ.biUnion draws := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    revert hi
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hi
      exact Or.inl hi
    · intro hi
      exact Or.inr ⟨j, hi⟩
  · rintro (hx | ⟨j, hj⟩)
    · exact ⟨0, hx⟩
    · exact ⟨j.succ, hj⟩

/-- Exact law of the union of a finite history of independent draws. -/
theorem iid_bernoulli_union_expectation (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (n : ℕ) (F : Finset X → ℝ) :
    ((bernoulliLaw p hp0 hp1).iid n).expectation (fun draws => F (Finset.univ.biUnion draws)) =
      bernoulliExpectation (1 - (1 - p) ^ n) F := by
  induction n generalizing F with
  | zero => simp
  | succ n ih =>
      rw [FiniteLaw.iid_expectation_succ]
      simp_rw [biUnion_fin_cons]
      have hi (A : Finset X) := ih (fun W => F (A ∪ W))
      have hrewrite : (fun A => ((bernoulliLaw p hp0 hp1).iid n).expectation
          (fun draws => F (A ∪ Finset.univ.biUnion draws))) =
          (fun A => bernoulliExpectation (1 - (1 - p) ^ n) (fun W => F (A ∪ W))) := by
        funext A
        exact hi A
      rw [hrewrite, bernoulliLaw_expectation, bernoulliExpectation_union]
      congr 1
      rw [pow_succ]
      ring

theorem iid_bernoulli_union_probability (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (n : ℕ) (P : Finset X → Prop) :
    ((bernoulliLaw p hp0 hp1).iid n).prob (fun draws => P (Finset.univ.biUnion draws)) =
      bernoulliProbability (1 - (1 - p) ^ n) P := by
  rw [FiniteLaw.prob_eq_expectation, bernoulliProbability_eq_expectation]
  exact iid_bernoulli_union_expectation p hp0 hp1 n (fun W => if P W then 1 else 0)

theorem bernoulli_union_parameter_mem {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    0 ≤ 1 - (1 - p) ^ n ∧ 1 - (1 - p) ^ n ≤ 1 := by
  have hpow0 : 0 ≤ (1 - p) ^ n := pow_nonneg (sub_nonneg.mpr hp1) _
  have hpow1 : (1 - p) ^ n ≤ 1 := pow_le_one₀ (sub_nonneg.mpr hp1) (by linarith)
  constructor <;> linarith

theorem bernoulli_union_parameter_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    1 - (1 - p) ^ n ≤ (n : ℝ) * p := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpow1 : (1 - p) ^ n ≤ 1 := pow_le_one₀ (sub_nonneg.mpr hp1) (by linarith)
      have hmul := mul_le_mul_of_nonneg_left hpow1 hp0
      rw [pow_succ, Nat.cast_succ]
      nlinarith

end LeanBlast.SecondKahnKalai

end

end OAI

import OAI.NumberTheory.TwoPoint.Bounds.PrimeWordEncoding
import OAI.NumberTheory.TwoPoint.Bounds.BadCatalogCost
import OAI.NumberTheory.TwoPoint.Bounds.CrudeTraceWeights

namespace OAI

/-! Complete reciprocal counting for actual numerical tuple and padding words. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma split_assignment_reciprocal_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (P Q : Finset ℕ) :
    (∑ a : S → P, ∑ b : {i // i ∉ S} → Q,
      ∏ i, ((joinCoordinates S (fun z => (a z).val) (fun z => (b z).val) i : ℕ) : ℝ)⁻¹) =
      primeHarmonicMass P ^ Fintype.card S *
        primeHarmonicMass Q ^ Fintype.card {i // i ∉ S} := by
  simp only [reciprocal_product_join]
  calc
    _ = (∑ a : S → P, ∏ i, ((a i).val : ℝ)⁻¹) *
        (∑ b : {i // i ∉ S} → Q, ∏ i, ((b i).val : ℝ)⁻¹) := by
      exact (sum_mul_sum _ _ _ _).symm
    _ = _ := by rw [sum_reciprocal_assignments, sum_reciprocal_assignments]

lemma primeWordEncoding_weight_sum (R T : ℕ) (P Q : Finset ℕ) :
    (∑ e : PrimeWordEncoding R T P Q, e.weight) =
      ∑ n : Fin (T + 1), ∑ c : CrudeWordCode R n.val R,
        primeHarmonicMass P ^ Fintype.card c.tupleClasses *
          primeHarmonicMass Q ^ Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses} := by
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro n _
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro c _
  rw [Fintype.sum_prod_type]
  change (∑ a : c.tupleClasses → P, ∑ b : {z : c.usedClasses // z ∉ c.tupleClasses} → Q,
    ∏ z : c.usedClasses,
      ((joinCoordinates c.tupleClasses (fun z => (a z).val) (fun z => (b z).val) z : ℕ) : ℝ)⁻¹) = _
  exact split_assignment_reciprocal_sum c.tupleClasses P Q

/-- Both prime supplies may be enlarged, but distinct abstract classes
continue to pay distinct reciprocal factors, including after collisions. -/
theorem primeWordEncoding_weight_le (R T : ℕ) (P Q : Finset ℕ) (U : ℝ)
    (hU : 1 ≤ U) (hP : primeHarmonicMass P ≤ U) (hQ : primeHarmonicMass Q ≤ U) :
    (∑ e : PrimeWordEncoding R T P Q, e.weight) ≤
      (∑ n : Fin (T + 1), (Fintype.card (CrudeWordCode R n.val R) : ℝ)) * U ^ T := by
  rw [primeWordEncoding_weight_sum, sum_mul]
  apply sum_le_sum
  intro n _
  calc
    _ ≤ ∑ _c : CrudeWordCode R n.val R, U ^ T := by
      apply sum_le_sum
      intro c _
      exact (c.class_mass_le (by unfold primeHarmonicMass; positivity)
        (by unfold primeHarmonicMass; positivity) hP hQ hU).trans
        (pow_le_pow_right₀ hU (by omega))
    _ = _ := by simp

/-- A bound for the original numerical words, before any equality-pattern
or prime assignment is enlarged. This is the crude catalog estimate used
by the many-unlit and witness cases. -/
theorem numerical_word_reciprocal_sum_le (R T : ℕ) (P Q : Finset ℕ)
    (F : Finset (Fin R → SignedStep)) (weight : List SignedStep → ℝ) (W U : ℝ)
    (hW : 0 ≤ W) (hU : 1 ≤ U)
    (hP : primeHarmonicMass P ≤ U) (hQ : primeHarmonicMass Q ≤ U)
    (hweight : ∀ w ∈ F, weight (List.ofFn w) ≤ W)
    (hT : ∀ w ∈ F, Fintype.card (ActualPrimeSlot w) ≤ T)
    (ht : ∀ w ∈ F, ∀ i, Squarefree (w i).tuple)
    (hq : ∀ w ∈ F, ∀ i, Squarefree (w i).padding)
    (htP : ∀ w ∈ F, ∀ i, (w i).tuple.primeFactors ⊆ P)
    (hqQ : ∀ w ∈ F, ∀ i, (w i).padding.primeFactors ⊆ Q)
    (hd : ∀ w ∈ F, ∀ i j, Disjoint (w i).tuple.primeFactors (w j).padding.primeFactors) :
    (∑ w ∈ F, weight (List.ofFn w) *
      ∏ p ∈ wordDivisorPrimeSupport (List.ofFn w), (p : ℝ)⁻¹) ≤
      W * (∑ n : Fin (T + 1), (Fintype.card (CrudeWordCode R n.val R) : ℝ)) * U ^ T := by
  let mass (w : List SignedStep) := ∏ p ∈ wordDivisorPrimeSupport w, (p : ℝ)⁻¹
  have hcover : ∀ w ∈ F.image List.ofFn, ∃ e : PrimeWordEncoding R T P Q,
      e.decode = w ∧ weight w * mass w ≤ W * e.weight := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hv
    obtain ⟨e, he, _, _, _, hmass⟩ := PrimeWordEncoding.covers w (hT w hw)
      (ht w hw) (hq w hw) (htP w hw) (hqQ w hw) (hd w hw)
    refine ⟨e, he, ?_⟩
    rw [hmass]
    exact mul_le_mul_of_nonneg_right (hweight w hw) (by dsimp [mass]; positivity)
  calc
    _ = ∑ w ∈ F.image List.ofFn, weight w * mass w := by
      rw [sum_image (fun _ _ _ _ he => List.ofFn_injective he)]
    _ ≤ ∑ e : PrimeWordEncoding R T P Q, W * e.weight :=
      finite_decoding_weight_bound (F.image List.ofFn) PrimeWordEncoding.decode
        (fun w => weight w * mass w) (fun e => W * e.weight)
        (fun e => mul_nonneg hW e.weight_nonneg) hcover
    _ = W * ∑ e : PrimeWordEncoding R T P Q, e.weight := (mul_sum _ _ _).symm
    _ ≤ W * ((∑ n : Fin (T + 1), (Fintype.card (CrudeWordCode R n.val R) : ℝ)) * U ^ T) :=
      mul_le_mul_of_nonneg_left (primeWordEncoding_weight_le R T P Q U hU hP hQ) hW
    _ = _ := by ring

/-- Explicit exponential form of the complete code and reciprocal cost. -/
theorem crude_numerical_cost_exp_bound (R T b : ℕ)
    (L C U : ℝ) (hR : 1 ≤ R) (hL : 0 < L) (hlog : 1 ≤ Real.log L)
    (hslots : (T : ℝ) ≤ C * R * Real.log L)
    (hT : (T : ℝ) + 1 ≤ L ^ (2 : ℕ)) (hRpoly : (R : ℝ) + 1 ≤ L ^ (2 : ℕ))
    (hU : 1 ≤ U) (hUP : U ≤ L ^ b) :
    (∑ n : Fin (T + 1), (Fintype.card (CrudeWordCode R n.val R) : ℝ)) * U ^ T ≤
      Real.exp ((3 + 5 * C + b * C) * R * (Real.log L) ^ 2) := by
  have hcode (n : Fin (T + 1)) :
      (Fintype.card (CrudeWordCode R n.val R) : ℝ) ≤
        Real.exp ((1 + 5 * C) * R * (Real.log L) ^ 2) := by
    have hn : n.val ≤ T := by omega
    have hnr : (n.val : ℝ) ≤ T := by exact_mod_cast hn
    exact short_crudeWordCode_bound R n.val R L C hlog le_rfl
      (hnr.trans hslots) (by linarith) hRpoly
  have hcount : (∑ n : Fin (T + 1), (Fintype.card (CrudeWordCode R n.val R) : ℝ)) ≤
      Real.exp ((3 + 5 * C) * R * (Real.log L) ^ 2) := by
    calc
      _ ≤ ((T : ℝ) + 1) * Real.exp ((1 + 5 * C) * R * (Real.log L) ^ 2) := by
        simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using
          (sum_le_sum (s := (univ : Finset (Fin (T + 1)))) (fun n _ => hcode n))
      _ ≤ Real.exp (2 * R * (Real.log L) ^ 2) *
          Real.exp ((1 + 5 * C) * R * (Real.log L) ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact hT.trans (by
          simpa using short_polynomial_exp_bound R 2 L hR hL hlog)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hmass : U ^ T ≤ Real.exp ((b : ℝ) * C * R * (Real.log L) ^ 2) := by
    calc
      _ ≤ (L ^ b) ^ T := pow_le_pow_left₀ (by linarith) hUP _
      _ = Real.exp ((T : ℝ) * b * Real.log L) := by
        rw [← pow_mul, ← Real.exp_log hL, ← Real.exp_nat_mul, Real.log_exp]
        congr 1
        push_cast
        ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have ht := mul_le_mul_of_nonneg_right hslots
          (show 0 ≤ (b : ℝ) * Real.log L by positivity)
        nlinarith
  calc
    _ ≤ Real.exp ((3 + 5 * C) * R * (Real.log L) ^ 2) *
        Real.exp ((b : ℝ) * C * R * (Real.log L) ^ 2) :=
      mul_le_mul hcount hmass (by positivity) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- The numerical assignment sum inherits the explicit code-cost bound. -/
theorem primeWordEncoding_weight_exp_bound (R T b : ℕ) (P Q : Finset ℕ)
    (L C U : ℝ) (hR : 1 ≤ R) (hL : 0 < L) (hlog : 1 ≤ Real.log L)
    (hslots : (T : ℝ) ≤ C * R * Real.log L)
    (hT : (T : ℝ) + 1 ≤ L ^ (2 : ℕ)) (hRpoly : (R : ℝ) + 1 ≤ L ^ (2 : ℕ))
    (hU : 1 ≤ U) (hUP : U ≤ L ^ b)
    (hP : primeHarmonicMass P ≤ U) (hQ : primeHarmonicMass Q ≤ U) :
    (∑ e : PrimeWordEncoding R T P Q, e.weight) ≤
      Real.exp ((3 + 5 * C + b * C) * R * (Real.log L) ^ 2) :=
  (primeWordEncoding_weight_le R T P Q U hU hP hQ).trans
    (crude_numerical_cost_exp_bound R T b L C U hR hL hlog hslots hT hRpoly hU hUP)

end TwoPointCorrelations

end OAI

import OAI.GroupTheory.PolycyclicRecognition.Algebra.DynkinInput

namespace OAI

/-!
# Finite BCH products controlled by the sum of input sizes

The coefficient bound in the existing finite Dynkin input also controls
products by the sum of the logarithmic input norms. In particular the
bound tends to zero with that sum, independently of the number of factors.
This is the estimate needed for contracting quotient trajectories in
exponential coordinates; no Riemannian metric comparison is assumed.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule
open scoped BigOperators Manifold

variable {L J : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype J]

/-- Keep the individual letter sizes when estimating a right-nested word. -/
theorem norm_rightNestedWord_le_product (b : Basis J ℝ L)
    {I : Type*} (X : I → L) {C : ℝ} (hC : 0 ≤ C)
    (hbracket : ∀ i j k, |b.repr ⁅b i, b j⁆ k| ≤ C)
    (d : ℕ) (w : Fin (d + 1) → I) :
    ‖b.equivFun (evalBracketWord X (rightNestedWord d w))‖ ≤
      ((Fintype.card J : ℝ) ^ 2 * C) ^ d * ∏ i, ‖b.equivFun (X (w i))‖ := by
  let K := (Fintype.card J : ℝ) ^ 2 * C
  have hK : 0 ≤ K := by positivity
  induction d with
  | zero => simp [rightNestedWord]
  | succ d ih =>
    calc
      _ ≤ K * ‖b.equivFun (X (w 0))‖ *
          ‖b.equivFun (evalBracketWord X (rightNestedWord d (fun i => w i.succ)))‖ :=
        norm_basis_bracket_le b hC hbracket _ _
      _ ≤ K * ‖b.equivFun (X (w 0))‖ *
          (K ^ d * ∏ i : Fin (d + 1), ‖b.equivFun (X (w i.succ))‖) := by
        exact mul_le_mul_of_nonneg_left (ih (fun i => w i.succ)) (by positivity)
      _ = _ := by
        conv_rhs => rw [Fin.prod_univ_succ]
        dsimp [K]
        rw [pow_succ]
        ring

/-- The finite Dynkin polynomial is bounded by a polynomial in the sum
of input norms, with zero constant term. -/
theorem norm_finiteDynkinPolynomial_le_sum (b : Basis J ℝ L) {c n : ℕ}
    (coeff : DynkinCoefficients c n) (hcoeff : ∀ d w, |coeff d w| ≤ (2 : ℝ) ^ c)
    (X : Fin n → L) {C : ℝ} (hC : 0 ≤ C)
    (hbracket : ∀ i j k, |b.repr ⁅b i, b j⁆ k| ≤ C) :
    ‖b.equivFun (finiteDynkinPolynomial coeff X)‖ ≤
      (c : ℝ) * 2 ^ c * (1 + (Fintype.card J : ℝ) ^ 2 * C) ^ c *
        (∑ i, ‖b.equivFun (X i)‖) * (1 + ∑ i, ‖b.equivFun (X i)‖) ^ c := by
  let K := (Fintype.card J : ℝ) ^ 2 * C
  let S := ∑ i, ‖b.equivFun (X i)‖
  have hK : 0 ≤ K := by positivity
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hdegree (d : Fin c) :
      ‖b.equivFun (∑ w : Fin (d.val + 1) → Fin n,
        coeff d w • evalBracketWord X (rightNestedWord d.val w))‖ ≤
      2 ^ c * (1 + K) ^ c * S * (1 + S) ^ c := by
    rw [map_sum]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ w : Fin (d.val + 1) → Fin n,
          2 ^ c * K ^ d.val * ∏ i, ‖b.equivFun (X (w i))‖ := by
        apply Finset.sum_le_sum
        intro w _
        rw [map_smul, norm_smul, Real.norm_eq_abs]
        have hb := norm_rightNestedWord_le_product b X hC hbracket d.val w
        have ht := mul_le_mul (hcoeff d w) hb (norm_nonneg _) (by positivity : 0 ≤ (2 : ℝ) ^ c)
        simpa only [K, mul_assoc] using ht
      _ = 2 ^ c * K ^ d.val * S ^ (d.val + 1) := by
        rw [← Finset.mul_sum,
          ← Fintype.sum_pow (fun i : Fin n => ‖b.equivFun (X i)‖) (d.val + 1)]
      _ ≤ 2 ^ c * (1 + K) ^ c * (S * (1 + S) ^ c) := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact (pow_le_pow_left₀ hK (by linarith) d.val).trans
            (pow_le_pow_right₀ (by linarith) d.isLt.le)
        · rw [pow_succ, mul_comm]
          apply mul_le_mul_of_nonneg_left _ hS
          exact (pow_le_pow_left₀ hS (by linarith) d.val).trans
            (pow_le_pow_right₀ (by linarith) d.isLt.le)
        · positivity
        · positivity
      _ = _ := by ring
  unfold finiteDynkinPolynomial
  rw [map_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _d : Fin c, 2 ^ c * (1 + K) ^ c * S * (1 + S) ^ c :=
      Finset.sum_le_sum (fun d _ => hdegree d)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp [K, S]
      ring

section ExponentialProducts

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

/-- Actual finite products of exponentials have a logarithm controlled by
the total input size, independently of the number of factors. -/
theorem exists_product_log_with_sum_bound
    (dynkin : NilpotentDynkinExpansionInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    {c n : ℕ} (hc : lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
      (GroupLieAlgebra (𝓘(ℝ, E)) G) c = ⊥)
    (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    {C : ℝ} (hC : 0 ≤ C)
    (hbracket : ∀ i j k, |b.repr ⁅b i, b j⁆ k| ≤ C)
    (X : Fin n → GroupLieAlgebra (𝓘(ℝ, E)) G) :
    ∃ z, (List.ofFn (fun i => Exp (X i))).prod = Exp z ∧
      ‖b.equivFun z‖ ≤
        (c : ℝ) * 2 ^ c * (1 + (Fintype.card J : ℝ) ^ 2 * C) ^ c *
          (∑ i, ‖b.equivFun (X i)‖) * (1 + ∑ i, ‖b.equivFun (X i)‖) ^ c := by
  obtain ⟨coeff, hcoeff, hprod⟩ := dynkin Exp hExp c hc n
  exact ⟨finiteDynkinPolynomial coeff X, hprod X,
    norm_finiteDynkinPolynomial_le_sum b coeff hcoeff X hC hbracket⟩

end ExponentialProducts
end PolycyclicRecognition

end

end OAI

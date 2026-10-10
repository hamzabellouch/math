import OAI.NumberTheory.JointDickman.Counting.LagSquareSum
import OAI.NumberTheory.JointDickman.Counting.SamplingMoments
import OAI.NumberTheory.JointDickman.Amplification.ConditionedRootTests

namespace OAI

/-! # Row moments of the deterministic singular-factor envelope -/
namespace JointDickman
open Finset Classical PublishedInputs

noncomputable def lagEnvelope {M : ℕ} (T : ℕ) (D : ℝ) (i k : Fin M) : ℝ :=
  if i ≠ k ∧ Nat.dist i.val k.val < T then D/(T : ℝ)*singularFactor 24 (Nat.dist i.val k.val) else 0

theorem lagEnvelope_nonneg {M : ℕ} (T : ℕ) {D : ℝ} (hD : 0 ≤ D) (i k : Fin M) :
    0 ≤ lagEnvelope T D i k := by
  unfold lagEnvelope
  split_ifs
  · exact mul_nonneg (div_nonneg hD (Nat.cast_nonneg _))
      (zero_le_one.trans (singularFactor_one_le (by norm_num) _))
  · exact le_rfl

theorem lagEnvelope_row_sum {M T : ℕ} (hT : 0 < T) {D : ℝ} (hD : 0 ≤ D) (i : Fin M) :
    (∑ k, lagEnvelope T D i k) ≤ 2*D*Real.exp 24 := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have he (k : Fin M) : lagEnvelope T D i k = D/(T : ℝ)*
      (if i ≠ k ∧ Nat.dist i.val k.val < T then singularFactor 24 (Nat.dist i.val k.val) else 0) := by
    unfold lagEnvelope
    split_ifs <;> simp only [mul_zero]
  simp_rw [he]
  rw [← mul_sum]
  exact (mul_le_mul_of_nonneg_left (distance_lag_singular_sum i T) (div_nonneg hD hTr.le)).trans_eq
    (by field_simp)

theorem lagEnvelope_row_square_sum {M T : ℕ} (hT : 0 < T) {D : ℝ} (i : Fin M) :
    (∑ k, (lagEnvelope T D i k)^2) ≤ 2*D^2*Real.exp 1200/(T : ℝ) := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have he (k : Fin M) : (lagEnvelope T D i k)^2 = (D/(T : ℝ))^2*
      (if i ≠ k ∧ Nat.dist i.val k.val < T then (singularFactor 24 (Nat.dist i.val k.val))^2 else 0) := by
    unfold lagEnvelope
    split_ifs <;> simp only [mul_pow,mul_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  simp_rw [he]
  rw [← mul_sum]
  exact (mul_le_mul_of_nonneg_left (distance_lag_square_sum i T) (sq_nonneg _)).trans_eq
    (by field_simp)

theorem lagEnvelope_row_mean {M T : ℕ} {A : Type*} [Fintype A]
    (hT : 0 < T) {D : ℝ} (hD : 0 ≤ D) (p : Fin M → A → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (K : Fin M → Fin M → A → A → ℝ)
    (hK : ∀ i k a b, |K i k a b| ≤ lagEnvelope T D i k) (i : Fin M) (a : A) :
    |siteRowMean p K i a| ≤ 2*D*Real.exp 24 := by
  have he (k : Fin M) :
      |finiteExpectation (p k) (fun b => K i k a b)| ≤ lagEnvelope T D i k :=
    (finiteExpectation_abs_bound (p k) _ (hp k)).trans
      ((finiteExpectation_mono (p k) (hp k) (hK i k a)).trans_eq
        (finiteExpectation_const (p k) (hpone k) _))
  calc
    _ ≤ ∑ k : {k : Fin M // k ≠ i}, |finiteExpectation (p k) (fun b => K i k a b)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : {k : Fin M // k ≠ i}, lagEnvelope T D i k := sum_le_sum (fun k _ => he k)
    _ = ∑ k : Fin M, lagEnvelope T D i k := by
      rw [Fintype.sum_eq_add_sum_subtype_ne _ i]
      simp only [lagEnvelope,ne_eq,not_true_eq_false,false_and,ite_false,zero_add]
    _ ≤ _ := lagEnvelope_row_sum hT hD i

theorem lagEnvelope_row_square_mass {M T : ℕ} {A : Type*} [Fintype A]
    (hT : 0 < T) {D : ℝ} (hD : 0 ≤ D) (p : Fin M → A → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (K : Fin M → Fin M → A → A → ℝ)
    (hK : ∀ i k a b, |K i k a b| ≤ lagEnvelope T D i k) (i : Fin M) :
    siteRowSquareMass p K i ≤ 2*D^2*Real.exp 1200/(T : ℝ) := by
  have he (k : Fin M) (a : A) :
      finiteExpectation (p k) (fun b => (K i k a b)^2) ≤ (lagEnvelope T D i k)^2 := by
    apply (finiteExpectation_mono (p k) (hp k) (fun b => ?_)).trans_eq
      (finiteExpectation_const (p k) (hpone k) _)
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (lagEnvelope_nonneg T hD i k)).mpr (hK i k a b)
  have hr (a : A) : (∑ k : {k : Fin M // k ≠ i},
      finiteExpectation (p k) (fun b => (K i k a b)^2)) ≤ 2*D^2*Real.exp 1200/(T : ℝ) := by
    calc
      _ ≤ ∑ k : {k : Fin M // k ≠ i}, (lagEnvelope T D i k)^2 := sum_le_sum (fun k _ => he k a)
      _ = ∑ k : Fin M, (lagEnvelope T D i k)^2 := by
        rw [Fintype.sum_eq_add_sum_subtype_ne _ i]
        simp only [lagEnvelope,ne_eq,not_true_eq_false,false_and,ite_false,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_add]
      _ ≤ _ := lagEnvelope_row_square_sum hT i
  exact (finiteExpectation_mono (p i) (hp i) hr).trans_eq
    (finiteExpectation_const (p i) (hpone i) _)

end JointDickman

end OAI

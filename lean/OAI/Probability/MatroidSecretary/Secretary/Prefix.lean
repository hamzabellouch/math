import OAI.Probability.MatroidProphet.Main
import OAI.Probability.MatroidSecretary.Sampling.UniformPermutationImage
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Fin
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals

namespace OAI

/-!
Finite combinatorial probability for the random secretary prefix.
The Bernoulli mask used to draw the prefix length is part of the initial seed;
its cardinality has the binomial law, and it is independent of the uniformly
random arrival permutation. No product-law assertion conditional on that full
seed is made.

Source: sections/secretary.tex, eq:secretary-prefix-mask, lines 54–66;
SHA256 3554fe0f7296782edf63cc7f1305c377e7a7b9d8f8948b9510ea4ad02a702d63.
These supporting laws include n=0, k=0, k=n, and Bernoulli rates 0 and 1.
-/

namespace MatroidProphet.Secretary
open Finset
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma bitsWeight_constant (p : ℝ) (S : Finset α) :
    bitsWeight (fun _ : α => p) univ S =
      p ^ S.card * (1 - p) ^ (Fintype.card α - S.card) := by
  classical
  unfold bitsWeight
  rw [Finset.prod_ite]
  simp only [filter_mem_eq_inter, univ_inter, prod_const]
  congr 1
  rw [show (univ.filter fun e : α => e ∉ S) = univ \ S by ext; simp]
  rw [card_sdiff_of_subset (subset_univ S), card_univ]

lemma bernoulli_cardinality_mass (p : ℝ) (k : ℕ) :
    (∑ S : Finset α, if S.card = k then bitsWeight (fun _ : α => p) univ S else 0) =
      (Nat.choose (Fintype.card α) k : ℝ) * p ^ k * (1 - p) ^ (Fintype.card α - k) := by
  classical
  rw [← Finset.sum_filter]
  have hf : (univ.filter fun S : Finset α => S.card = k) = univ.powersetCard k := by
    ext S
    simp
  rw [hf]
  calc
    (∑ S ∈ univ.powersetCard k, bitsWeight (fun _ : α => p) univ S) =
        ∑ _S ∈ (univ : Finset α).powersetCard k,
          p ^ k * (1 - p) ^ (Fintype.card α - k) := by
      apply sum_congr rfl
      intro S hS
      rw [bitsWeight_constant, (mem_powersetCard.mp hS).2]
    _ = _ := by simp [card_powersetCard, mul_assoc]

lemma bitsWeight_perm (p : ℝ) (σ : Equiv.Perm α) (S : Finset α) :
    bitsWeight (fun _ : α => p) univ (S.map σ.toEmbedding) =
      bitsWeight (fun _ : α => p) univ S := by
  simp only [bitsWeight_constant, card_map]

lemma bitsExpectation_perm (p : ℝ) (σ : Equiv.Perm α) (f : Finset α → ℝ) :
    bitsExpectation (fun _ : α => p) univ (fun S => f (S.map σ.toEmbedding)) =
      bitsExpectation (fun _ : α => p) univ f := by
  classical
  simp only [bitsExpectation, powerset_univ]
  have h := σ.finsetCongr.sum_comp
    (fun S => bitsWeight (fun _ : α => p) univ S * f S)
  simpa only [Equiv.finsetCongr_apply, bitsWeight_perm] using h

lemma prefix_filter_eq_map {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) :
    (univ.filter fun e : Fin n => (σ.symm e).val < k) =
      (univ.filter fun i : Fin n => i.val < k).map σ.toEmbedding := by
  classical
  ext e
  simp only [mem_filter, mem_univ, true_and, mem_map, Equiv.toEmbedding_apply]
  constructor
  · intro he
    exact ⟨σ.symm e, he, σ.apply_symm_apply e⟩
  · rintro ⟨i, hi, rfl⟩
    simpa only [σ.symm_apply_apply] using hi

lemma prefix_filter_card {n : ℕ} (σ : Equiv.Perm (Fin n)) {k : ℕ} (hk : k ≤ n) :
    (univ.filter fun e : Fin n => (σ.symm e).val < k).card = k := by
  rw [prefix_filter_eq_map, card_map, Fin.card_filter_val_lt, min_eq_right hk]

omit [DecidableEq α] in
lemma integral_uniform_eq_average [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (f : α → ℝ) :
    (∫ a, f a ∂(PMF.uniformOfFintype α).toMeasure) =
      (Fintype.card α : ℝ)⁻¹ * ∑ a, f a := by
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul, ← mul_sum]

/-- Conditional only on the prefix length, the actual uniform-permutation
prefix has the uniform law on all subsets of that cardinality. -/
theorem uniform_prefix_average {n : ℕ} {k : ℕ} (hk : k ≤ n)
    (f : Finset (Fin n) → ℝ) :
    (∑ σ : Equiv.Perm (Fin n),
      f (univ.filter fun e : Fin n => (σ.symm e).val < k)) /
        Fintype.card (Equiv.Perm (Fin n)) =
      (∑ S ∈ (univ : Finset (Fin n)).powersetCard k, f S) /
        Nat.choose n k := by
  simp_rw [prefix_filter_eq_map]
  simpa only [Fin.card_filter_val_lt, min_eq_right hk, Fintype.card_fin] using
    uniform_permutation_image_average
      (univ.filter fun i : Fin n => i.val < k) f

/-- Exact fixed-length atom law, including cardinality mismatch. -/
theorem uniform_prefix_atom {n : ℕ} {k : ℕ} (hk : k ≤ n)
    (S : Finset (Fin n)) :
    (∑ σ : Equiv.Perm (Fin n),
      if (univ.filter fun e : Fin n => (σ.symm e).val < k) = S then (1 : ℝ) else 0) /
        Fintype.card (Equiv.Perm (Fin n)) =
      if k = S.card then (Nat.choose n k : ℝ)⁻¹ else 0 := by
  simp_rw [prefix_filter_eq_map]
  simpa only [Fin.card_filter_val_lt, min_eq_right hk, Fintype.card_fin] using
    uniform_permutation_image_atom
      (univ.filter fun i : Fin n => i.val < k) S

/-- Measure-theoretic form of the fixed-length prefix averaging law. -/
theorem integral_uniform_prefix {n : ℕ} {k : ℕ} (hk : k ≤ n)
    [MeasurableSpace (Equiv.Perm (Fin n))]
    [MeasurableSingletonClass (Equiv.Perm (Fin n))]
    (f : Finset (Fin n) → ℝ) :
    (∫ σ, f (univ.filter fun e : Fin n => (σ.symm e).val < k)
      ∂(PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure) =
      (∑ S ∈ (univ : Finset (Fin n)).powersetCard k, f S) /
        Nat.choose n k := by
  rw [integral_uniform_eq_average]
  simpa only [div_eq_mul_inv, mul_comm] using uniform_prefix_average hk f

end MatroidProphet.Secretary

end OAI

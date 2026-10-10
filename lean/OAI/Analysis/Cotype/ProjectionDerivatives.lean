import OAI.Analysis.Cotype.ProjectionCoefficients
import OAI.Analysis.Cotype.BivariateSplit

namespace OAI

noncomputable section
open scoped BigOperators
open Polynomial
namespace Cotype
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def setIndexEquiv : Finset ι ≃ (ι → Bool) where
  toFun := setIndex
  invFun p := Finset.univ.filter (fun i => p i = true)
  left_inv t := by ext i; simp [setIndex]
  right_inv p := by funext i; cases h : p i <;> simp [setIndex, h]

variable {m : ℕ}

theorem grouped_vector_generating (g : Cube m → ℝ) (x : ℝ) :
    (∑ l ∈ Finset.range (m+1), levelFourier g l * x^l) =
      biasedExpectation g (fun _ => x) := by
  have hf (l : ℕ) : (Finset.univ : Finset (Fin m)).powersetCard l =
      Finset.univ.filter (fun t : Finset (Fin m) => t.card = l) := by
    ext t
    simp [Finset.mem_powersetCard]
  simp only [levelFourier, hf, Finset.sum_filter, Finset.sum_mul]
  rw [Finset.sum_comm]
  have he (t : Finset (Fin m)) :
      (∑ l ∈ Finset.range (m+1), (if t.card = l then fourier g (setIndex t) else 0) * x^l) =
        fourier g (setIndex t) * x^t.card := by
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp [show t.card < m+1 by have h := Finset.card_le_univ t; simp at h; omega]
  simp_rw [he]
  rw [biasedExpectation_common_mean]
  apply Fintype.sum_equiv setIndexEquiv
  intro t
  simp [setIndexEquiv, setIndex]

theorem levelFourier_first {g : Cube m → ℝ} {b : ℝ}
    (hb : ∀ j, fourier g (unitIndex j) = b) : levelFourier g 1 = (m : ℝ)*b := by
  have he (j : Fin m) : setIndex {j} = unitIndex j := by
    funext i; simp [setIndex, unitIndex, eq_comm]
  simp [levelFourier, Finset.powersetCard_one, he, hb]

def retainedSectionU (f : SignMatrix m → ℝ) (d : ℕ) (s : ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (m+1), ∑ l ∈ Finset.range (m+1),
    (retainedCoefficient f d k l * s^k) • (X : ℝ[X])^l

def partialS (f : SignMatrix m → ℝ) (d : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (m+1), ∑ l ∈ Finset.range (m+1),
    (retainedCoefficient f d k l * ((X : ℝ[X])^k).derivative.eval 0) • X^l

def partialU (f : SignMatrix m → ℝ) (d : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (m+1), ∑ l ∈ Finset.range (m+1),
    (retainedCoefficient f d k l * ((X : ℝ[X])^l).derivative.eval 0) • X^k

theorem derivative_eval_zero (Q : ℝ[X]) : Q.derivative.eval 0 = Q.coeff 1 := by
  rw [← coeff_zero_eq_eval_zero, coeff_derivative]
  norm_num

theorem retainedSectionU_eval (f : SignMatrix m → ℝ) (d : ℕ) (s u : ℝ) :
    (retainedSectionU f d s).eval u = truncatedGrouped f d s u := by
  simp only [retainedSectionU, eval_finsetSum, eval_smul, smul_eq_mul, eval_pow,
    eval_X, truncatedGrouped]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  unfold retainedCoefficient
  split_ifs <;> ring

theorem partialS_eval (f : SignMatrix m → ℝ) (d : ℕ) (u : ℝ) :
    (partialS f d).eval u = (retainedSectionS f d u).derivative.eval 0 := by
  simp only [partialS, retainedSectionS, derivative_sum, derivative_smul,
    eval_finsetSum, eval_smul, smul_eq_mul, eval_pow, eval_X]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem partialU_eval (f : SignMatrix m → ℝ) (d : ℕ) (s : ℝ) :
    (partialU f d).eval s = (retainedSectionU f d s).derivative.eval 0 := by
  simp only [partialU, retainedSectionU, derivative_sum, derivative_smul,
    eval_finsetSum, eval_smul, smul_eq_mul, eval_pow, eval_X]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem partialS_eq (f : SignMatrix m → ℝ) {d : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) :
    partialS f d = ∑ l ∈ Finset.range (m+1), (Ckl f 1 l * (1/2 : ℝ)^l) • X^l := by
  simp only [partialS, derivative_eval_zero, coeff_X_pow, eq_comm]
  have he (k l : ℕ) : (retainedCoefficient f d k l * (if k = 1 then (1:ℝ) else 0)) • (X : ℝ[X])^l =
      if k = 1 then (Ckl f 1 l * (1/2 : ℝ)^l) • X^l else 0 := by
    split_ifs with h
    · subst k; simp [retainedCoefficient, hd]
    · simp
  simp_rw [he]
  simp [Finset.sum_ite_eq', show 1 < m+1 by omega]

theorem partialU_eq (f : SignMatrix m → ℝ) {d : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) :
    partialU f d = ∑ k ∈ Finset.range (m+1), (Ckl f k 1 * (1/2 : ℝ)^k) • X^k := by
  simp only [partialU, derivative_eval_zero, coeff_X_pow, eq_comm]
  have he (k l : ℕ) : (retainedCoefficient f d k l * (if l = 1 then (1:ℝ) else 0)) • (X : ℝ[X])^k =
      if l = 1 then (Ckl f k 1 * (1/2 : ℝ)^k) • X^k else 0 := by
    split_ifs with h
    · subst l; simp [retainedCoefficient, hd]
    · simp
  simp_rw [he]
  simp [Finset.sum_ite_eq', show 1 < m+1 by omega]

theorem admissible_partialS {Ψ : SignMatrix m → ℝ} {f g : Cube m → ℝ} {a b : ℝ}
    (h : ScalarAdmissible m a b Ψ f g) {d : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) (u : ℝ) :
    (partialS Ψ d).eval u = (m : ℝ)*a * biasedExpectation g (fun _ => u/2) := by
  obtain ⟨hΨ, _, hg, _, _, _, _, _, hp, _⟩ := h
  rw [partialS_eq Ψ hd hm]
  simp only [eval_finsetSum, eval_smul, smul_eq_mul, eval_pow, eval_X,
    Ckl_one_row hΨ hg hp]
  rw [← grouped_vector_generating]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [div_eq_mul_inv, mul_pow]
  ring

theorem admissible_partialU {Ψ : SignMatrix m → ℝ} {f g : Cube m → ℝ} {a b : ℝ}
    (h : ScalarAdmissible m a b Ψ f g) {d : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) (s : ℝ) :
    (partialU Ψ d).eval s = (m : ℝ)*b * biasedExpectation f (fun _ => s/2) := by
  obtain ⟨hΨ, hf, _, _, _, _, _, _, _, hp⟩ := h
  rw [partialU_eq Ψ hd hm]
  simp only [eval_finsetSum, eval_smul, smul_eq_mul, eval_pow, eval_X,
    Ckl_one_column hΨ hf hp]
  rw [← grouped_vector_generating]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [div_eq_mul_inv, mul_pow]
  ring

theorem admissible_mixed_derivative {Ψ : SignMatrix m → ℝ} {f g : Cube m → ℝ} {a b : ℝ}
    (h : ScalarAdmissible m a b Ψ f g) {d : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) :
    (partialS Ψ d).derivative.eval 0 = ((m : ℝ)*a)*((m : ℝ)*b)/2 := by
  obtain ⟨hΨ, _, hg, _, _, _, _, hb, hp, _⟩ := h
  rw [derivative_eval_zero, partialS_eq Ψ hd hm]
  simp only [finsetSum_coeff, coeff_smul, coeff_X_pow, smul_eq_mul]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  rw [ite_eq_left (Finset.mem_range.mpr (by omega))]
  rw [Ckl_one_row hΨ hg hp, levelFourier_first hb]
  norm_num
  ring

end Cotype

end

end OAI

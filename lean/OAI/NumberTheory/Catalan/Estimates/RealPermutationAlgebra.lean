import Mathlib.Tactic.Ring
import OAI.NumberTheory.Catalan.Analysis.RealPairedIntegral

namespace OAI

noncomputable section

open scoped BigOperators

namespace InternalCatalan

def rawRealIntegrand (N : ℕ) (t s : Fin (n N) → ℝ) : ℝ :=
  Matrix.det (Matrix.of (fun r i : Fin (n N) => realRowAmplitude N r.val (t i))) *
    ∏ k : Fin (n N), (filteredColumn N k.val).eval (s k) / (1 - t k * s k)

def leftRealIntegrand (N : ℕ) (t s : Fin (n N) → ℝ) : ℝ :=
  Matrix.det (Matrix.of (fun r i : Fin (n N) => realRowAmplitude N r.val (t i))) *
    Matrix.det (Matrix.of (fun i j : Fin (n N) => (1 : ℝ) / (1 - t i * s j))) *
      ∏ k : Fin (n N), (filteredColumn N k.val).eval (s k)

def doubleRealIntegrand (N : ℕ) (t s : Fin (n N) → ℝ) : ℝ :=
  Matrix.det (Matrix.of (fun r i : Fin (n N) => realRowAmplitude N r.val (t i))) *
    Matrix.det (Matrix.of (fun i j : Fin (n N) => (1 : ℝ) / (1 - t i * s j))) *
      Matrix.det (Matrix.of (fun j k : Fin (n N) => (filteredColumn N k.val).eval (s j)))

theorem sum_rawRealIntegrand_permute_left (N : ℕ) (t s : Fin (n N) → ℝ) :
    (∑ σ : Equiv.Perm (Fin (n N)), rawRealIntegrand N (t ∘ σ) s) =
      leftRealIntegrand N t s := by
  classical
  unfold rawRealIntegrand leftRealIntegrand
  simp only [Function.comp_apply]
  rw [Matrix.det_apply'
    (Matrix.of (fun i j : Fin (n N) => (1 : ℝ) / (1 - t i * s j)))]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  have hA :
      Matrix.det (Matrix.of (fun r i : Fin (n N) => realRowAmplitude N r.val (t (σ i)))) =
        ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          Matrix.det (Matrix.of (fun r i : Fin (n N) => realRowAmplitude N r.val (t i))) :=
    Matrix.det_permute' σ
      (Matrix.of (fun r i : Fin (n N) => realRowAmplitude N r.val (t i)))
  rw [hA]
  simp only [Matrix.of_apply, div_eq_mul_inv, one_mul, Finset.prod_mul_distrib]
  ring

theorem sum_leftRealIntegrand_permute_right (N : ℕ) (t s : Fin (n N) → ℝ) :
    (∑ τ : Equiv.Perm (Fin (n N)), leftRealIntegrand N t (s ∘ τ)) =
      doubleRealIntegrand N t s := by
  classical
  unfold leftRealIntegrand doubleRealIntegrand
  simp only [Function.comp_apply]
  rw [Matrix.det_apply'
    (Matrix.of (fun j k : Fin (n N) => (filteredColumn N k.val).eval (s j)))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  have hC :
      Matrix.det (Matrix.of (fun i j : Fin (n N) => (1 : ℝ) / (1 - t i * s (τ j)))) =
        ((Equiv.Perm.sign τ : ℤ) : ℝ) *
          Matrix.det (Matrix.of (fun i j : Fin (n N) => (1 : ℝ) / (1 - t i * s j))) :=
    Matrix.det_permute' τ
      (Matrix.of (fun i j : Fin (n N) => (1 : ℝ) / (1 - t i * s j)))
  rw [hC]
  simp only [Matrix.of_apply]
  ring

end InternalCatalan

end

end OAI

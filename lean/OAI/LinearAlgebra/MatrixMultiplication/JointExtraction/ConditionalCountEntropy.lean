import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.PopulationRates

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

noncomputable section

namespace MatrixMultiplication.JointConditionalCountEntropy

open MatrixMultiplication.Foundation JointPopulationRates
open scoped BigOperators

variable {U A : Type*} [Fintype U] [Fintype A]

attribute [local instance] Classical.propDecidable

def classCounts (n : U → ℕ) (f : U → A) (a : A) (u : U) : ℕ :=
  if f u = a then n u else 0

def classSize (n : U → ℕ) (f : U → A) (a : A) : ℕ :=
  ∑ u, classCounts n f a u

theorem classSize_total (n : U → ℕ) (f : U → A) :
    (∑ a, classSize n f a) = ∑ u, n u := by
  classical
  unfold classSize classCounts
  rw [Finset.sum_comm]
  simp

theorem sum_masked_entropy (p : U → ℝ) (f : U → A) :
    (∑ a, finiteEntropy (fun u => if f u = a then p u else 0)) =
      finiteEntropy p := by
  classical
  have ht (a : A) (u : U) :
      entropyTerm (if f u = a then p u else 0) =
        if f u = a then entropyTerm (p u) else 0 := by
    by_cases h : f u = a <;> simp [h]
  simp only [finiteEntropy, ht]
  rw [Finset.sum_comm]
  simp

theorem sum_classCounts_entropy (n : U → ℕ) (f : U → A) (scale : ℝ) :
    (∑ a, finiteEntropy (fun u => (classCounts n f a u : ℝ) / scale)) =
      finiteEntropy (fun u => (n u : ℝ) / scale) := by
  classical
  have hm (a : A) :
      (fun u => (classCounts n f a u : ℝ) / scale) =
        (fun u => if f u = a then (n u : ℝ) / scale else 0) := by
    funext u
    by_cases h : f u = a <;> simp [classCounts, h]
  simp_rw [hm]
  exact sum_masked_entropy _ f

theorem sum_scaled_class_empirical_entropy (n : U → ℕ) (f : U → A)
    (scale : ℝ) :
    (∑ a, ((classSize n f a : ℝ) / scale) *
      finiteEntropy (fun u =>
        (classCounts n f a u : ℝ) / (classSize n f a : ℝ))) =
      finiteEntropy (fun u => (n u : ℝ) / scale) -
        finiteEntropy (fun a => (classSize n f a : ℝ) / scale) := by
  calc
    _ = ∑ a, (finiteEntropy (fun u => (classCounts n f a u : ℝ) / scale) -
        entropyTerm ((classSize n f a : ℝ) / scale)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact weighted_empirical_entropy_eq (classCounts n f a) scale
    _ = _ := by
      rw [Finset.sum_sub_distrib, sum_classCounts_entropy]
      rfl

theorem sum_classSize_mul_empirical_entropy (n : U → ℕ) (f : U → A) :
    (∑ a, (classSize n f a : ℝ) *
      finiteEntropy (fun u =>
        (classCounts n f a u : ℝ) / (classSize n f a : ℝ))) =
      (∑ u, n u : ℕ) *
        (finiteEntropy (fun u => (n u : ℝ) / (∑ v, n v : ℕ)) -
          finiteEntropy (fun a => (classSize n f a : ℝ) / (∑ v, n v : ℕ))) := by
  have hclasses := sum_scaled_class_empirical_entropy n f 1
  have hjoint := weighted_empirical_entropy_eq n 1
  have hmarginal := weighted_empirical_entropy_eq (classSize n f) 1
  simp only [div_one] at hclasses hjoint hmarginal
  rw [classSize_total] at hmarginal
  rw [hclasses, mul_sub, hjoint, hmarginal]
  ring

theorem sum_classSize_mul_entropy_of_law (n : U → ℕ) (f : U → A)
    (p : FiniteLaw U) (scale : ℝ)
    (hn : ∀ u, (n u : ℝ) = scale * p.mass u) :
    (∑ a, (classSize n f a : ℝ) *
      finiteEntropy (fun u =>
        (classCounts n f a u : ℝ) / (classSize n f a : ℝ))) =
      scale * (finiteEntropy p.mass - finiteEntropy (p.map f).mass) := by
  classical
  have hclass (a : A) : (classSize n f a : ℝ) = scale * (p.map f).mass a := by
    rw [classSize, Nat.cast_sum, FiniteLaw.map_mass, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    by_cases h : f u = a <;> simp [classCounts, h, hn]
  have h := sum_scaled_class_empirical_entropy n f 1
  simp only [div_one] at h
  rw [h]
  simp_rw [hn, hclass]
  rw [finiteEntropy_scalar p.mass scale p.total,
    finiteEntropy_scalar (p.map f).mass scale (p.map f).total]
  ring

end MatrixMultiplication.JointConditionalCountEntropy

end

end OAI

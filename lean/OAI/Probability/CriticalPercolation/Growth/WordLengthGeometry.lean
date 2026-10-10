import Mathlib
import OAI.Probability.CriticalPercolation.Growth.PolynomialGrowthDescent

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.HarmonicAnalysis
variable {A : Type*} [Group A]

structure WordGeometry (A : Type*) [Group A] where
  generators : Finset A
  one_mem : (1:A)∈generators
  inv_eq : generators⁻¹=generators
  generates : Subgroup.closure (generators:Set A)=⊤

namespace WordGeometry
variable (W : WordGeometry A)
abbrev ball (n : ℕ) := W.generators^n

lemma exists_mem_ball (a : A) : ∃ n, a∈W.ball n :=
  SparseGrowth.exists_mem_pow W.generators W.inv_eq (by rw [W.generates]; trivial)

def length (a : A) : ℕ := Nat.find (W.exists_mem_ball a)

lemma mem_ball_length (a : A) : a∈W.ball (W.length a) := Nat.find_spec (W.exists_mem_ball a)

lemma length_le_iff {a : A} {n : ℕ} : W.length a≤n ↔ a∈W.ball n := by
  constructor
  · intro h
    exact Finset.pow_subset_pow_right W.one_mem h (W.mem_ball_length a)
  · intro h; exact Nat.find_min' (W.exists_mem_ball a) h

lemma ball_mono : Monotone W.ball := by
  intro m n h
  exact Finset.pow_subset_pow_right W.one_mem h

lemma length_mul_le (a b : A) : W.length (a*b)≤W.length a+W.length b := by
  apply W.length_le_iff.mpr
  rw [ball,pow_add]
  exact Finset.mem_mul.mpr ⟨a,W.mem_ball_length a,b,W.mem_ball_length b,rfl⟩

lemma length_inv (a : A) : W.length a⁻¹=W.length a := by
  have hl (b : A) : W.length b⁻¹≤W.length b := by
    apply W.length_le_iff.mpr
    have hh := Finset.inv_mem_inv (W.mem_ball_length b)
    simpa [ball,←inv_pow,W.inv_eq] using hh
  exact le_antisymm (hl a) (by simpa using hl a⁻¹)

lemma length_one : W.length 1=0 := by
  exact Nat.eq_zero_of_le_zero (W.length_le_iff.mpr (by simp [ball]))

lemma length_generator {s : A} (hs : s∈W.generators) : W.length s≤1 :=
  W.length_le_iff.mpr (by simpa [ball] using hs)

lemma length_mul_generator {s : A} (hs : s∈W.generators) (a : A) :
    W.length (a*s)≤W.length a+1 ∧ W.length a≤W.length (a*s)+1 := by
  constructor
  · exact (W.length_mul_le a s).trans (Nat.add_le_add_left (W.length_generator hs) _)
  · have hh := W.length_mul_le (a*s) s⁻¹
    rw [mul_inv_cancel_right,W.length_inv] at hh
    exact hh.trans (Nat.add_le_add_left (W.length_generator hs) _)

def cutoff (R : ℕ) (a : A) : ℝ := max 0 (2*(R:ℝ)-(W.length a:ℝ))

lemma cutoff_nonneg (R : ℕ) (a : A) : 0≤W.cutoff R a := le_max_left _ _

lemma cutoff_large (R : ℕ) {a : A} (ha : a∈W.ball R) : (R:ℝ)≤W.cutoff R a := by
  have hl : (W.length a:ℝ)≤R := by exact_mod_cast W.length_le_iff.mpr ha
  exact (by linarith : (R:ℝ)≤2*R-W.length a).trans (le_max_right _ _)

lemma cutoff_eq_zero (R : ℕ) {a : A} (ha : 2*R≤W.length a) : W.cutoff R a=0 := by
  have hl : 2*(R:ℝ)≤W.length a := by exact_mod_cast ha
  exact max_eq_left (by linarith)

lemma cutoff_ne_zero_length (R : ℕ) {a : A} (ha : W.cutoff R a≠0) :
    W.length a<2*R := by
  by_contra! h
  exact ha (W.cutoff_eq_zero R h)

lemma cutoff_lipschitz_generator (R : ℕ) {s : A} (hs : s∈W.generators) (a : A) :
    |W.cutoff R (a*s)-W.cutoff R a|≤1 := by
  obtain ⟨h1,h2⟩ := W.length_mul_generator hs a
  have h1' : (W.length (a*s):ℝ)≤(W.length a:ℝ)+1 := by exact_mod_cast h1
  have h2' : (W.length a:ℝ)≤(W.length (a*s):ℝ)+1 := by exact_mod_cast h2
  unfold cutoff
  rw [abs_le]
  constructor <;> rcases le_total 0 (2*(R:ℝ)-W.length (a*s)) with hx|hx <;>
    rcases le_total 0 (2*(R:ℝ)-W.length a) with hy|hy <;>
    simp only [max_eq_right hx,max_eq_left hx,max_eq_right hy,max_eq_left hy] <;> linarith

end WordGeometry
end CriticalPercolation.HarmonicAnalysis
end
end

end OAI

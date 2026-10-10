/-
Copyright (c) 2026 OpenAI. All rights reserved.
Authors: OpenAI
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

namespace OAI

/-!
# Finite Boolean weights and variances

Finite weighted laws support Boolean event masses, complementary masses, and the disagreement
of independent draws. The variance estimates give scalar ingredients for the finite graph
construction in Section 7 of *Constant-factor hardness of uniform sparsest cut*.
-/

open scoped BigOperators

namespace UniformSparsestCut.FiniteWeights

variable {ι : Type*} [Fintype ι]

def indicator (b : Bool) : ℝ := if b then 1 else 0

def disagree (b c : Bool) : ℝ := if b = c then 0 else 1

def total (w : ι → ℝ) : ℝ := ∑ i, w i

def mass (w : ι → ℝ) (h : ι → Bool) : ℝ := ∑ i, w i * indicator (h i)

def variance (w : ι → ℝ) (h : ι → Bool) : ℝ := mass w h * (1 - mass w h)

/-- The weight of a disagreement for two independent draws (not necessarily normalized). -/
def disagreement (w u : ι → ℝ) (h : ι → Bool) : ℝ :=
  ∑ i, w i * ∑ j, u j * disagree (h i) (h j)

theorem indicator_nonneg (b : Bool) : 0 ≤ indicator b := by
  cases b <;> simp [indicator]

theorem indicator_le_one (b : Bool) : indicator b ≤ 1 := by
  cases b <;> simp [indicator]

theorem indicator_not (b : Bool) : indicator (!b) = 1 - indicator b := by
  cases b <;> simp [indicator]

theorem disagree_nonneg (b c : Bool) : 0 ≤ disagree b c := by
  cases b <;> cases c <;> simp [disagree]

theorem disagree_eq (b c : Bool) :
    disagree b c = indicator b * (1 - indicator c) + (1 - indicator b) * indicator c := by
  cases b <;> cases c <;> simp [disagree, indicator]

theorem total_nonneg {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) : 0 ≤ total w :=
  Finset.sum_nonneg (fun i _ => hw i)

theorem total_mono {w u : ι → ℝ} (hwu : ∀ i, w i ≤ u i) : total w ≤ total u :=
  Finset.sum_le_sum (fun i _ => hwu i)

theorem total_add (w u : ι → ℝ) : total (fun i => w i + u i) = total w + total u := by
  simp [total, Finset.sum_add_distrib]

theorem total_smul (a : ℝ) (w : ι → ℝ) : total (fun i => a * w i) = a * total w := by
  simp [total, Finset.mul_sum]

theorem mass_nonneg {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (h : ι → Bool) : 0 ≤ mass w h :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (indicator_nonneg (h i)))

theorem mass_le_total {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (h : ι → Bool) :
    mass w h ≤ total w := by
  apply Finset.sum_le_sum
  intro i _
  simpa using mul_le_mul_of_nonneg_left (indicator_le_one (h i)) (hw i)

theorem mass_mono {w u : ι → ℝ} (hwu : ∀ i, w i ≤ u i) (h : ι → Bool) :
    mass w h ≤ mass u h := by
  exact Finset.sum_le_sum (fun i _ =>
    mul_le_mul_of_nonneg_right (hwu i) (indicator_nonneg (h i)))

theorem mass_add (w u : ι → ℝ) (h : ι → Bool) :
    mass (fun i => w i + u i) h = mass w h + mass u h := by
  simp [mass, add_mul, Finset.sum_add_distrib]

theorem mass_smul (a : ℝ) (w : ι → ℝ) (h : ι → Bool) :
    mass (fun i => a * w i) h = a * mass w h := by
  simp [mass, mul_assoc, Finset.mul_sum]

theorem mass_compl (w : ι → ℝ) (h : ι → Bool) :
    mass w (fun i => !(h i)) = total w - mass w h := by
  simp [mass, indicator_not, mul_sub, Finset.sum_sub_distrib, total]

theorem variance_nonneg {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw₁ : total w = 1)
    (h : ι → Bool) : 0 ≤ variance w h := by
  exact mul_nonneg (mass_nonneg hw h) (sub_nonneg.mpr (hw₁ ▸ mass_le_total hw h))

theorem inner_disagreement (u : ι → ℝ) (h : ι → Bool) (b : Bool) :
    (∑ j, u j * disagree b (h j)) =
      indicator b * (total u - mass u h) + (1 - indicator b) * mass u h := by
  calc
    _ = ∑ j, (indicator b * (u j - u j * indicator (h j)) +
        (1 - indicator b) * (u j * indicator (h j))) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [disagree_eq]
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
        total, mass]

theorem disagreement_eq (w u : ι → ℝ) (h : ι → Bool) :
    disagreement w u h = mass w h * (total u - mass u h) +
      (total w - mass w h) * mass u h := by
  unfold disagreement
  simp_rw [inner_disagreement]
  calc
    _ = ∑ i, ((w i * indicator (h i)) * (total u - mass u h) +
        (w i - w i * indicator (h i)) * mass u h) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib,
        total, mass]

theorem disagreement_self (w : ι → ℝ) (hw : total w = 1) (h : ι → Bool) :
    disagreement w w h = 2 * variance w h := by
  rw [disagreement_eq, hw]
  unfold variance
  ring

theorem disagreement_nonneg {w u : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hu : ∀ i, 0 ≤ u i) (h : ι → Bool) : 0 ≤ disagreement w u h := by
  unfold disagreement
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i)
    (Finset.sum_nonneg (fun j _ => mul_nonneg (hu j) (disagree_nonneg _ _))))

/-- Product domination: the constant is squared, since the two draws are independent. -/
theorem variance_domination {w u : ι → ℝ} {A : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hu : ∀ i, 0 ≤ u i)
    (hw₁ : total w = 1) (hu₁ : total u = 1) (hA : 0 ≤ A)
    (hdom : ∀ i, w i ≤ A * u i) (h : ι → Bool) :
    variance w h ≤ A ^ 2 * variance u h := by
  have hm : mass w h ≤ A * mass u h := by
    simpa [mass_smul] using mass_mono hdom h
  have hc : 1 - mass w h ≤ A * (1 - mass u h) := by
    simpa [mass_smul, mass_compl, total_smul, hw₁, hu₁, mul_sub] using
      mass_mono hdom (fun i => !(h i))
  have hc₀ : 0 ≤ 1 - mass w h := sub_nonneg.mpr (hw₁ ▸ mass_le_total hw h)
  have hm₀ : 0 ≤ A * mass u h := mul_nonneg hA (mass_nonneg hu h)
  have hh := mul_le_mul hm hc hc₀ hm₀
  unfold variance
  nlinarith only [hh]

/-- A change of color with probability at most `L` changes Boolean variance by at most `L`.
This scalar estimate also follows by coupling two independent draws and a union bound. -/
theorem variance_change {z r L : ℝ} (hz₀ : 0 ≤ z) (hz₁ : z ≤ 1)
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) (h₁ : z - r ≤ L) (h₂ : r - z ≤ L) :
    z * (1 - z) ≤ r * (1 - r) + L := by
  rcases le_total z r with hzr | hrz
  · have hh := mul_nonneg (sub_nonneg.mpr hzr) (show 0 ≤ 2 - z - r by linarith)
    nlinarith only [hh, h₂]
  · have hh := mul_nonneg (sub_nonneg.mpr hrz) (add_nonneg hz₀ hr₀)
    nlinarith only [hh, h₁]

end UniformSparsestCut.FiniteWeights

end OAI

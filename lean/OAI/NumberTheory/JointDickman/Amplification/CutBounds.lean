import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace OAI

/-!
# Real cut tests control complex label energies

This is the deterministic estimate (graph-cut-labels) in the manuscript.
It makes no independence assumption about the labels and the kernel.
-/

open scoped BigOperators ComplexConjugate

namespace JointDickman

/-- Signs used in the finite cut maximum. -/
def cutSign (b : Bool) : ℝ := if b then 1 else -1

theorem abs_cutSign (b : Bool) : |cutSign b| = 1 := by
  cases b <;> norm_num [cutSign]

/-- A linear test bounded for all sign vectors is bounded throughout the cube. -/
theorem linear_bound_of_signs {ι : Type*} [Fintype ι] (a : ι → ℝ) (C : ℝ)
    (hsign : ∀ s : ι → Bool, |∑ i, a i * cutSign (s i)| ≤ C)
    (f : ι → ℝ) (hf : ∀ i, |f i| ≤ 1) : |∑ i, a i * f i| ≤ C := by
  classical
  let s : ι → Bool := fun i => decide (0 ≤ a i)
  have heq : (∑ i, a i * cutSign (s i)) = ∑ i, |a i| := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 0 ≤ a i
    · simp [s, cutSign, hi, abs_of_nonneg hi]
    · simp [s, cutSign, hi, abs_of_neg (lt_of_not_ge hi)]
  have hsum : (∑ i, |a i|) ≤ C := by
    have h := hsign s
    rw [heq, abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)] at h
    exact h
  calc
    |∑ i, a i * f i| ≤ ∑ i, |a i * f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |a i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hf i) (abs_nonneg _)).trans_eq (mul_one _)
    _ ≤ C := hsum

noncomputable def realBilinear {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (f g : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, K i j * f i * g j

noncomputable def complexEnergy {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (z : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, (K i j : ℂ) * conj (z i) * z j

/-- The two applications of the linear sign lemma give the exact extension
from the finite sign maximum to arbitrary real test coordinates in `[-1,1]`. -/
theorem realBilinear_bound_of_signs {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (C : ℝ)
    (hcut : ∀ s t : ι → Bool,
      |realBilinear K (fun i => cutSign (s i)) (fun j => cutSign (t j))| ≤ C)
    (f g : ι → ℝ) (hf : ∀ i, |f i| ≤ 1) (hg : ∀ i, |g i| ≤ 1) :
    |realBilinear K f g| ≤ C := by
  have hrow (u v : ι → ℝ) :
      realBilinear K u v = ∑ i, (∑ j, K i j * v j) * u i := by
    simp only [realBilinear, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hcol (u v : ι → ℝ) :
      realBilinear K u v = ∑ j, (∑ i, K i j * u i) * v j := by
    simp only [realBilinear, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hs (s : ι → Bool) : |realBilinear K (fun i => cutSign (s i)) g| ≤ C := by
    rw [hcol]
    apply linear_bound_of_signs _ C _ g hg
    intro t
    rw [← hcol]
    exact hcut s t
  rw [hrow]
  apply linear_bound_of_signs _ C _ f hf
  intro s
  rw [← hrow]
  exact hs s

theorem realBilinear_rescale {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (f g : ι → ℝ) :
    realBilinear K f g =
      4 * realBilinear K (fun i => f i / 2) (fun i => g i / 2) := by
  simp only [realBilinear, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem realBilinear_bound_two {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (C : ℝ)
    (hcut : ∀ f g : ι → ℝ, (∀ i, |f i| ≤ 1) → (∀ i, |g i| ≤ 1) →
      |realBilinear K f g| ≤ C)
    (f g : ι → ℝ) (hf : ∀ i, |f i| ≤ 2) (hg : ∀ i, |g i| ≤ 2) :
    |realBilinear K f g| ≤ 4 * C := by
  rw [realBilinear_rescale, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply hcut
  · intro i
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [hf i]
  · intro i
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [hg i]

theorem complexEnergy_re {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (z : ι → ℂ) :
    (complexEnergy K z).re =
      realBilinear K (fun i => (z i).re) (fun i => (z i).re) +
      realBilinear K (fun i => (z i).im) (fun i => (z i).im) := by
  simp [complexEnergy, realBilinear, Complex.mul_re, Complex.mul_im,
    Finset.sum_add_distrib]

theorem complexEnergy_im {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (z : ι → ℂ) :
    (complexEnergy K z).im =
      realBilinear K (fun i => (z i).re) (fun i => (z i).im) -
      realBilinear K (fun i => (z i).im) (fun i => (z i).re) := by
  simp [complexEnergy, realBilinear, Complex.mul_re, Complex.mul_im,
    Finset.sum_add_distrib, sub_eq_add_neg]

/-- The factor 16 is the one used when the centered labels have norm at most 2. -/
theorem complexEnergy_le_sixteen {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (C : ℝ)
    (hcut : ∀ f g : ι → ℝ, (∀ i, |f i| ≤ 1) → (∀ i, |g i| ≤ 1) →
      |realBilinear K f g| ≤ C)
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 2) :
    ‖complexEnergy K z‖ ≤ 16 * C := by
  have hre (i : ι) : |(z i).re| ≤ 2 := (Complex.abs_re_le_norm _).trans (hz i)
  have him (i : ι) : |(z i).im| ≤ 2 := (Complex.abs_im_le_norm _).trans (hz i)
  have hrr := realBilinear_bound_two K C hcut _ _ hre hre
  have hii := realBilinear_bound_two K C hcut _ _ him him
  have hri := realBilinear_bound_two K C hcut _ _ hre him
  have hir := realBilinear_bound_two K C hcut _ _ him hre
  calc
    ‖complexEnergy K z‖ ≤ |(complexEnergy K z).re| + |(complexEnergy K z).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 16 * C := by
      rw [complexEnergy_re, complexEnergy_im]
      have ha := abs_add_le
        (realBilinear K (fun i => (z i).re) (fun i => (z i).re))
        (realBilinear K (fun i => (z i).im) (fun i => (z i).im))
      have hb := abs_sub
        (realBilinear K (fun i => (z i).re) (fun i => (z i).im))
        (realBilinear K (fun i => (z i).im) (fun i => (z i).re))
      linarith

/-- This uses exactly the finite sign tests in the manuscript's cut norm. -/
theorem complexEnergy_le_sixteen_of_signs {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (C : ℝ)
    (hcut : ∀ s t : ι → Bool,
      |realBilinear K (fun i => cutSign (s i)) (fun j => cutSign (t j))| ≤ C)
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 2) :
    ‖complexEnergy K z‖ ≤ 16 * C :=
  complexEnergy_le_sixteen K C (realBilinear_bound_of_signs K C hcut) z hz

end JointDickman

end OAI

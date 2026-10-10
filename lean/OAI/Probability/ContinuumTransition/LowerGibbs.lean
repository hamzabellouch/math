import OAI.Probability.ContinuumTransition.LowerEnergy

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def kacLowerGain (C : NNReal) (S u : ℝ) (m N n : ℕ) : ℝ :=
  ((gridIndices m 1).card*(n : ℝ)^2*((1-kacRowError C S u)/u^3)-
    (gridIndices (m+N) 1).card*n*scaledKernel S 0)/2

theorem physicalProfile_le_innerBlock {t : ℝ} (ht : 1 < t)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n)
    {q : ℕ} (hq : 0 < q) (hu : 2 ≤ (q : ℝ)/4) (s : Finset Lattice)
    {x y : Space} (hx : x ∈ ⋃ k ∈ s, innerGridBox ((q : ℝ)/4) k)
    (hy : y ∈ ⋃ k ∈ s, innerGridBox ((q : ℝ)/4) k) :
    physicalProfile t σ R ‖x-y‖ ≤ quadraticBlock q (physicalProfile t σ R) 0 x y := by
  obtain ⟨k,_,hxk⟩ := mem_iUnion₂.mp hx
  obtain ⟨l,_,hyl⟩ := mem_iUnion₂.mp hy
  by_cases hkl : k = l
  · rw [quadraticBlock_on hq _ 0 (innerGridBox_subset_gridBox _ _ hxk)
      (hkl ▸ innerGridBox_subset_gridBox _ _ hyl), sub_zero]
  · rw [quadraticBlock_cross hq _ 0 hkl (innerGridBox_subset_gridBox _ _ hxk)
      (innerGridBox_subset_gridBox _ _ hyl)]
    exact physicalProfile_nonpos ht hσ hR ((by norm_num : (1 : ℝ) ≤ 2).trans
      (innerGridBox_separation hu hkl hxk hyl))

theorem kac_gibbsFamily_lower_fixed {C : NNReal} (hC : LipschitzWith C kernel)
    {t β a S μ : ℝ} (ht : 1 < t) (hβ : 0 ≤ β) (ha : 0 ≤ a) (hS : 0 < S)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    {q : ℕ} (hq : 0 < q) (hu : 2 ≤ (q : ℝ)/4) {N m : ℕ}
    (hN : S+(q : ℝ)/4 ≤ (N : ℝ)*((q : ℝ)/4)) (n : ℕ)
    {ι : Type} [Fintype ι] (x : ι → Space)
    (hx : ∀ i, x i ∈ ⋃ k ∈ gridIndices (m+N) 1, innerGridBox ((q : ℝ)/4) k) :
    Real.exp (β*(t*a)*kacLowerGain C S ((q : ℝ)/4) m N n)*
      fixedOccupationFamily (innerGridBox ((q : ℝ)/4)) (gridIndices (m+N) 1) (fun _ => n)
        (gibbsFamily (quadraticBlock q (physicalProfile t σ R) 0) β μ) ι x ≤
      gibbsFamily (fun x y => physicalProfile t (prepend a σ) (prepend S R) ‖x-y‖) β μ ι x := by
  have ht0 : 0 ≤ t := (lt_trans zero_lt_one ht).le
  have hu0 : 0 < (q : ℝ)/4 := by positivity
  unfold fixedOccupationFamily
  split_ifs with hn
  · have hgain := kac_energy_lower_fixed hC hS hu0 hN x n hx hn
    have href := gibbsEnergy_mono (U := fun x y => physicalProfile t σ R ‖x-y‖)
      (V := quadraticBlock q (physicalProfile t σ R) 0) x (fun i j => physicalProfile_le_innerBlock ht hσ hR hq hu
      (gridIndices (m+N) 1) (hx i) (hx j))
    have heq : (fun x y => physicalProfile t (prepend a σ) (prepend S R) ‖x-y‖) =
        (fun x y : Space => physicalProfile t σ R ‖x-y‖-(t*a)*scaledKernel S (x-y)) := by
      funext x y
      exact physicalProfile_prepend t hσ hR hs ‖x-y‖
    rw [heq]
    unfold gibbsFamily
    split_ifs
    · rw [← Real.exp_add, gibbsEnergy_sub, gibbsEnergy_mul_left]
      apply Real.exp_le_exp.mpr
      change kacLowerGain C S ((q : ℝ)/4) m N n ≤ _ at hgain
      have hg := mul_le_mul_of_nonneg_left hgain (mul_nonneg hβ (mul_nonneg ht0 ha))
      have hr := mul_le_mul_of_nonneg_left href hβ
      nlinarith only [hg,hr]
    · simp only [mul_zero, le_refl]
  · simp only [mul_zero]
    exact gibbsFamily_nonneg _ _ _ ι x

end ContinuumTemperature
end

end OAI

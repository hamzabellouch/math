import OAI.Probability.ContinuumTransition.InnerGrid

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem familyTerm_innerBlock {q : ℕ} (hq : 0 < q) (φ : ℝ → ℝ) (β μ : ℝ)
    (k : Lattice) (n : ℕ) :
    familyTerm (gibbsFamily (quadraticBlock q φ 0) β μ) (innerGridBox ((q : ℝ)/4) k) n =
      Real.exp (μ*n)*partition φ β ((q : ℝ)/4-2) n := by
  have he : familyTerm (gibbsFamily (quadraticBlock q φ 0) β μ) (innerGridBox ((q : ℝ)/4) k) n =
      familyTerm (gibbsFamily (fun x y => φ ‖x-y‖-0) β (μ+β*0/2))
        (innerGridBox ((q : ℝ)/4) k) n := by
    simp only [mul_zero, zero_div, add_zero]
    unfold familyTerm familyIntegral
    congr 1
    apply setIntegral_congr_fun
      (measurableSet_generalConfigurations (measurableSet_innerGridBox _ _) (Fin n))
    intro x hx
    unfold gibbsFamily
    rw [gibbsEnergy_congr (W := fun x y => φ ‖x-y‖-0) x (fun i j =>
      quadraticBlock_on hq φ 0 (innerGridBox_subset_gridBox _ _ (hx i))
        (innerGridBox_subset_gridBox _ _ (hx j)))]
  rw [he, familyTerm_shift]
  simp only [mul_zero, zero_div, zero_mul, add_zero, innerGridBox]
  rw [setPartition_translate, setPartition, generalPartition_eq_partition]

theorem grandFinite_innerBlocks {t β μ : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8) {q : ℕ} (hq : 0 < q)
    (s : Finset Lattice) :
    GrandFinite (gibbsFamily (quadraticBlock q (physicalProfile t σ R) 0) β μ)
      (⋃ k ∈ s, innerGridBox ((q : ℝ)/4) k) := by
  have hcoeff : β*0/2*((q : ℝ)/4)^3 ≤
      β*(t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/(4+2/((q : ℝ)/4))^3 := by
    have ha : 0 ≤ t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2 := sub_nonneg.mpr hsmall
    simp only [mul_zero, zero_div, zero_mul]
    positivity
  have hh := grandFinite_quadraticBlocks (μ := μ) ht hβ (le_refl 0) hσ hR hs hsmall hq hcoeff s
  simp only [mul_zero, zero_div, add_zero] at hh
  apply hh.mono_set _ (gibbsFamily_nonneg _ _ _)
  exact iUnion₂_mono (fun k _ => innerGridBox_subset_gridBox _ k)

theorem grandFinite_fixedInnerBlocks {t β μ : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8) {q : ℕ} (hq : 0 < q)
    (s : Finset Lattice) (n : ℕ) :
    GrandFinite (fixedOccupationFamily (innerGridBox ((q : ℝ)/4)) s (fun _ => n)
      (gibbsFamily (quadraticBlock q (physicalProfile t σ R) 0) β μ))
      (⋃ k ∈ s, innerGridBox ((q : ℝ)/4) k) := by
  exact (grandFinite_innerBlocks ht hβ hσ hR hs hsmall hq s).fixedOccupation
    (A := innerGridBox ((q : ℝ)/4)) (s := s) (fun _ => n)
    (fun k _ => measurableSet_innerGridBox _ k)
    (fun ι _ => measurable_gibbsFamily
      (measurable_quadraticBlock q (measurable_physicalProfile t hσ hR hs) 0) β μ ι)
    (gibbsFamily_nonneg _ _ _)

theorem grandIntegral_fixedInnerBlocks {t β μ : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8) {q : ℕ} (hq : 0 < q)
    (s : Finset Lattice) (n : ℕ) :
    grandIntegral (fixedOccupationFamily (innerGridBox ((q : ℝ)/4)) s (fun _ => n)
      (gibbsFamily (quadraticBlock q (physicalProfile t σ R) 0) β μ))
      (⋃ k ∈ s, innerGridBox ((q : ℝ)/4) k) =
        (Real.exp (μ*n)*partition (physicalProfile t σ R) β ((q : ℝ)/4-2) n)^s.card := by
  have hu : 0 < (q : ℝ)/4 := by positivity
  rw [grandIntegral_fixedOccupation_product
    (measurable_quadraticBlock q (measurable_physicalProfile t hσ hR hs) 0)
    (quadraticBlock_symm q (physicalProfile t σ R) 0) β μ _ _ s
    (fun k _ => measurableSet_innerGridBox _ k)
    (fun _ _ _ _ hkl => innerGridBox_disjoint hu hkl)
    (fun _ _ _ _ hkl _ hx _ hy => quadraticBlock_cross hq _ 0 hkl
      (innerGridBox_subset_gridBox _ _ hx) (innerGridBox_subset_gridBox _ _ hy))
    (grandFinite_innerBlocks ht hβ hσ hR hs hsmall hq s)]
  simp only [familyTerm_innerBlock hq, Finset.prod_const]

end ContinuumTemperature
end

end OAI

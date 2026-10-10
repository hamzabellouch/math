import OAI.Probability.ContinuumTransition.BlockPartition

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem grandFinite_quadraticBlocks {t β μ γ : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8) {q : ℕ} (hq : 0 < q)
    (hcoeff : β*γ/2*((q : ℝ)/4)^3 ≤
      β*(t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/(4+2/((q : ℝ)/4))^3) (s : Finset Lattice) :
    GrandFinite (gibbsFamily (quadraticBlock q (physicalProfile t σ R) γ) β (μ+β*γ/2))
      (⋃ k ∈ s, gridBox ((q : ℝ)/4) k) := by
  have hu : 0 < (q : ℝ)/4 := by positivity
  have hC : 0 ≤ t*(∑' n, σ n)*kernelHeight :=
    mul_nonneg (mul_nonneg ht (tsum_nonneg hσ)) kernelHeight_pos.le
  apply grandFinite_gibbs_blocks (quadraticBlock_symm q (physicalProfile t σ R) γ) hβ
    (gridBox ((q : ℝ)/4)) s (fun k _ => measurableSet_gridBox _ k)
    (fun _ _ _ _ hkl => gridBox_disjoint hu hkl)
    (fun _ _ _ _ hkl _ hx _ hy => (quadraticBlock_cross hq (physicalProfile t σ R) γ hkl hx hy).ge)
  · intro ι _
    exact integrableOn_gibbs_of_lower
      (measurable_quadraticBlock q (measurable_physicalProfile t hσ hR hs) γ)
      (add_nonneg hC hγ) hβ
      (quadraticBlock_lower hC hγ (physicalProfile_ge_constant ht hσ hR hs) q)
      (volume_gridBlocks_ne_top hu.le s) ι
  · exact fun k _ => grandFinite_quadraticBlock_box ht hβ hγ hσ hR hs hsmall hq hcoeff k

theorem quadraticBlocks_grand_le {t β μ γ : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8) {q : ℕ} (hq : 0 < q)
    (hcoeff : β*γ/2*((q : ℝ)/4)^3 ≤
      β*(t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/(4+2/((q : ℝ)/4))^3) (s : Finset Lattice) :
    grandIntegral (gibbsFamily (quadraticBlock q (physicalProfile t σ R) γ) β (μ+β*γ/2))
      (⋃ k ∈ s, gridBox ((q : ℝ)/4) k) ≤
    (∑' n, quadraticGrandTerm (physicalProfile t σ R) β μ (β*γ/2*((q : ℝ)/4)^3) ((q : ℝ)/4) n)^s.card := by
  have hu : 0 < (q : ℝ)/4 := by positivity
  have hF := grandFinite_quadraticBlocks (μ := μ) ht hβ hγ hσ hR hs hsmall hq hcoeff s
  have hp := grandIntegral_gibbs_blocks (quadraticBlock_symm q (physicalProfile t σ R) γ) hβ
    (gridBox ((q : ℝ)/4)) s (fun k _ => measurableSet_gridBox _ k)
    (fun _ _ _ _ hkl => gridBox_disjoint hu hkl)
    (fun _ _ _ _ hkl _ hx _ hy => (quadraticBlock_cross hq (physicalProfile t σ R) γ hkl hx hy).ge) hF
  apply hp.trans
  rw [← Finset.prod_const]
  apply Finset.prod_le_prod₀
  · exact fun k _ => grandIntegral_nonneg _ _ (gibbsFamily_nonneg _ _ _)
  · intro k _
    apply (grandFinite_quadraticBlock_box ht hβ hγ hσ hR hs hsmall hq hcoeff k).summable.tsum_le_tsum
      (quadraticBlock_familyTerm_le ht hβ hσ hR hs hsmall hq k)
      (summable_quadraticGrandTerm ht hβ hu hσ hR hs hsmall hcoeff)

end ContinuumTemperature
end

end OAI

import OAI.NumberTheory.CubicMoment.Decomposition.StoppedBinDecomposition

namespace OAI

/-! Weighted finite-sum forms of the exact largest-prime decomposition,
ready for the actual norm twist and cubic character. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPairSupport_primary (R D : Finset Eisenstein)
    (hR : ∀ r ∈ R, primary r) (hD : ∀ d ∈ D, primary d)
    {n : Eisenstein} (hn : n ∈ primaryPairSupport R D) : primary n := by
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hr,hd⟩ := Finset.mem_product.mp ht
  exact primary_mul (hR _ hr) (hD _ hd)

lemma stopped_largest_bin_moment_roles (U R D : Finset Eisenstein)
    (hU : ∀ n ∈ U, primary n) (f K : Eisenstein → ℂ)
    (hK : ∀ n, ¬Squarefree n → K n = 0) (w B ρ : ℝ) {j : ℕ}
    (hj : j < geometricBinCount ρ B) (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool) :
    (∑ n ∈ U, stoppedBeta R D f primeDetectorCutoff w
        (stoppedLargestBinTest B ρ j j₀ k h Z Q early) n*K n) =
      (∑ n ∈ U, stoppedBeta R D f primeDetectorCutoff w
        (stoppedDistinguishedTest B ρ j j₀ k h Z Q early) n*K n)+
      ∑ n ∈ U, stoppedBeta R D f primeDetectorCutoff w
        (stoppedSelectedTest B ρ j j₀ k h Z Q early) n*K n := by
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hs : Squarefree n
  · rw [stoppedBeta_largest_bin_roles R D f w B ρ hj j₀ k h Z Q early (hU n hn) hs,add_mul]
  · simp only [hK n hs,mul_zero,add_zero]

theorem stopped_long_bin_moment_decomposition (U R D : Finset Eisenstein)
    (hU : ∀ n ∈ U, primary n) (f K : Eisenstein → ℂ) (B ρ y w : ℝ)
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hK : ∀ n, ¬(Squarefree n ∧ 1 < norm n ∧ norm n ≤ B) → K n = 0)
    (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool) :
    (∑ n ∈ U, stoppedBeta R D f primeDetectorCutoff w
      (stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B) j₀ k h Z Q early) n*K n) =
    (∑ n ∈ U, stoppedBeta R D f primeDetectorCutoff w
      (stoppedShortBinTest B ρ y j₀ k h Z Q early) n*K n)+
    ∑ j ∈ stoppedLongBins B ρ y, ∑ n ∈ U,
      stoppedBeta R D f primeDetectorCutoff w
        (stoppedLargestBinTest B ρ j j₀ k h Z Q early) n*K n := by
  calc
    _ = ∑ n ∈ U,
        (stoppedBeta R D f primeDetectorCutoff w
          (stoppedShortBinTest B ρ y j₀ k h Z Q early) n+
          ∑ j ∈ stoppedLongBins B ρ y, stoppedBeta R D f primeDetectorCutoff w
            (stoppedLargestBinTest B ρ j j₀ k h Z Q early) n)*K n := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hp : Squarefree n ∧ 1 < norm n ∧ norm n ≤ B
      · rw [stoppedBeta_long_bin_decomposition R D f w B ρ y hρ hρ₂ j₀ k h Z Q early
          (hU n hn) hp.1 hp.2.1 hp.2.2]
      · simp only [hK n hp,mul_zero]
    _ = _ := by
      simp_rw [add_mul,Finset.sum_mul]
      rw [Finset.sum_add_distrib,Finset.sum_comm]

end CubicFirstMoment

end

end OAI

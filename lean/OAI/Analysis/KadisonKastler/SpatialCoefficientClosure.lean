import OAI.Analysis.KadisonKastler.KaplanskyDensity

namespace OAI

/-! # Vanishing vector coefficients pass to the bicommutant -/

namespace KadisonKastler

noncomputable section

open Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem coefficient_zero_generated_contraction
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ η : H)
    (hzero : ∀ a : S, inner ℂ η (a.val ξ) = 0)
    (b : H →L[ℂ] H) (hb : b ∈ generatedVonNeumannAlgebra S) (hbn : ‖b‖ ≤ 1) :
    inner ℂ η (b ξ) = 0 := by
  classical
  have hb' : b ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
    rwa [← generatedVonNeumannAlgebra_coe]
  obtain ⟨a, _, ht⟩ := publishedKaplanskyDensity.exists_strong_contraction_net S b hb' hbn
  have hlim := (tendsto_const_nhds : Tendsto (fun _ : Finset H × ℕ => η) atTop (𝓝 η)).inner
    (𝕜 := ℂ) (ht ξ)
  have he : (fun d : Finset H × ℕ => inner ℂ η ((a d).val ξ)) = fun _ => 0 :=
    funext (fun d => hzero (a d))
  rw [he] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

theorem coefficient_zero_generated
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ η : H)
    (hzero : ∀ a : S, inner ℂ η (a.val ξ) = 0)
    (b : H →L[ℂ] H) (hb : b ∈ generatedVonNeumannAlgebra S) :
    inner ℂ η (b ξ) = 0 := by
  let c : ℝ := ‖b‖ + 1
  have hc : 0 < c := by dsimp [c]; positivity
  have hb' : (c⁻¹ : ℝ) • b ∈ generatedVonNeumannAlgebra S :=
    ((generatedVonNeumannAlgebra S).toStarSubalgebra.toSubalgebra.toSubmodule.restrictScalars
      ℝ).smul_mem c⁻¹ hb
  have hn : ‖(c⁻¹ : ℝ) • b‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le)]
    rw [← div_eq_inv_mul]
    exact (div_le_one hc).mpr (by dsimp [c]; linarith)
  have hz := coefficient_zero_generated_contraction S ξ η hzero _ hb' hn
  change inner ℂ η ((c⁻¹ : ℝ) • b ξ) = 0 at hz
  rw [inner_smul_right_eq_smul] at hz
  exact (smul_eq_zero.mp hz).resolve_left (inv_ne_zero hc.ne')

end

end KadisonKastler

end OAI

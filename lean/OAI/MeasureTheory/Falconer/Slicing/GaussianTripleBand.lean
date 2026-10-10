import OAI.MeasureTheory.Falconer.Slicing.GaussianGram
import OAI.MeasureTheory.Falconer.Slicing.GaussianRows
import OAI.MeasureTheory.Falconer.Slicing.SliceCoordinates

namespace OAI

/-! # Gaussian bands for a nonsingular triple of actual direction vectors -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_three_vector_band (v : Fin 3 → Space d)
    (hv : 0 < (Matrix.gram ℝ v).det) {r : ℝ} (hr : 0 ≤ r) :
    stdGaussian (Space d) {x | ∀ j, |inner ℝ (v j) x| ≤ r} ≤
      ENNReal.ofReal (gaussianVolumeNormalization 3*(Real.sqrt (Matrix.gram ℝ v).det)⁻¹*(2*r)^3) := by
  let V := Submodule.span ℝ (range v)
  have hlin : LinearIndependent ℝ v := Matrix.linearIndependent_of_det_gram_ne_zero (ne_of_gt hv)
  have hdim : Module.finrank ℝ V = 3 := by
    simpa only [Fintype.card_fin] using finrank_span_eq_card hlin
  let e := sliceCoordinates V hdim
  have hw (j : Fin 3) : v j ∈ V := Submodule.subset_span (mem_range_self j)
  have hd := bandCoordinateMap_det_ne_zero v V rfl e
  have hs : Real.sqrt (Matrix.gram ℝ v).det =
      |LinearMap.det (bandCoordinateMap v V e : Space 3 →ₗ[ℝ] Space 3)| := by
    rw [← bandCoordinateMap_det_sq v V hw e,Real.sqrt_sq_eq_abs]
  have hh := gaussian_multi_vector_band v V hw e hd hr
  simpa only [abs_inv,hs] using hh

theorem gaussianRows_three_vector_band (v : Fin 3 → Space d)
    (hv : 0 < (Matrix.gram ℝ v).det) {r : ℝ} (hr : 0 ≤ r) :
    gaussianRows d h {A | ∀ i, ∀ j, |inner ℝ (v j) (A i)| ≤ r} ≤
      ENNReal.ofReal ((gaussianVolumeNormalization 3*(Real.sqrt (Matrix.gram ℝ v).det)⁻¹*(2*r)^3)^h) := by
  have he : {A : Fin h → Space d | ∀ i, ∀ j, |inner ℝ (v j) (A i)| ≤ r} =
      Set.pi univ (fun _ => {x : Space d | ∀ j, |inner ℝ (v j) x| ≤ r}) := by
    ext A
    simp
  rw [gaussianRows,he,Measure.pi_pi]
  calc
    _ ≤ ∏ _ : Fin h, ENNReal.ofReal
        (gaussianVolumeNormalization 3*(Real.sqrt (Matrix.gram ℝ v).det)⁻¹*(2*r)^3) :=
      Finset.prod_le_prod (fun _ _ => gaussian_three_vector_band v hv hr)
    _ = _ := by
      rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← ENNReal.ofReal_pow]
      unfold gaussianVolumeNormalization
      positivity

end Falconer

end OAI

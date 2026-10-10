import OAI.NumberTheory.Ostmann.QuadraticSieveSquareIntegralBoundary
import OAI.NumberTheory.Ostmann.QuadraticSieveSquareIntegralCoefficient
import OAI.NumberTheory.Ostmann.QuadraticSieveSquareIntegralSubstitution

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve
open MeasureTheory Filter Complex Set
open scoped SchwartzMap FourierTransform Topology

theorem fourier_square_integral_of_gap (W : 𝓢(ℝ, ℂ)) {a δ : ℝ}
    (ha : a≠0) (hδ : 0<δ) (hW : ∀ t : ℝ, t<δ → W t=0) :
    (∫ x : ℝ, (𝓕 W) (a*x^2)) =
      (1-(Real.sign a : ℂ)*I)/(Real.sqrt |a| : ℂ)*
        (∫ x : ℝ in Ioi 0, W (x^2)) := by
  rw [fourier_square_integral_gaussian W ha hδ hW]
  have hsupport : ∀ t : ℝ, t∉Ioi (0 : ℝ) → squareGaussianValue 0 a t*W t=0 := by
    intro t ht
    rw [hW t (lt_of_le_of_lt (le_of_not_gt ht) hδ),mul_zero]
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero hsupport]
  calc
    _ = ∫ t : ℝ in Ioi 0,
        ((1-(Real.sign a : ℂ)*I)/(2*(Real.sqrt |a| : ℂ)))*(W t/(Real.sqrt t : ℂ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simp only [squareGaussianValue]
      rw [square_gaussian_boundary_value ha ht]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ = ((1-(Real.sign a : ℂ)*I)/(2*(Real.sqrt |a| : ℂ)))*
        (2*(∫ x : ℝ in Ioi 0, W (x^2))) := by
      rw [integral_const_mul,integral_Ioi_div_sqrt]
    _ = _ := by simp only [div_eq_mul_inv,mul_inv_rev]; ring

theorem positive_compact_support_gap (W : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport W)
    (hs : tsupport W ⊆ Ioi (0 : ℝ)) :
    ∃ δ : ℝ, 0<δ ∧ ∀ t : ℝ, t<δ → W t=0 := by
  by_cases hn : (tsupport W).Nonempty
  · obtain ⟨δ,hδ,hmin⟩ := hc.exists_isLeast hn
    refine ⟨δ,hs hδ,?_⟩
    intro t ht
    by_contra hWt
    have hmem : t∈tsupport W := subset_tsupport W (Function.mem_support.mpr hWt)
    exact (not_le_of_gt ht) (hmin hmem)
  · refine ⟨1,by norm_num,?_⟩
    intro t ht
    by_contra hWt
    exact hn ⟨t,subset_tsupport W (Function.mem_support.mpr hWt)⟩

theorem fourier_square_integral (W : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport W)
    (hs : tsupport W ⊆ Ioi (0 : ℝ)) {a : ℝ} (ha : a≠0) :
    (∫ x : ℝ, (𝓕 W) (a*x^2)) =
      (1-(Real.sign a : ℂ)*I)/(Real.sqrt |a| : ℂ)*
        (∫ x : ℝ in Ioi 0, W (x^2)) := by
  obtain ⟨δ,hδ,hW⟩ := positive_compact_support_gap W hc hs
  exact fourier_square_integral_of_gap W ha hδ hW

end Ostmann.QuadraticSieve

end

end OAI

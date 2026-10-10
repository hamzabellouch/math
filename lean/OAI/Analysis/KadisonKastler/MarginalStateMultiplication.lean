import OAI.Analysis.KadisonKastler.PureStateExtension
import OAI.Analysis.KadisonKastler.CornerStatePullback

namespace OAI

/-! # Multiplication bounds from a normal vector-state marginal

A state on the ambient operator algebra need not be normal. Agreement
with a vector state on one algebra is enough for the corresponding
one-sided multiplication estimate.
-/

namespace KadisonKastler

open NaimarkZFC
open scoped ComplexOrder

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem state_left_mul_le_of_vector_marginal
    (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (hφ : IsState φ) (Ω : H)
    (a b : H →L[ℂ] H)
    (ha : φ (a*star a)=((‖star a Ω‖^2 : ℝ) : ℂ)) :
    ‖φ (a*b)‖ ≤ ‖star a Ω‖*‖b‖ := by
  let : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _
  let f := positiveOfSquares φ hφ.2
  have hf : f 1=1 := ((isState_iff φ).mp hφ).1
  have he : φ (a*b)=inner ℂ (gnsOrbit f (star a)) (gnsOrbit f b) := by
    simp only [gnsOrbit_apply,UniformSpace.Completion.inner_coe,
      PositiveLinearMap.preGNS_inner_def,PositiveLinearMap.ofPreGNS_toPreGNS,star_star]
    rfl
  have ha' : ‖gnsOrbit f (star a)‖=‖star a Ω‖ := by
    rw [gnsOrbit_norm,star_star]
    change Real.sqrt (φ (a*star a)).re=‖star a Ω‖
    rw [ha,Complex.ofReal_re,Real.sqrt_sq (norm_nonneg _)]
  have hb : ‖gnsOrbit f b‖ ≤ ‖b‖ := by
    change ‖f.gnsStarAlgHom b (gnsVector f)‖ ≤ ‖b‖
    calc
      _ ≤ ‖f.gnsStarAlgHom b‖*‖gnsVector f‖ := (f.gnsStarAlgHom b).le_opNorm _
      _ ≤ ‖b‖*‖gnsVector f‖ := mul_le_mul_of_nonneg_right
        (NonUnitalStarAlgHom.norm_apply_le f.gnsStarAlgHom b) (norm_nonneg _)
      _ = ‖b‖ := by rw [gnsVector_norm_eq_one f hf,mul_one]
  rw [he]
  exact (norm_inner_le_norm _ _).trans (by rw [ha']; gcongr)

theorem state_right_mul_le_of_vector_marginal
    (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (hφ : IsState φ) (Ω : H)
    (a b : H →L[ℂ] H)
    (hb : φ (star b*b)=((‖b Ω‖^2 : ℝ) : ℂ)) :
    ‖φ (a*b)‖ ≤ ‖a‖*‖b Ω‖ := by
  let : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _
  let f := positiveOfSquares φ hφ.2
  have hf : f 1=1 := ((isState_iff φ).mp hφ).1
  have he : φ (a*b)=inner ℂ (gnsOrbit f (star a)) (gnsOrbit f b) := by
    simp only [gnsOrbit_apply,UniformSpace.Completion.inner_coe,
      PositiveLinearMap.preGNS_inner_def,PositiveLinearMap.ofPreGNS_toPreGNS,star_star]
    rfl
  have hb' : ‖gnsOrbit f b‖=‖b Ω‖ := by
    rw [gnsOrbit_norm]
    change Real.sqrt (φ (star b*b)).re=‖b Ω‖
    rw [hb,Complex.ofReal_re,Real.sqrt_sq (norm_nonneg _)]
  have ha : ‖gnsOrbit f (star a)‖ ≤ ‖a‖ := by
    change ‖f.gnsStarAlgHom (star a) (gnsVector f)‖ ≤ ‖a‖
    calc
      _ ≤ ‖f.gnsStarAlgHom (star a)‖*‖gnsVector f‖ := (f.gnsStarAlgHom (star a)).le_opNorm _
      _ ≤ ‖star a‖*‖gnsVector f‖ := mul_le_mul_of_nonneg_right
        (NonUnitalStarAlgHom.norm_apply_le f.gnsStarAlgHom (star a)) (norm_nonneg _)
      _ = ‖a‖ := by rw [gnsVector_norm_eq_one f hf,mul_one,norm_star]
  rw [he]
  exact (norm_inner_le_norm _ _).trans (by rw [hb']; gcongr)

end

end KadisonKastler

end OAI

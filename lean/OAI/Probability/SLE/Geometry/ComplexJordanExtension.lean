import Schoenflies.JordanSchoenflies

namespace OAI

/-! Complex-coordinate application of the relative Schönflies theorem.
The prescribed boundary homeomorphism is retained pointwise. -/
noncomputable section
open Set

namespace SLEExactGauge

def complexPlaneCoordinates : ℂ ≃ₜ Schoenflies.Plane where
  toFun z := !₂[z.re,z.im]
  invFun v := ⟨v 0,v 1⟩
  left_inv _ := rfl
  right_inv v := by
    ext i
    fin_cases i <;> rfl
  continuous_toFun := by
    apply (PiLp.continuous_toLp _ _).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact Complex.continuous_re
    · exact Complex.continuous_im
  continuous_invFun := by
    have hc : Continuous (fun v : Schoenflies.Plane =>
        (v 0 : ℂ)+(v 1 : ℂ)*Complex.I) := by fun_prop
    convert hc using 1
    funext v
    apply Complex.ext <;> simp

lemma complexPlaneCoordinates_isArcBetween
    (p : ℝ → ℂ) (hc : ContinuousOn p (Icc 0 1)) (hi : InjOn p (Icc 0 1)) :
    Schoenflies.IsArcBetween (complexPlaneCoordinates '' (p '' Icc 0 1))
      (complexPlaneCoordinates (p 0)) (complexPlaneCoordinates (p 1)) := by
  refine ⟨complexPlaneCoordinates ∘ p,
    complexPlaneCoordinates.continuous.comp_continuousOn hc,
    (complexPlaneCoordinates.injective.injOn).comp hi (mapsTo_image p _),?_,rfl,rfl⟩
  rw [image_image]
  rfl

theorem complex_jordan_extension {C D : Set ℂ}
    (hC : Schoenflies.IsJordanCurve (complexPlaneCoordinates '' C))
    (hD : Schoenflies.IsJordanCurve (complexPlaneCoordinates '' D))
    (e : C ≃ₜ D) :
    ∃ H : ℂ ≃ₜ ℂ, ∀ z : C, H z=e z := by
  let ec := ((complexPlaneCoordinates.image C).symm.trans e).trans
    (complexPlaneCoordinates.image D)
  obtain ⟨F,hF⟩ := Schoenflies.jordan_schoenflies_of_homeomorph hC hD ec
  refine ⟨(complexPlaneCoordinates.trans F).trans complexPlaneCoordinates.symm,?_⟩
  intro z
  apply complexPlaneCoordinates.injective
  have hh := hF ((complexPlaneCoordinates.image C) z)
  simpa [ec] using hh

end SLEExactGauge

end

end OAI

import OAI.NumberTheory.CubicGram.PeriodicPoisson

namespace OAI

/-! Integral self-duality for the symmetric Eisenstein trace pairing. -/

noncomputable section
open MeasureTheory
namespace CubicFirstMoment

private def traceBilinear : ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] ℝ where
  toFun z :=
    { toFun := fun w => tracePair z w
      map_add' := by intro a b; simp [tracePair,mul_add]
      map_smul' := by intro r w; simp [tracePair,Complex.real_smul]; ring }
  map_add' := by
    intro a b
    ext w
    simp [tracePair,add_mul]
    ring
  map_smul' := by
    intro r z
    ext w
    simp [tracePair,Complex.real_smul]
    ring

lemma integral_traceFourier_mul (f g : ℂ → ℂ) (hf : Integrable f) (hg : Integrable g) :
    (∫ y : ℂ, traceFourier f y*g y) = ∫ x : ℂ, f x*traceFourier g x := by
  have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (L := traceBilinear) (ContinuousLinearMap.mul ℂ ℂ)
    Real.continuous_fourierChar
    (by change Continuous (fun p : ℂ × ℂ => 2*(p.1*p.2).re); fun_prop) hf hg
  have hflip (x y : ℂ) : traceBilinear.flip x y = tracePair x y := by
    change tracePair y x = tracePair x y
    simp only [tracePair,mul_comm]
  have hpair (x y : ℂ) : traceBilinear x y = tracePair x y := rfl
  simpa only [VectorFourier.fourierIntegral,hpair,hflip,traceFourier,
    Circle.smul_def,smul_eq_mul,ContinuousLinearMap.mul_apply',LinearMap.coe_mk,AddHom.coe_mk]
    using h

end CubicFirstMoment

end

end OAI

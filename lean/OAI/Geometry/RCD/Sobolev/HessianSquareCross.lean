import OAI.Geometry.RCD.Sobolev.HessianActionLocality

namespace OAI

/-! # The Hessian of a square in an arbitrary regular direction -/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem localHessianAction_square_cross {Ω : Set X}
    (f g Ffg Fgg P : SobolevSpace μ hQ) (A B : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ f x|≤A)
    (hF : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ Ffg x|≤B)
    (hFr : SobolevSpace.toLp μ hQ Ffg =ᵐ[μ.restrict Ω] localGamma μ hQ f g)
    (hPr : SobolevSpace.toLp μ hQ P =ᵐ[μ.restrict Ω]
      localGamma μ hQ (SobolevSpace.product μ hQ f f A A) g) :
    localHessianAction μ hQ (SobolevSpace.product μ hQ f f A A) g g P P Fgg
      =ᵐ[μ.restrict Ω] fun x =>
        2*SobolevSpace.toLp μ hQ f x*localHessianAction μ hQ f g g Ffg Ffg Fgg x+
          2*(localGamma μ hQ f g x)^2 := by
  have hP : SobolevSpace.toLp μ hQ P =ᵐ[μ.restrict Ω]
      SobolevSpace.toLp μ hQ ((2:ℝ) • SobolevSpace.product μ hQ f Ffg A B) := by
    filter_upwards [hPr,hFr,
      ae_restrict_of_ae (localGamma_product_left μ hQ f f g A A hf hf),
      ae_restrict_of_ae (SobolevSpace.product_coe μ hQ f Ffg A B hf hF),
      ae_restrict_of_ae (Lp.coeFn_smul (2:ℝ)
        (SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ f Ffg A B)))]
      with x hp hr hprod hrep hsmul
    simp only [map_smul,Pi.smul_apply,smul_eq_mul] at *
    rw [hp,hprod,hsmul,hrep,hr]
    ring
  exact (localHessianAction_congr μ hQ EventuallyEq.rfl EventuallyEq.rfl
    EventuallyEq.rfl hP hP EventuallyEq.rfl).trans
    ((localHessianAction_potential_square μ hQ f g g Ffg Ffg Fgg A B B hf hF hF hFr hFr).mono
      fun x hx => by rw [hx]; ring)

end RegularPointCoordinates

end

end OAI

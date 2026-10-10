import OAI.Geometry.RCD.Sobolev.HessianPotentialSquare

namespace OAI

/-! # Local representative independence of the Hessian action -/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem localHessianAction_congr {Ω : Set X}
    {f f' u u' v v' fu fu' fv fv' uv uv' : SobolevSpace μ hQ}
    (hf : SobolevSpace.toLp μ hQ f =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ f')
    (hu : SobolevSpace.toLp μ hQ u =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ u')
    (hv : SobolevSpace.toLp μ hQ v =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ v')
    (hfu : SobolevSpace.toLp μ hQ fu =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ fu')
    (hfv : SobolevSpace.toLp μ hQ fv =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ fv')
    (huv : SobolevSpace.toLp μ hQ uv =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ uv') :
    localHessianAction μ hQ f u v fu fv uv =ᵐ[μ.restrict Ω]
      localHessianAction μ hQ f' u' v' fu' fv' uv' := by
  filter_upwards [localGamma_pair_congr_ae μ hQ hu hfv,
    localGamma_pair_congr_ae μ hQ hv hfu,
    localGamma_pair_congr_ae μ hQ hf huv] with x h₁ h₂ h₃
  simp only [localHessianAction,h₁,h₂,h₃]

/-- The square identity uses any local Gram representatives, including
the entries of the common finite-family Bochner construction. -/
theorem localHessianAction_square_self {Ω : Set X}
    (g G P : SobolevSpace μ hQ) (A B : ℝ≥0)
    (hg : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ g x|≤A)
    (hG : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ G x|≤B)
    (hGr : SobolevSpace.toLp μ hQ G =ᵐ[μ.restrict Ω] localGamma μ hQ g g)
    (hPr : SobolevSpace.toLp μ hQ P =ᵐ[μ.restrict Ω]
      localGamma μ hQ (SobolevSpace.product μ hQ g g A A) g) :
    localHessianAction μ hQ (SobolevSpace.product μ hQ g g A A) g g P P G
      =ᵐ[μ.restrict Ω] fun x =>
        2*SobolevSpace.toLp μ hQ g x*localHessianAction μ hQ g g g G G G x+
          2*(localGamma μ hQ g g x)^2 := by
  have hP : SobolevSpace.toLp μ hQ P =ᵐ[μ.restrict Ω]
      SobolevSpace.toLp μ hQ ((2:ℝ) • SobolevSpace.product μ hQ g G A B) := by
    filter_upwards [hPr,hGr,
      ae_restrict_of_ae (localGamma_product_left μ hQ g g g A A hg hg),
      ae_restrict_of_ae (SobolevSpace.product_coe μ hQ g G A B hg hG),
      ae_restrict_of_ae (Lp.coeFn_smul (2:ℝ)
        (SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ g G A B)))]
      with x hp hr hprod hrep hsmul
    simp only [map_smul,Pi.smul_apply,smul_eq_mul] at *
    rw [hp,hprod,hsmul,hrep,hr]
    ring
  exact (localHessianAction_congr μ hQ EventuallyEq.rfl EventuallyEq.rfl
    EventuallyEq.rfl hP hP EventuallyEq.rfl).trans
    ((localHessianAction_potential_square μ hQ g g g G G G A B B hg hG hG hGr hGr).mono
      fun x hx => by rw [hx]; ring)

end RegularPointCoordinates

end

end OAI

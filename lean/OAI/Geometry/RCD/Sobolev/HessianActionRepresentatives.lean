import OAI.Geometry.RCD.Sobolev.HessianActionLocality

namespace OAI

/-! # Transferring Hessian actions between locally equal directions -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem localHessianAction_congr_of_grams {Ω : Set X}
    (w u u' v v' A A' B B' C C' : SobolevSpace μ Q)
    (hu : SobolevSpace.toLp μ Q u =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ Q u')
    (hv : SobolevSpace.toLp μ Q v =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ Q v')
    (hA : SobolevSpace.toLp μ Q A =ᵐ[μ.restrict Ω] localGamma μ Q w u)
    (hA' : SobolevSpace.toLp μ Q A' =ᵐ[μ.restrict Ω] localGamma μ Q w u')
    (hB : SobolevSpace.toLp μ Q B =ᵐ[μ.restrict Ω] localGamma μ Q w v)
    (hB' : SobolevSpace.toLp μ Q B' =ᵐ[μ.restrict Ω] localGamma μ Q w v')
    (hC : SobolevSpace.toLp μ Q C =ᵐ[μ.restrict Ω] localGamma μ Q u v)
    (hC' : SobolevSpace.toLp μ Q C' =ᵐ[μ.restrict Ω] localGamma μ Q u' v') :
    localHessianAction μ Q w u v A B C =ᵐ[μ.restrict Ω]
      localHessianAction μ Q w u' v' A' B' C' := by
  apply localHessianAction_congr μ Q (EventuallyEq.refl _ _) hu hv
  · exact (hA.trans (localGamma_pair_congr_ae μ Q (EventuallyEq.refl _ _) hu)).trans hA'.symm
  · exact (hB.trans (localGamma_pair_congr_ae μ Q (EventuallyEq.refl _ _) hv)).trans hB'.symm
  · exact (hC.trans (localGamma_pair_congr_ae μ Q hu hv)).trans hC'.symm

end RegularPointCoordinates

end

end OAI

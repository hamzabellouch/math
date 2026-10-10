import OAI.Analysis.KadisonKastler.ScalarPacketMeasure
import OAI.Analysis.KadisonKastler.IsometricCompressionState

namespace OAI

/-! # Packet compression equals the scalar probability action average -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem scalarPacketAverage_eq_compression
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (hφ : ‖φ‖=1) (T : H →L[ℂ] H) :
    scalarPacketAverage U hU φ hφ T=
      operatorCompression (regularGaugedPacket U hU φ) (regularConstantHom volume T) := by
  suffices he : (scalarPacketAverage U hU φ hφ T).toLinearMap=
      (operatorCompression (regularGaugedPacket U hU φ) (regularConstantHom volume T)).toLinearMap by
    ext ξ
    exact LinearMap.congr_fun he ξ
  apply (ext_inner_map _ _).mp
  intro ξ
  have h : inner ℂ ξ (scalarPacketAverage U hU φ hφ T ξ)=
      inner ℂ ξ (operatorCompression (regularGaugedPacket U hU φ)
        (regularConstantHom volume T) ξ) := by
    rw [operatorCompression_apply]
    change inner ℂ ξ (scalarPacketAverage U hU φ hφ T ξ)=
      inner ℂ ξ ((regularGaugedPacket U hU φ).adjoint
        (regularConstantHom volume T (regularGaugedPacket U hU φ ξ)))
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact (regularGaugedPacket_coefficient U hU φ hφ T ξ).symm
  have hs := congrArg star h
  calc
    _ = star (inner ℂ ξ (scalarPacketAverage U hU φ hφ T ξ)) := (inner_conj_symm _ _).symm
    _ = star (inner ℂ ξ (operatorCompression (regularGaugedPacket U hU φ)
      (regularConstantHom volume T) ξ)) := hs
    _ = _ := inner_conj_symm _ _

theorem scalarPacketAverage_selfAdjoint
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (hφ : ‖φ‖=1)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (scalarPacketAverage U hU φ hφ T) := by
  rw [scalarPacketAverage_eq_compression]
  have hc : (regularConstantHom (volume : Measure ℝ) T).adjoint=regularConstantHom volume T := by
    rw [← ContinuousLinearMap.star_eq_adjoint,← map_star,hT.star_eq]
  change (operatorCompression (regularGaugedPacket U hU φ) (regularConstantHom volume T)).adjoint=_
  simp only [operatorCompression_apply,ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,hc,ContinuousLinearMap.comp_assoc]

end

end KadisonKastler

end OAI

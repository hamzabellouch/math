import OAI.Analysis.KadisonKastler.RegularCommutantDiagonal
import OAI.Analysis.KadisonKastler.RegularCoreHilbertSum

namespace OAI

/-! # Gauged wave-packet coefficients

Compression between two scalar wave packets turns commutation with the
regular copy of `P` into membership in `P'`. Translation commutation
then gives the exact covariance of these coefficients. These are the
operator-valued coefficients used in the regular commutant argument.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))

/-- A scalar wave packet in the regular representation, with its gauge removed. -/
def regularGaugedPacket (φ : Lp ℂ 2 (volume : Measure ℝ)) :
    H →L[ℂ] RegularCoreHilbert H :=
  (star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H).comp
    (regularTensorVector φ)

theorem regularGaugedPacket_apply_ae (φ : Lp ℂ 2 (volume : Measure ℝ)) (ξ : H) :
    regularGaugedPacket U hU φ ξ =ᵐ[volume] fun t =>
      (star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) (φ t • ξ) := by
  filter_upwards [regularGauge_star_apply_ae U hU (regularTensorVector φ ξ),
    regularTensorVector_apply_ae φ ξ] with t hg hφ
  exact hg.trans (congrArg (star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) hφ)

theorem norm_regularGaugedPacket_apply (φ : Lp ℂ 2 (volume : Measure ℝ)) (ξ : H) :
    ‖regularGaugedPacket U hU φ ξ‖ = ‖φ‖ * ‖ξ‖ := by
  change ‖(star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (regularTensorVector φ ξ)‖ = _
  exact (Unitary.norm_map (star (regularGauge U hU)) (regularTensorVector φ ξ)).trans
    (norm_regularTensorVector φ ξ)

theorem norm_regularGaugedPacket_le (φ : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖regularGaugedPacket U hU φ‖ ≤ ‖φ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro ξ
  exact (norm_regularGaugedPacket_apply U hU φ ξ).le

/-- The packet inclusion intertwines the original and regular actions. -/
theorem regularGaugedPacket_intertwines
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (A : H →L[ℂ] H) :
    (regularCoreEmbedding U hU A).comp (regularGaugedPacket U hU φ) =
      (regularGaugedPacket U hU φ).comp A := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [regularCoreEmbedding_apply_ae U hU A (regularGaugedPacket U hU φ ξ),
    regularGaugedPacket_apply_ae U hU φ ξ,
    regularGaugedPacket_apply_ae U hU φ (A ξ)] with t hπ hφ hA
  change regularCoreEmbedding U hU A (regularGaugedPacket U hU φ ξ) t =
    regularGaugedPacket U hU φ (A ξ) t
  rw [hπ, hφ, hA]
  have hc : (U (Multiplicative.ofAdd t) : H →L[ℂ] H)
      ((star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) (φ t • ξ)) = φ t • ξ := by
    exact congrArg (fun B : H →L[ℂ] H => B (φ t • ξ))
      (Unitary.mul_star_self_of_mem (U (Multiplicative.ofAdd t)).property)
  rw [hc, map_smul]

/-- The adjoint packet intertwines in the reverse direction. -/
theorem regularGaugedPacket_adjoint_intertwines
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (A : H →L[ℂ] H) :
    (regularGaugedPacket U hU φ).adjoint.comp (regularCoreEmbedding U hU A) =
      A.comp (regularGaugedPacket U hU φ).adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint
    (regularGaugedPacket_intertwines U hU φ (star A))
  have he : (regularCoreEmbedding U hU (star A)).adjoint = regularCoreEmbedding U hU A := by
    rw [StarHomClass.map_star, ← ContinuousLinearMap.star_eq_adjoint, star_star]
  have ha : (star A).adjoint = A := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_star]
  simpa only [ContinuousLinearMap.adjoint_comp, he, ha] using h

/-- An operator coefficient between two wave packets. -/
def regularPacketCoefficient
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (φ ψ : Lp ℂ 2 (volume : Measure ℝ)) : H →L[ℂ] H :=
  (regularGaugedPacket U hU φ).adjoint.comp (T.comp (regularGaugedPacket U hU ψ))

theorem inner_regularPacketCoefficient
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (φ ψ : Lp ℂ 2 (volume : Measure ℝ)) (ξ η : H) :
    inner ℂ η (regularPacketCoefficient U hU T φ ψ ξ) =
      inner ℂ (regularGaugedPacket U hU φ η) (T (regularGaugedPacket U hU ψ ξ)) := by
  change inner ℂ η ((regularGaugedPacket U hU φ).adjoint
    (T (regularGaugedPacket U hU ψ ξ))) = _
  exact ContinuousLinearMap.adjoint_inner_right (regularGaugedPacket U hU φ) η
    (T (regularGaugedPacket U hU ψ ξ))

/-- Core commutation forces every packet coefficient into the original commutant. -/
theorem regularPacketCoefficient_mem_commutant (P : VonNeumannAlgebra H)
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ A ∈ P, Commute T (regularCoreEmbedding U hU A))
    (φ ψ : Lp ℂ 2 (volume : Measure ℝ)) :
    regularPacketCoefficient U hU T φ ψ ∈ P.commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro A hA
  apply ContinuousLinearMap.ext
  intro ξ
  change A ((regularGaugedPacket U hU φ).adjoint (T (regularGaugedPacket U hU ψ ξ))) =
    (regularGaugedPacket U hU φ).adjoint (T (regularGaugedPacket U hU ψ (A ξ)))
  have hleft := congrArg (fun B : RegularCoreHilbert H →L[ℂ] H =>
    B (T (regularGaugedPacket U hU ψ ξ)))
    (regularGaugedPacket_adjoint_intertwines U hU φ A)
  have hright := congrArg (fun B : H →L[ℂ] RegularCoreHilbert H => B ξ)
    (regularGaugedPacket_intertwines U hU ψ A)
  have hcomm := congrArg (fun B : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H =>
    B (regularGaugedPacket U hU ψ ξ)) (hT A hA).eq
  change (regularGaugedPacket U hU φ).adjoint
    (regularCoreEmbedding U hU A (T (regularGaugedPacket U hU ψ ξ))) =
    A ((regularGaugedPacket U hU φ).adjoint (T (regularGaugedPacket U hU ψ ξ))) at hleft
  change regularCoreEmbedding U hU A (regularGaugedPacket U hU ψ ξ) =
    regularGaugedPacket U hU ψ (A ξ) at hright
  change T (regularCoreEmbedding U hU A (regularGaugedPacket U hU ψ ξ)) =
    regularCoreEmbedding U hU A (T (regularGaugedPacket U hU ψ ξ)) at hcomm
  rw [← hleft, ← hcomm, hright]

/-- Translation shifts a scalar packet and acts on its vector by `U_s*`. -/
theorem regularTranslation_gaugedPacket
    (s : Multiplicative ℝ) (φ : Lp ℂ 2 (volume : Measure ℝ)) :
    (regularRightTranslation (H := H) s :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H).comp (regularGaugedPacket U hU φ) =
    (regularGaugedPacket U hU (regularTranslateApply s.toAdd φ)).comp
      (star (U s) : H →L[ℂ] H) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [regularRightTranslation_apply_ae s (regularGaugedPacket U hU φ ξ),
    (measurePreserving_add_right volume s.toAdd).quasiMeasurePreserving.ae_eq_comp
      (regularGaugedPacket_apply_ae U hU φ ξ),
    regularGaugedPacket_apply_ae U hU (regularTranslateApply s.toAdd φ)
      ((star (U s) : H →L[ℂ] H) ξ), regularTranslateApply_ae s.toAdd φ]
    with t hρ hφ hψ ht
  simp only [Function.comp_def] at hφ
  change (regularRightTranslation (H := H) s :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (regularGaugedPacket U hU φ ξ) t =
    regularGaugedPacket U hU (regularTranslateApply s.toAdd φ)
      ((star (U s) : H →L[ℂ] H) ξ) t
  rw [hρ, hφ, hψ, ht]
  have hmul : U (Multiplicative.ofAdd (t + s.toAdd)) = U s * U (Multiplicative.ofAdd t) := by
    rw [add_comm]
    exact map_mul U s (Multiplicative.ofAdd t)
  rw [hmul, Submonoid.coe_mul, star_mul, mul_apply_eq_comp, map_smul]

end

end KadisonKastler

end OAI

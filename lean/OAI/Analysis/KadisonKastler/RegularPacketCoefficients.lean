import OAI.Analysis.KadisonKastler.RegularCommutantPackets
import OAI.Analysis.KadisonKastler.RegularCoreBasis

namespace OAI

/-! # Covariance and faithfulness of regular packet coefficients

Gauged scalar packets span the whole regular Hilbert space. Consequently
their operator coefficients are faithful, and simultaneous translation of
the two scalar packets is conjugation of the coefficient by the original
unitary group.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))

/-- Rewriting the packet translation identity in the forward vector direction. -/
theorem regularGaugedPacket_translate
    (s : Multiplicative ℝ) (φ : Lp ℂ 2 (volume : Measure ℝ)) (ξ : H) :
    regularGaugedPacket U hU (regularTranslateApply s.toAdd φ) ξ =
      (regularRightTranslation (H := H) s :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
        (regularGaugedPacket U hU φ ((U s : H →L[ℂ] H) ξ)) := by
  have he := congrArg (fun A : H →L[ℂ] RegularCoreHilbert H =>
    A ((U s : H →L[ℂ] H) ξ)) (regularTranslation_gaugedPacket U hU s φ)
  have hu : (star (U s) : H →L[ℂ] H) ((U s : H →L[ℂ] H) ξ) = ξ :=
    congrArg (fun A : H →L[ℂ] H => A ξ)
      (Unitary.star_mul_self_of_mem (U s).property)
  change _ = regularGaugedPacket U hU (regularTranslateApply s.toAdd φ)
    ((star (U s) : H →L[ℂ] H) ((U s : H →L[ℂ] H) ξ)) at he
  rw [hu] at he
  exact he.symm

/-- Translation-invariant operators have covariant original-space coefficients. -/
theorem regularPacketCoefficient_translate
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (s : Multiplicative ℝ)
    (hT : Commute T (regularRightTranslation (H := H) s :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    (φ ψ : Lp ℂ 2 (volume : Measure ℝ)) :
    regularPacketCoefficient U hU T (regularTranslateApply s.toAdd φ)
        (regularTranslateApply s.toAdd ψ) =
      unitaryConj (star (U s)) (regularPacketCoefficient U hU T φ ψ) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_left ℂ
  intro η
  rw [inner_regularPacketCoefficient, regularGaugedPacket_translate,
    regularGaugedPacket_translate]
  have ht := congrArg (fun A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H =>
    A (regularGaugedPacket U hU ψ ((U s : H →L[ℂ] H) ξ))) hT.eq
  change T ((regularRightTranslation (H := H) s :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularGaugedPacket U hU ψ ((U s : H →L[ℂ] H) ξ))) =
    (regularRightTranslation (H := H) s :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (T (regularGaugedPacket U hU ψ ((U s : H →L[ℂ] H) ξ))) at ht
  rw [ht, Unitary.inner_map_map]
  rw [← inner_regularPacketCoefficient]
  simp only [unitaryConj, Unitary.coe_star, star_star, mul_apply_eq_comp]
  change inner ℂ ((U s : H →L[ℂ] H) η)
      (regularPacketCoefficient U hU T φ ψ ((U s : H →L[ℂ] H) ξ)) =
    inner ℂ η ((star (U s) : H →L[ℂ] H)
      (regularPacketCoefficient U hU T φ ψ ((U s : H →L[ℂ] H) ξ)))
  exact (ContinuousLinearMap.adjoint_inner_right (U s : H →L[ℂ] H) η _).symm

/-- A bounded map is determined by its values on all gauged scalar packets. -/
theorem regularGaugedPacket_ext
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {A B : RegularCoreHilbert H →L[ℂ] F}
    (h : ∀ φ ξ, A (regularGaugedPacket U hU φ ξ) =
      B (regularGaugedPacket U hU φ ξ)) : A = B := by
  let D : RegularCoreHilbert H →L[ℂ] F :=
    (A - B).comp (star (regularGauge U hU) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
  have hD (φ : Lp ℂ 2 (volume : Measure ℝ)) (ξ : H) :
      D (regularTensorVector φ ξ) = 0 := by
    change A (regularGaugedPacket U hU φ ξ) -
      B (regularGaugedPacket U hU φ ξ) = 0
    exact sub_eq_zero.mpr (h φ ξ)
  have hr : (⨆ i : ℕ, LinearMap.range
      (regularBasisSummand (H := H) regularScalarBasis i).toLinearMap) ≤ D.ker := by
    apply iSup_le
    intro i y hy
    obtain ⟨ξ, rfl⟩ := hy
    exact hD (regularScalarBasis i) ξ
  have hc := Submodule.topologicalClosure_minimal _ hr D.isClosed_ker
  have hzero (y : RegularCoreHilbert H) : D y = 0 :=
    hc (regularBasisSummand_total (H := H) regularScalarBasis (Submodule.mem_top))
  apply ContinuousLinearMap.ext
  intro y
  have hz := hzero ((regularGauge U hU :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) y)
  have hu : (star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      ((regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) y) = y :=
    congrArg (fun Q : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => Q y)
      (Unitary.star_mul_self_of_mem (regularGauge U hU).property)
  change A ((star (regularGauge U hU) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      ((regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) y)) -
    B ((star (regularGauge U hU) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      ((regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) y)) = 0 at hz
  rw [hu] at hz
  exact sub_eq_zero.mp hz

/-- Equality of every packet coefficient implies equality of the operators. -/
theorem regularPacketCoefficient_faithful
    {T S : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (h : ∀ φ ψ, regularPacketCoefficient U hU T φ ψ =
      regularPacketCoefficient U hU S φ ψ) : T = S := by
  have ha (φ : Lp ℂ 2 (volume : Measure ℝ)) :
      (regularGaugedPacket U hU φ).adjoint.comp T =
        (regularGaugedPacket U hU φ).adjoint.comp S := by
    apply regularGaugedPacket_ext U hU
    intro ψ ξ
    exact congrArg (fun A : H →L[ℂ] H => A ξ) (h φ ψ)
  have hadj : T.adjoint = S.adjoint := by
    apply regularGaugedPacket_ext U hU
    intro φ ξ
    have he := congrArg ContinuousLinearMap.adjoint (ha φ)
    simp only [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint] at he
    exact congrArg (fun A : H →L[ℂ] RegularCoreHilbert H => A ξ) he
  simpa only [ContinuousLinearMap.adjoint_adjoint] using
    congrArg ContinuousLinearMap.adjoint hadj

end

end KadisonKastler

end OAI

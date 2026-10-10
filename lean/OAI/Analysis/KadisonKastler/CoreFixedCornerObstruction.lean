import OAI.Analysis.KadisonKastler.CoreCornerCommutation
import OAI.Analysis.KadisonKastler.CoreFrequencyCovariance
import OAI.Analysis.KadisonKastler.RegularActionPackets

namespace OAI

/-! # A pointwise fixed nonzero corner prevents factoriality of the core -/

namespace KadisonKastler

open MeasureTheory Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regularConstant_frequencyWindow_ne_zero (p : H →L[ℂ] H) (hp : p ≠ 0) :
    regularConstantHom volume p * regularFrequencyWindow 0 1 ≠ 0 := by
  intro hz
  apply hp
  apply ContinuousLinearMap.ext
  intro x
  have hh := congrArg (fun T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H =>
    T (unitFrequencyVector x)) hz
  change regularConstantHom volume p (regularFrequencyWindow 0 1 (unitFrequencyVector x)) = 0 at hh
  rw [unitFrequencyVector_fixed] at hh
  change regularConstantHom volume p (regularFrequencyPacket unitFrequencyScalar x) = 0 at hh
  rw [regularConstantHom_frequencyPacket] at hh
  have hn := congrArg norm hh
  rw [norm_zero, norm_regularFrequencyPacket, norm_unitFrequencyScalar, one_mul] at hn
  exact norm_eq_zero.mp hn

theorem regularConstant_frequencyWindow_ne_self (p : H →L[ℂ] H) (hp : p ≠ 0) :
    regularConstantHom volume p * regularFrequencyWindow 0 1 ≠ regularConstantHom volume p := by
  intro he
  let P : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H := regularConstantHom volume p
  let Q := regularCharacterUnitary (H := H) (2 * Real.pi * 1)
  have hP : unitaryConj Q P = P := by
    exact (commute_unitary_iff_star_right_conjugate Q.property).mp
      (regularCharacter_commute_constant _ _)
  have hh := congrArg (Unitary.conjStarAlgAut ℂ (RegularCoreHilbert H →L[ℂ]
    RegularCoreHilbert H) Q) he
  rw [map_mul] at hh
  change unitaryConj Q P * unitaryConj Q (regularFrequencyWindow 0 1) = unitaryConj Q P at hh
  rw [hP, regularFrequencyWindow_character_conj] at hh
  have he' : P * regularFrequencyWindow 1 2 = P := by
    simpa only [zero_add, show (1 : ℝ) + 1 = 2 by norm_num] using hh
  have hzero := regularFrequencyWindow_mul_eq_zero_of_disjoint (H := H) 0 1 1 2
    (Set.disjoint_left.mpr (by intro x hx hy; exact (not_lt_of_ge hx.2) hy.1))
  have hz : P = 0 := by
    calc
      P = P * regularFrequencyWindow 1 2 := he'.symm
      _ = (P * regularFrequencyWindow 0 1) * regularFrequencyWindow 1 2 := by rw [he]
      _ = 0 := by rw [mul_assoc, hzero, mul_zero]
  apply hp
  apply real_regularConstantHom_injective
  exact hz.trans (map_zero _).symm

theorem regularCore_not_factor_of_fixed_corner
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (M : VonNeumannAlgebra H) (hn : ∀ s a, a ∈ M → unitaryConj (U s) a ∈ M)
    (p : AlgebraProjection M) (hp0 : p.val ≠ 0)
    (hfix : ∀ t a, a ∈ M → unitaryConj (U t) (p.val.val * a * p.val.val) =
      p.val.val * a * p.val.val) : ¬ ScalarCenter (regularCoreAlgebra U hU M) := by
  have hp : ∀ t, unitaryConj (U t) p.val.val = p.val.val := by
    intro t
    have h := hfix t 1 M.one_mem
    simpa only [mul_one, show p.val.val * p.val.val = p.val.val from
      congrArg Subtype.val p.property.isIdempotentElem.eq] using h
  let R := regularCoreAlgebra U hU M
  let P : Algebra R := ⟨regularCoreEmbedding U hU p.val.val,
    regularCoreEmbedding_mem_core U hU M p.val.property⟩
  let W : Algebra R := ⟨regularFrequencyWindow 0 1, regularFrequencyWindow_mem_core U hU M 0 1⟩
  have hP : IsStarProjection P := by
    constructor
    · apply Subtype.ext
      exact (p.property.map M.toStarSubalgebra.subtype |>.map (regularCoreEmbedding U hU)).isIdempotentElem.eq
    · apply Subtype.ext
      exact (p.property.map M.toStarSubalgebra.subtype |>.map (regularCoreEmbedding U hU)).isSelfAdjoint.star_eq
  have hW : IsStarProjection W := by
    constructor
    · apply Subtype.ext
      exact (regularFrequencyWindow_isStarProjection (H := H) 0 1).isIdempotentElem.eq
    · apply Subtype.ext
      exact (regularFrequencyWindow_isStarProjection (H := H) 0 1).isSelfAdjoint.star_eq
  have hPW : Commute P W := by
    apply Subtype.ext
    change Commute (regularCoreEmbedding U hU p.val.val) (regularFrequencyWindow 0 1)
    rw [regularCoreEmbedding_eq_constant_of_fixed U hU _ hp]
    exact regularFrequencyWindow_commute_of_translations _
      (regularConstant_commute_translation _) 0 1
  let p' : AlgebraProjection R := ⟨P, hP⟩
  let q : AlgebraProjection R := ⟨P * W, hP.mul hW hPW⟩
  have hqp : q ≤ p' := by
    change P * (P * W) = P * W
    rw [← mul_assoc, hP.isIdempotentElem.eq]
  intro hf
  have hc : ∀ a : Algebra R, q.val * (p'.val * a * p'.val) =
      (p'.val * a * p'.val) * q.val := by
    intro a
    have hS : Commute (P * a * P) W := by
      apply Subtype.ext
      exact (regularFrequencyWindow_commute_of_translations _
        (regularCore_fixed_corner_commute_translations U hU M hn p hfix a.val a.property) 0 1).eq
    change (P * W) * (P * a * P) = (P * a * P) * (P * W)
    calc
      _ = P * ((P * a * P) * W) := by rw [mul_assoc, hS.symm.eq]
      _ = (P * a * P) * W := by simp only [← mul_assoc, hP.isIdempotentElem.eq]
      _ = _ := by
        rw [← mul_assoc (P * a * P) P W, mul_assoc (P * a) P P,
          hP.isIdempotentElem.eq]
  rcases factor_corner_central_projection hf p' q hqp hc with hz | he
  · apply regularConstant_frequencyWindow_ne_zero p.val.val
      (fun h => hp0 (Subtype.ext h))
    have hh := congrArg Subtype.val hz
    change regularCoreEmbedding U hU p.val.val * regularFrequencyWindow 0 1 = 0 at hh
    rwa [regularCoreEmbedding_eq_constant_of_fixed U hU _ hp] at hh
  · apply regularConstant_frequencyWindow_ne_self p.val.val
      (fun h => hp0 (Subtype.ext h))
    have hh := congrArg (fun r : AlgebraProjection R => r.val.val) he
    change regularCoreEmbedding U hU p.val.val * regularFrequencyWindow 0 1 =
      regularCoreEmbedding U hU p.val.val at hh
    rwa [regularCoreEmbedding_eq_constant_of_fixed U hU _ hp] at hh

end

end KadisonKastler

end OAI

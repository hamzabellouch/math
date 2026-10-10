import OAI.Analysis.KadisonKastler.RegularCoreSemifinite

namespace OAI

/-! # A uniform tolerance for regular-core descent

The tolerance is obtained from the proved continuous error functions at zero.
It is chosen before the Hilbert space, the algebras, and the modular action.
Both the original-space gap and the regular tensor gap remain explicit.
-/

namespace KadisonKastler

open Filter Topology

noncomputable section

universe u

/-- One positive tolerance satisfies every numerical requirement of the
regular-core descent and the prescribed final displacement. -/
theorem exists_regularCore_tolerance {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧
      302 * t < 1 / 100 ∧
      302 * (302 * t) < 174 / 1000000000000000 ∧
      3 * 50948 * Real.sqrt (302 * (302 * t)) < 1 / 100000 ∧
      commonPositionError (302 * (302 * t)) < 1 / 4000000 ∧
      2 * matrixCornerError t < 1 / 1000 ∧
      t + 2 * matrixCornerError t < 1 ∧
      256 * matrixCornerError t < ε := by
  have h₁ : ∀ᶠ t : ℝ in 𝓝 0, 302 * t < 1 / 100 :=
    (continuous_const.mul continuous_id).continuousAt.eventually_lt_const (by norm_num)
  have h₂ : ∀ᶠ t : ℝ in 𝓝 0,
      302 * (302 * t) < 174 / 1000000000000000 :=
    (continuous_const.mul (continuous_const.mul continuous_id)).continuousAt.eventually_lt_const
      (by norm_num)
  have hc₃ : Continuous (fun t : ℝ =>
      3 * 50948 * Real.sqrt (302 * (302 * t))) := by fun_prop
  have h₃ : ∀ᶠ t : ℝ in 𝓝 0,
      3 * 50948 * Real.sqrt (302 * (302 * t)) < 1 / 100000 :=
    hc₃.continuousAt.eventually_lt_const (by norm_num)
  have hc₄ : Continuous (fun t : ℝ => commonPositionError (302 * (302 * t))) :=
    continuous_commonPositionError.comp
      (continuous_const.mul (continuous_const.mul continuous_id))
  have h₄ : ∀ᶠ t : ℝ in 𝓝 0,
      commonPositionError (302 * (302 * t)) < 1 / 4000000 :=
    hc₄.continuousAt.eventually_lt_const (by norm_num)
  have h₅ : ∀ᶠ t : ℝ in 𝓝 0, 2 * matrixCornerError t < 1 / 1000 :=
    (continuous_const.mul continuous_matrixCornerError).continuousAt.eventually_lt_const
      (by norm_num)
  have h₆ : ∀ᶠ t : ℝ in 𝓝 0, t + 2 * matrixCornerError t < 1 :=
    (continuous_id.add (continuous_const.mul continuous_matrixCornerError)).continuousAt.eventually_lt_const
      (by norm_num)
  have h₇ : ∀ᶠ t : ℝ in 𝓝 0, 256 * matrixCornerError t < ε :=
    (continuous_const.mul continuous_matrixCornerError).continuousAt.eventually_lt_const
      (by simpa using hε)
  have hall : ∀ᶠ t : ℝ in 𝓝 0,
      302 * t < 1 / 100 ∧
      302 * (302 * t) < 174 / 1000000000000000 ∧
      3 * 50948 * Real.sqrt (302 * (302 * t)) < 1 / 100000 ∧
      commonPositionError (302 * (302 * t)) < 1 / 4000000 ∧
      2 * matrixCornerError t < 1 / 1000 ∧
      t + 2 * matrixCornerError t < 1 ∧
      256 * matrixCornerError t < ε := by
    filter_upwards [h₁, h₂, h₃, h₄, h₅, h₆, h₇] with t ht₁ ht₂ ht₃ ht₄ ht₅ ht₆ ht₇
    exact ⟨ht₁, ht₂, ht₃, ht₄, ht₅, ht₆, ht₇⟩
  obtain ⟨d, hd, hball⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨d / 2, half_pos hd, hball ?_⟩
  simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hd)] using
    half_lt_self hd

local instance regularCoreModulusOrder {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (P : VonNeumannAlgebra H) :
    PartialOrder (Algebra P) := CStarAlgebra.spectralOrder _
local instance regularCoreModulusStarOrder {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (P : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra P) := CStarAlgebra.spectralOrderedRing _

/-- Uniform strong stability from a type II∞ source regular core. The
original and tensor gaps are both hypotheses; no ordinary-gap amplification
is asserted. -/
theorem uniform_regularCore_strong_stability
    (h : FiniteFactorPublishedInputs.{u})
    (hComm : PublishedRegularCommutant.{u})
    (hSpectral : PublishedRealSpectralCommutant.{u})
    (hDiagonal : PublishedRealDiagonalDecomposition.{u})
    (hCopies : PublishedProperInfiniteProjectionCopies.{u})
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
      (M N : VonNeumannAlgebra H),
      PublishedMultiplicationCorrection M →
      PublishedBlockCommutantApproximation (Algebra M) H →
      ∀ (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
        (hU : ∀ ξ, Continuous (fun s : ℝ =>
          (U (Multiplicative.ofAdd s) : H →L[ℂ] H) ξ)),
      (∀ s T, T ∈ M → unitaryConj (U s) T ∈ M) →
      (∀ s T, T ∈ N → unitaryConj (U s) T ∈ N) →
      TypeIIInfinityFactor (regularCoreAlgebra U hU M) →
      kkDistance (regularTensorAlgebra M) (regularTensorAlgebra N) < t →
      kkDistance M N < t → NearConjugacy M N ε := by
  obtain ⟨t, ht, hEmbed, hPosition, hStandard, hSpatial, hCP, hge, hεt⟩ :=
    exists_regularCore_tolerance hε
  refine ⟨t, ht, ?_⟩
  intro H _ _ _ _ M N hCorrection hCommutant U hU hM hN hCore hTensor hGap
  obtain ⟨v, hv, hnorm⟩ := regularCore_spatial_of_typeIIInfinity
    h hComm hSpectral hDiagonal M N hCorrection hCommutant U hU hM hN
    hCopies hCore ht hEmbed hPosition hTensor hGap hStandard hSpatial hCP hge
  exact ⟨v, hv, hnorm.trans_lt hεt⟩

end

end KadisonKastler

end OAI

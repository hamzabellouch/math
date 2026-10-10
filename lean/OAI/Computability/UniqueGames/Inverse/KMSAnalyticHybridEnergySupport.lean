import OAI.Computability.UniqueGames.Analysis.FiberEnergyLemmas
import OAI.Computability.UniqueGames.Inverse.KMSAffineRestrictionPresentationLemmas

namespace OAI

section

/-!
# Exact rank support of actual hybrid derivatives

The actual Hybrid selector loses exactly `dim A + codim B` in rank.
Consequently a pure rank component has derivative coefficients supported at
that exact remaining rank. Orders above the original rank give zero.
-/

noncomputable section

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixCharacters (linearTraceCharacter)
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix UniqueGamesTheorem.Appendix.Derivatives
open UniqueGamesTheorem.Inverse.KMSAnalytic

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 E] in
/-- The actual selector implies the exact rank loss for the actual
compressed Fourier frequency. -/
theorem hybrid_frequency_rank (A : Submodule F2 E) (B : Submodule F2 F)
    (S : F →ₗ[F2] E) (hS : LinearIdentities.Hybrid S A B) :
    Module.finrank F2 (Restriction.compressFrequency A B S).range + order A B =
      Module.finrank F2 S.range := by
  have hr := Level.LinearRank.hybrid_rank_loss A B S hS.1 hS.2
  have hc : Level.LinearRank.compress A B S = Restriction.compressFrequency A B S := rfl
  rw [hc] at hr
  change Module.finrank F2 (Restriction.compressFrequency A B S).range +
    (Module.finrank F2 A + Module.finrank F2 (F ⧸ B)) = Module.finrank F2 S.range
  omega

variable [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- A rank-`i` component has no derivative coefficient away from the
exact compressed rank plus the order. -/
theorem linearCoeff_hybridDerivative_rankComponent_eq_zero
    (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (T : E →ₗ[F2] F) (f : (E →ₗ[F2] F) → ℝ) (i : ℕ)
    (Z : B →ₗ[F2] (E ⧸ A))
    (hZ : Module.finrank F2 Z.range + order A B ≠ i) :
    linearCoeff (hybridDerivative A B T (rankComponent i f)) Z = 0 := by
  rw [linearCoeff_hybridDerivative]
  apply Finset.sum_eq_zero
  intro S _
  by_cases hS : LinearIdentities.Hybrid S A B ∧
      Restriction.compressFrequency A B S = Z
  · rw [ite_eq_left hS]
    have hr := hybrid_frequency_rank A B S hS.1
    rw [hS.2] at hr
    have hne : Module.finrank F2 S.range ≠ i := fun hs => hZ (hr.trans hs)
    simp only [rankComponent, coeff_component, ite_eq_right hne, zero_mul]
  · rw [ite_eq_right hS]

/-- If the order is larger than the selected rank, the actual derivative
vanishes, including all affine translates. -/
theorem hybridDerivative_rankComponent_eq_zero_of_lt_order
    (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (T : E →ₗ[F2] F) (f : (E →ₗ[F2] F) → ℝ) (i : ℕ)
    (hi : i < order A B) :
    hybridDerivative A B T (rankComponent i f) = 0 := by
  apply function_eq_of_linearCoeff_eq
  intro Z
  rw [linearCoeff_hybridDerivative_rankComponent_eq_zero A B T f i Z (by omega)]
  simp [linearCoeff]

/-- Parseval restricted to the exact rank-loss equality. -/
theorem hybridDerivative_rankComponent_energy_eq_support
    (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (T : E →ₗ[F2] F) (f : (E →ₗ[F2] F) → ℝ) (i : ℕ) :
    (𝔼 N, hybridDerivative A B T (rankComponent i f) N ^ 2) =
      ∑ Z : B →ₗ[F2] (E ⧸ A) with Module.finrank F2 Z.range + order A B = i,
        linearCoeff (hybridDerivative A B T (rankComponent i f)) Z ^ 2 := by
  rw [← linear_parseval, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro Z _
  by_cases hZ : Module.finrank F2 Z.range + order A B = i
  · rw [ite_eq_left hZ]
  · rw [ite_eq_right hZ, linearCoeff_hybridDerivative_rankComponent_eq_zero A B T f i Z hZ]
    norm_num

/-- Exact normalized energy is supported on compressed frequencies of rank
`i - order A B`. This also holds above the order cutoff since every
coefficient then vanishes. -/
theorem hybridDerivative_rankComponent_energy_eq_rank
    (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (T : E →ₗ[F2] F) (f : (E →ₗ[F2] F) → ℝ) (i : ℕ) :
    (𝔼 N, hybridDerivative A B T (rankComponent i f) N ^ 2) =
      ∑ Z : B →ₗ[F2] (E ⧸ A) with Module.finrank F2 Z.range = i - order A B,
        linearCoeff (hybridDerivative A B T (rankComponent i f)) Z ^ 2 := by
  rw [← linear_parseval, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro Z _
  by_cases hZ : Module.finrank F2 Z.range = i - order A B
  · rw [ite_eq_left hZ]
  · rw [ite_eq_right hZ,
      linearCoeff_hybridDerivative_rankComponent_eq_zero A B T f i Z (by omega)]
    norm_num

/-- The rank-restricted exact energy written in the actual compressed
Fourier fibers used by the analytic estimate. -/
theorem hybridDerivative_rankComponent_energy_eq_rank_fibers
    (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (T : E →ₗ[F2] F) (f : (E →ₗ[F2] F) → ℝ) (i : ℕ) :
    (𝔼 N, hybridDerivative A B T (rankComponent i f) N ^ 2) =
      ∑ Z : B →ₗ[F2] (E ⧸ A) with Module.finrank F2 Z.range = i - order A B,
        (∑ S : F →ₗ[F2] E,
          if LinearIdentities.Hybrid S A B ∧ Restriction.compressFrequency A B S = Z
          then linearCoeff (rankComponent i f) S * (linearTraceCharacter S T).re
          else 0) ^ 2 := by
  rw [hybridDerivative_rankComponent_energy_eq_rank]
  simp_rw [linearCoeff_hybridDerivative]

section Product

variable {A U B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup U] [Module F2 U]
  [AddCommGroup B] [Module F2 B] [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C]

omit [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C] in
/-- The explicit change from quotient frequencies to blocks preserves rank. -/
theorem productFrequencyEquiv_finrank
    (Z : (LinearMap.range (LinearMap.inl F2 B C)) →ₗ[F2]
      ((A × U) ⧸ LinearMap.range (LinearMap.inl F2 A U))) :
    Module.finrank F2 (productFrequencyEquiv Z).range = Module.finrank F2 Z.range := by
  change Module.finrank F2
    (((quotientRightEquiv (R := F2) (A := A) (U := U)).toLinearMap.comp Z).comp
      (leftRangeEquiv (R := F2) (B := B) (C := C)).toLinearMap).range = _
  rw [LinearEquiv.range_comp, LinearMap.range_comp]
  exact (quotientRightEquiv (R := F2) (A := A) (U := U)).finrank_map_eq Z.range

omit [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C] in
/-- The intrinsic restriction order agrees with the two fixed block dimensions. -/
theorem product_restriction_order :
    order (LinearMap.range (LinearMap.inl F2 A U))
      (LinearMap.range (LinearMap.inl F2 B C)) =
      Module.finrank F2 A + Module.finrank F2 C := by
  unfold order
  rw [← (leftRangeEquiv (R := F2) (B := A) (C := U)).finrank_eq,
    (quotientRightEquiv (R := F2) (A := B) (U := C)).finrank_eq]

variable [Finite A] [Finite U] [Finite B] [Finite C]
  [Fintype ((A × U) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (A × U))] [Fintype (B →ₗ[F2] U)]

/-- The actual derivative energy, restricted to the exact ordinary block rank. -/
theorem hybridDerivative_rankComponent_product_energy_eq_rank_fibers
    (T : (A × U) →ₗ[F2] (B × C))
    (f : ((A × U) →ₗ[F2] (B × C)) → ℝ) (i : ℕ) :
    (𝔼 N, hybridDerivative (LinearMap.range (LinearMap.inl F2 A U))
      (LinearMap.range (LinearMap.inl F2 B C)) T (rankComponent i f) N ^ 2) =
      ∑ Z : B →ₗ[F2] U with
          Module.finrank F2 Z.range = i - (Module.finrank F2 A + Module.finrank F2 C),
        (∑ S : (B × C) →ₗ[F2] (A × U),
          if LinearIdentities.Hybrid S (LinearMap.range (LinearMap.inl F2 A U))
              (LinearMap.range (LinearMap.inl F2 B C)) ∧
              (LinearMap.snd F2 A U).comp (S.comp (LinearMap.inl F2 B C)) = Z
          then linearCoeff (rankComponent i f) S * (linearTraceCharacter S T).re
          else 0) ^ 2 := by
  let : Fintype ((LinearMap.range (LinearMap.inl F2 B C)) →ₗ[F2]
      ((A × U) ⧸ LinearMap.range (LinearMap.inl F2 A U))) :=
    Fintype.ofEquiv (B →ₗ[F2] U) productFrequencyEquiv.symm
  rw [hybridDerivative_rankComponent_energy_eq_rank_fibers,
    product_restriction_order, Finset.sum_filter, Finset.sum_filter]
  apply Fintype.sum_equiv productFrequencyEquiv
  intro Z
  rw [productFrequencyEquiv_finrank]
  simp_rw [compressFrequency_eq_iff_product]

end Product

end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end

end OAI

import Mathlib
import OAI.Computability.DirectedFeedback.Games.CoordinateTransport

namespace OAI

noncomputable section
namespace DFVSGames.Appendix.Derivatives
open scoped BigOperators
open DFVSGames.Fourier.MatrixCharacters DFVSGames.Fourier.MatrixFourier
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

def spectralProjector (P : (F →ₗ[F2] E) → Prop) (f : (E →ₗ[F2] F) → ℝ) :
    (E →ₗ[F2] F) → ℝ :=
  ∑ Y with P Y, linearCoeff f Y • (fun X => (linearTraceCharacter Y X).re)

theorem linearCoeff_spectralProjector (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) (Y : F →ₗ[F2] E) :
    linearCoeff (spectralProjector P f) Y = if P Y then linearCoeff f Y else 0 := by
  classical
  unfold spectralProjector
  rw [linearCoeff_sum]
  simp only [linearCoeff_smul, linearCoeff_character, mul_ite, mul_one, mul_zero]
  simp

theorem spectralProjector_energy (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, spectralProjector P f X ^ 2) = ∑ Y with P Y, linearCoeff f Y ^ 2 := by
  classical
  rw [← linear_parseval, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro Y _
  rw [linearCoeff_spectralProjector]
  split_ifs <;> simp

theorem spectralProjector_energy_le (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, spectralProjector P f X ^ 2) ≤ 𝔼 X, f X ^ 2 := by
  classical
  rw [spectralProjector_energy, ← linear_parseval]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun Y _ _ => sq_nonneg _)

theorem function_eq_of_linearCoeff_eq {f g : (E →ₗ[F2] F) → ℝ}
    (h : ∀ Y, linearCoeff f Y = linearCoeff g Y) : f = g := by
  funext M
  rw [← linear_fourier_inversion f M, ← linear_fourier_inversion g M]
  apply Finset.sum_congr rfl
  intro Y _
  rw [h Y]

theorem spectralProjector_comp (P Q : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) :
    spectralProjector P (spectralProjector Q f) =
      spectralProjector (fun Y => P Y ∧ Q Y) f := by
  classical
  apply function_eq_of_linearCoeff_eq
  intro Y
  simp only [linearCoeff_spectralProjector]
  by_cases hP : P Y <;> by_cases hQ : Q Y <;> simp [hP, hQ]

def hybridProjector (A : Submodule F2 E) (B : Submodule F2 F)
    (f : (E →ₗ[F2] F) → ℝ) : (E →ₗ[F2] F) → ℝ :=
  spectralProjector (fun Y => LinearIdentities.Hybrid Y A B) f

def hybridDerivative (A : Submodule F2 E) (B : Submodule F2 F)
    (T : E →ₗ[F2] F) (f : (E →ₗ[F2] F) → ℝ) :
    DFVSGames.Fourier.MatrixRestrictions.Parameter A B → ℝ :=
  DFVSGames.Fourier.MatrixRestrictions.restrict (hybridProjector A B f) A B T

def rankProjector (X : F →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ) :
    (E →ₗ[F2] F) → ℝ :=
  spectralProjector (fun Y => RankAdditivity.RankBelow X Y) f

def mapDerivative (X : F →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ) :
    DFVSGames.Fourier.MatrixRestrictions.Parameter X.range X.ker → ℝ :=
  DFVSGames.Fourier.MatrixRestrictions.restrict (rankProjector X f) X.range X.ker 0

theorem rankProjector_energy (X : F →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 M, rankProjector X f M ^ 2) =
      ∑ Y, if RankAdditivity.RankBelow X Y then linearCoeff f Y ^ 2 else 0 := by
  classical
  unfold rankProjector
  rw [spectralProjector_energy, Finset.sum_filter]

def selectorMultiplicity {I : Type*} [Fintype I]
    (P : I → (F →ₗ[F2] E) → Prop) (Y : F →ₗ[F2] E) : ℕ :=
  (Finset.univ.filter (fun i : I => P i Y)).card

theorem selector_energy_sum {I : Type*} [Fintype I]
    (P : I → (F →ₗ[F2] E) → Prop) (f : (E →ₗ[F2] F) → ℝ) :
    (∑ i : I, 𝔼 X, spectralProjector (P i) f X ^ 2) =
      ∑ Y : F →ₗ[F2] E, (selectorMultiplicity P Y : ℝ) * linearCoeff f Y ^ 2 := by
  classical
  simp_rw [spectralProjector_energy, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Y _
  calc
    (∑ i : I, if P i Y then linearCoeff f Y ^ 2 else 0) =
        ∑ i : I with P i Y, linearCoeff f Y ^ 2 := by rw [Finset.sum_filter]
    _ = _ := by simp [selectorMultiplicity]

theorem selector_energy_sum_le {I : Type*} [Fintype I]
    (P : I → (F →ₗ[F2] E) → Prop) (f : (E →ₗ[F2] F) → ℝ) (M : ℝ)
    (hcount : ∀ Y : F →ₗ[F2] E, linearCoeff f Y ≠ 0 →
      (selectorMultiplicity P Y : ℝ) ≤ M) :
    (∑ i : I, 𝔼 X, spectralProjector (P i) f X ^ 2) ≤ M * (𝔼 X, f X ^ 2) := by
  classical
  rw [selector_energy_sum, ← linear_parseval, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro Y _
  by_cases hY : linearCoeff f Y = 0
  · simp [hY]
  · exact mul_le_mul_of_nonneg_right (hcount Y hY) (sq_nonneg _)

variable [Finite E] [Finite F]

theorem linearCoeff_mapDerivative (X : F →ₗ[F2] E)
    [Fintype (X.ker →ₗ[F2] (E ⧸ X.range))]
    (f : (E →ₗ[F2] F) → ℝ) (Z : X.ker →ₗ[F2] (E ⧸ X.range)) :
    linearCoeff (mapDerivative X f) Z =
      ∑ Y : F →ₗ[F2] E,
        if RankAdditivity.RankBelow X Y ∧
            Restriction.compressFrequency X.range X.ker Y = Z then linearCoeff f Y else 0 := by
  classical
  unfold mapDerivative
  rw [Restriction.linear_coefficient_merging]
  apply Finset.sum_congr rfl
  intro Y _
  simp only [rankProjector, linearCoeff_spectralProjector]
  have hp : (linearTraceCharacter Y (0 : E →ₗ[F2] F)).re = 1 := by simp
  rw [hp]
  by_cases hR : RankAdditivity.RankBelow X Y <;>
    by_cases hC : Restriction.compressFrequency X.range X.ker Y = Z <;> simp [hR, hC]

theorem mapDerivative_energy_eq_coefficients (X : F →ₗ[F2] E)
    [Fintype (X.ker →ₗ[F2] (E ⧸ X.range))]
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 N, mapDerivative X f N ^ 2) =
      ∑ Z : X.ker →ₗ[F2] (E ⧸ X.range),
        (∑ Y : F →ₗ[F2] E, if RankAdditivity.RankBelow X Y ∧
          Restriction.compressFrequency X.range X.ker Y = Z then linearCoeff f Y else 0) ^ 2 := by
  rw [← linear_parseval]
  simp_rw [linearCoeff_mapDerivative]

theorem mapDerivative_energy_le (X : F →ₗ[F2] E)
    [Fintype (X.ker →ₗ[F2] (E ⧸ X.range))]
    (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hdegree : ∀ Y : F →ₗ[F2] E,
      d < Module.finrank F2 Y.range → linearCoeff f Y = 0) :
    (𝔼 N, mapDerivative X f N ^ 2) ≤
      (2 : ℝ) ^ (2 * Module.finrank F2 X.range * (d - Module.finrank F2 X.range)) *
        (𝔼 M, rankProjector X f M ^ 2) := by
  rw [mapDerivative_energy_eq_coefficients, rankProjector_energy]
  have hh := DerivativeEnergy.coefficient_energy X (linearCoeff f) d hdegree
  simp only [Restriction.compressFrequency, FullCompression.compression] at hh ⊢
  convert hh using 1
  congr 1

theorem mapDerivative_energy_eq_weighted_energy (X : F →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 N, mapDerivative X f N ^ 2) = WeightedFourthMoment.energy (linearCoeff f) X := by
  let := WeightedFourthMoment.compressedFintype X
  rw [mapDerivative_energy_eq_coefficients]
  unfold WeightedFourthMoment.energy
  simp only [Restriction.compressFrequency, FullCompression.compression]
  congr 1

theorem weighted_fourth_derivative_energy (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hdegree : ∀ Y : F →ₗ[F2] E,
      d < Module.finrank F2 Y.range → linearCoeff f Y = 0) :
    (∑ X : F →ₗ[F2] E, ((2 : ℝ)⁻¹) ^ (8 * d * Module.finrank F2 X.range) *
      (𝔼 N, mapDerivative X f N ^ 2) ^ 2) ≤ 2 * (𝔼 M, f M ^ 2) ^ 2 := by
  calc
    _ = ∑ X : F →ₗ[F2] E, ((2 : ℝ)⁻¹) ^ (8 * d * Module.finrank F2 X.range) *
        WeightedFourthMoment.energy (linearCoeff f) X ^ 2 := by
      apply Finset.sum_congr rfl
      intro X _
      rw [mapDerivative_energy_eq_weighted_energy]
    _ ≤ _ := by
      simpa only [linear_parseval] using
        WeightedFourthMoment.weighted_fourth_coefficient_energy (linearCoeff f) d hdegree

theorem spectralProjector_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (Q : (B →ₗ[F2] (E ⧸ A)) → Prop) (f : (E →ₗ[F2] F) → ℝ)
    (T : E →ₗ[F2] F) :
    spectralProjector Q (DFVSGames.Fourier.MatrixRestrictions.restrict f A B T) =
      DFVSGames.Fourier.MatrixRestrictions.restrict
        (spectralProjector (fun Y => Q (Restriction.compressFrequency A B Y)) f) A B T := by
  classical
  apply function_eq_of_linearCoeff_eq
  intro Z
  rw [linearCoeff_spectralProjector,
    Restriction.linear_coefficient_merging, Restriction.linear_coefficient_merging]
  by_cases hQ : Q Z
  · simp only [ite_eq_left hQ]
    apply Finset.sum_congr rfl
    intro Y _
    rw [linearCoeff_spectralProjector]
    by_cases hC : Restriction.compressFrequency A B Y = Z <;> simp [hC, hQ]
  · simp only [ite_eq_right hQ]
    symm
    apply Finset.sum_eq_zero
    intro Y _
    rw [linearCoeff_spectralProjector]
    by_cases hC : Restriction.compressFrequency A B Y = Z <;> simp [hC, hQ]

theorem spectralProjector_restriction_moment_average
    (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (Q : (B →ₗ[F2] (E ⧸ A)) → Prop) (f : (E →ₗ[F2] F) → ℝ)
    {N : Type*} [Fintype N] [Nonempty N]
    (θ : N → DFVSGames.Fourier.MatrixRestrictions.Parameter A B) (p : ℕ) :
    (𝔼 T, 𝔼 n, spectralProjector Q
      (DFVSGames.Fourier.MatrixRestrictions.restrict f A B T) (θ n) ^ p) =
      𝔼 M, spectralProjector (fun Y => Q (Restriction.compressFrequency A B Y)) f M ^ p := by
  simp_rw [spectralProjector_restriction]
  exact Restriction.real_translation_average
    (fun n => DFVSGames.Fourier.MatrixRestrictions.embed A B (θ n))
    (fun M => spectralProjector (fun Y => Q (Restriction.compressFrequency A B Y)) f M ^ p)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem hybridDerivative_energy_average (A : Submodule F2 E) (B : Submodule F2 F)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 T, 𝔼 N, hybridDerivative A B T f N ^ 2) =
      𝔼 X, hybridProjector A B f X ^ 2 :=
  Restriction.real_translation_average (DFVSGames.Fourier.MatrixRestrictions.embed A B)
    (fun X => hybridProjector A B f X ^ 2)

def HybridIndex (d : ℕ) :=
  {p : Submodule F2 E × Submodule F2 F //
    DFVSGames.Fourier.MatrixRestrictions.order p.1 p.2 ≤ d}

noncomputable instance hybridIndexFintype (d : ℕ) :
    Fintype (HybridIndex (E := E) (F := F) d) := by
  letI : Finite (Submodule F2 E) :=
    Finite.of_injective (fun A : Submodule F2 E => (A : Set E)) SetLike.coe_injective
  letI : Finite (Submodule F2 F) :=
    Finite.of_injective (fun B : Submodule F2 F => (B : Set F)) SetLike.coe_injective
  unfold HybridIndex
  exact Fintype.ofFinite _

def hybridMomentSum (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ s : HybridIndex (E := E) (F := F) d,
    𝔼 T, (𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2) ^ 2

def hybridSelectorEnergy (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ s : HybridIndex (E := E) (F := F) d,
    𝔼 X, hybridProjector s.val.1 s.val.2 f X ^ 2

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem hybridMomentSum_le_of_uniform_energy (d : ℕ)
    (f : (E →ₗ[F2] F) → ℝ) (ζ : ℝ)
    (hζ : ∀ (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F),
      DFVSGames.Fourier.MatrixRestrictions.order A B ≤ d →
        (𝔼 N, hybridDerivative A B T f N ^ 2) ≤ ζ) :
    hybridMomentSum d f ≤ ζ * hybridSelectorEnergy d f := by
  classical
  unfold hybridMomentSum hybridSelectorEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  calc
    (𝔼 T, (𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2) ^ 2) ≤
        𝔼 T, ζ * (𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2) := by
      apply Finset.expect_le_expect
      intro T _
      have hn : 0 ≤ 𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2 :=
        Finset.expect_nonneg (fun N _ => sq_nonneg _)
      simpa only [pow_two] using
        mul_le_mul_of_nonneg_right (hζ s.val.1 s.val.2 T s.property) hn
    _ = ζ * (𝔼 T, 𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2) :=
      (Finset.mul_expect _ _ _).symm
    _ = ζ * (𝔼 X, hybridProjector s.val.1 s.val.2 f X ^ 2) := by
      rw [hybridDerivative_energy_average]

end DFVSGames.Appendix.Derivatives
end

noncomputable section

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters DFVSGames.Fourier.MatrixFourier
open DFVSGames.Appendix DFVSGames.Appendix.Derivatives

section General

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem linearCoeff_hybridDerivative
    (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (T : E →ₗ[F2] F) (f : (E →ₗ[F2] F) → ℝ)
    (Z : B →ₗ[F2] (E ⧸ A)) :
    linearCoeff (hybridDerivative A B T f) Z =
      ∑ S : F →ₗ[F2] E,
        if LinearIdentities.Hybrid S A B ∧ Restriction.compressFrequency A B S = Z
        then linearCoeff f S * (linearTraceCharacter S T).re else 0 := by
  unfold hybridDerivative
  rw [Restriction.linear_coefficient_merging]
  apply Finset.sum_congr rfl
  intro S _
  simp only [hybridProjector, linearCoeff_spectralProjector]
  by_cases hH : LinearIdentities.Hybrid S A B <;>
    by_cases hC : Restriction.compressFrequency A B S = Z <;> simp [hH, hC]

theorem hybridDerivative_energy_eq_coefficients
    (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (T : E →ₗ[F2] F) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 N, hybridDerivative A B T f N ^ 2) =
      ∑ Z : B →ₗ[F2] (E ⧸ A),
        (∑ S : F →ₗ[F2] E,
          if LinearIdentities.Hybrid S A B ∧ Restriction.compressFrequency A B S = Z
          then linearCoeff f S * (linearTraceCharacter S T).re else 0) ^ 2 := by
  rw [← linear_parseval]
  simp_rw [linearCoeff_hybridDerivative]

end General

section ProductEquivalences

variable {R A U B C : Type*} [Ring R]
  [AddCommGroup A] [Module R A] [AddCommGroup U] [Module R U]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]

def leftRangeEquiv : B ≃ₗ[R] LinearMap.range (LinearMap.inl R B C) where
  toFun b := ⟨(b, 0), ⟨b, rfl⟩⟩
  invFun x := x.val.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨x, hx⟩
    obtain ⟨b, rfl⟩ := hx
    rfl
  map_add' _ _ := by apply Subtype.ext; simp
  map_smul' _ _ := by apply Subtype.ext; simp

@[simp] theorem leftRangeEquiv_coe (b : B) :
    (leftRangeEquiv (R := R) (C := C) b : B × C) = (b, 0) := rfl

def quotientRightMap :
    ((A × U) ⧸ LinearMap.range (LinearMap.inl R A U)) →ₗ[R] U :=
  (LinearMap.range (LinearMap.inl R A U)).liftQ (LinearMap.snd R A U) (by
    rintro x ⟨a, rfl⟩
    rfl)

@[simp] theorem quotientRightMap_mkQ (x : A × U) :
    quotientRightMap (R := R)
      ((LinearMap.range (LinearMap.inl R A U)).mkQ x) = x.2 := rfl

def quotientRightEquiv :
    ((A × U) ⧸ LinearMap.range (LinearMap.inl R A U)) ≃ₗ[R] U where
  toLinearMap := quotientRightMap
  invFun u := (LinearMap.range (LinearMap.inl R A U)).mkQ (0, u)
  left_inv := by
    intro q
    obtain ⟨⟨a, u⟩, rfl⟩ := (LinearMap.range (LinearMap.inl R A U)).mkQ_surjective q
    change (LinearMap.range (LinearMap.inl R A U)).mkQ (0, u) =
      (LinearMap.range (LinearMap.inl R A U)).mkQ (a, u)
    have hz : (LinearMap.range (LinearMap.inl R A U)).mkQ (a, 0) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨a, rfl⟩
    calc
      _ = (LinearMap.range (LinearMap.inl R A U)).mkQ (a, 0) +
          (LinearMap.range (LinearMap.inl R A U)).mkQ (0, u) := by rw [hz, zero_add]
      _ = (LinearMap.range (LinearMap.inl R A U)).mkQ ((a, 0) + (0, u)) :=
        (map_add _ _ _).symm
      _ = _ := by simp
  right_inv _ := rfl

@[simp] theorem quotientRightEquiv_mkQ (x : A × U) :
    quotientRightEquiv (R := R)
      ((LinearMap.range (LinearMap.inl R A U)).mkQ x) = x.2 := rfl

def productFrequencyEquiv :
    ((LinearMap.range (LinearMap.inl R B C)) →ₗ[R]
      ((A × U) ⧸ LinearMap.range (LinearMap.inl R A U))) ≃ (B →ₗ[R] U) where
  toFun Z := (quotientRightEquiv (R := R) (A := A) (U := U)).toLinearMap.comp
    (Z.comp (leftRangeEquiv (R := R) (B := B) (C := C)).toLinearMap)
  invFun Z := (quotientRightEquiv (R := R) (A := A) (U := U)).symm.toLinearMap.comp
    (Z.comp (leftRangeEquiv (R := R) (B := B) (C := C)).symm.toLinearMap)
  left_inv Z := by
    apply LinearMap.ext
    intro b
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  right_inv Z := by
    apply LinearMap.ext
    intro b
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]

end ProductEquivalences

variable {A U B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup U] [Module F2 U]
  [AddCommGroup B] [Module F2 B] [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C]

omit [FiniteDimensional F2 A] [FiniteDimensional F2 U] [FiniteDimensional F2 B] [FiniteDimensional F2 C] in

@[simp] theorem productFrequencyEquiv_compressFrequency
    (S : (B × C) →ₗ[F2] (A × U)) :
    productFrequencyEquiv (Restriction.compressFrequency
      (LinearMap.range (LinearMap.inl F2 A U))
      (LinearMap.range (LinearMap.inl F2 B C)) S) =
      (LinearMap.snd F2 A U).comp (S.comp (LinearMap.inl F2 B C)) := by
  apply LinearMap.ext
  intro b
  rfl

omit [FiniteDimensional F2 A] [FiniteDimensional F2 U] [FiniteDimensional F2 B] [FiniteDimensional F2 C] in

theorem compressFrequency_eq_iff_product
    (S : (B × C) →ₗ[F2] (A × U))
    (Z : (LinearMap.range (LinearMap.inl F2 B C)) →ₗ[F2]
      ((A × U) ⧸ LinearMap.range (LinearMap.inl F2 A U))) :
    Restriction.compressFrequency (LinearMap.range (LinearMap.inl F2 A U))
      (LinearMap.range (LinearMap.inl F2 B C)) S = Z ↔
    (LinearMap.snd F2 A U).comp (S.comp (LinearMap.inl F2 B C)) =
      productFrequencyEquiv Z := by
  constructor
  · intro h
    rw [← productFrequencyEquiv_compressFrequency S, h]
  · intro h
    apply productFrequencyEquiv.injective
    rw [productFrequencyEquiv_compressFrequency, h]

variable [Finite A] [Finite U] [Finite B] [Finite C]
  [Fintype ((A × U) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (A × U))] [Fintype (B →ₗ[F2] U)]

theorem hybridDerivative_product_energy_eq_coefficients
    (T : (A × U) →ₗ[F2] (B × C))
    (f : ((A × U) →ₗ[F2] (B × C)) → ℝ) :
    (𝔼 N, hybridDerivative (LinearMap.range (LinearMap.inl F2 A U))
      (LinearMap.range (LinearMap.inl F2 B C)) T f N ^ 2) =
      ∑ Z : B →ₗ[F2] U,
        (∑ S : (B × C) →ₗ[F2] (A × U),
          if LinearIdentities.Hybrid S (LinearMap.range (LinearMap.inl F2 A U))
              (LinearMap.range (LinearMap.inl F2 B C)) ∧
              (LinearMap.snd F2 A U).comp (S.comp (LinearMap.inl F2 B C)) = Z
          then linearCoeff f S * (linearTraceCharacter S T).re else 0) ^ 2 := by
  let : Fintype ((LinearMap.range (LinearMap.inl F2 B C)) →ₗ[F2]
      ((A × U) ⧸ LinearMap.range (LinearMap.inl F2 A U))) :=
    Fintype.ofEquiv (B →ₗ[F2] U) productFrequencyEquiv.symm
  rw [hybridDerivative_energy_eq_coefficients]
  apply Fintype.sum_equiv productFrequencyEquiv
  intro Z
  simp_rw [compressFrequency_eq_iff_product]

end DFVSGames.Inverse.KMSAnalyticHybridEnergy

end

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixCharacters (linearTraceCharacter)
open DFVSGames.Fourier.MatrixFourier

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

def synthesis (a : (F →ₗ[F2] E) → ℝ) : (E →ₗ[F2] F) → ℝ :=
  ∑ S, a S • (fun X => (linearTraceCharacter S X).re)

@[simp] theorem coeff_synthesis (a : (F →ₗ[F2] E) → ℝ) (T : F →ₗ[F2] E) :
    linearCoeff (synthesis a) T = a T := by
  unfold synthesis
  rw [linearCoeff_sum]
  simp only [linearCoeff_smul, linearCoeff_character, mul_ite, mul_one, mul_zero]
  simp

theorem synthesis_coeff (f : (E →ₗ[F2] F) → ℝ) : synthesis (linearCoeff f) = f := by
  funext X
  simpa only [synthesis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
    linear_fourier_inversion f X

theorem eq_of_coeff_eq {f g : (E →ₗ[F2] F) → ℝ}
    (h : ∀ T, linearCoeff f T = linearCoeff g T) : f = g := by
  rw [← synthesis_coeff f, ← synthesis_coeff g]
  exact congrArg synthesis (funext h)

theorem synthesis_inner (a b : (F →ₗ[F2] E) → ℝ) :
    (𝔼 X, synthesis a X * synthesis b X) = ∑ T, a T * b T := by
  rw [← linear_parseval_inner]
  simp

theorem synthesis_energy (a : (F →ₗ[F2] E) → ℝ) :
    (𝔼 X, synthesis a X ^ 2) = ∑ T, a T ^ 2 := by
  rw [← linear_parseval]
  simp

def component (P : (F →ₗ[F2] E) → Prop) (f : (E →ₗ[F2] F) → ℝ) :
    (E →ₗ[F2] F) → ℝ :=
  synthesis fun T => if P T then linearCoeff f T else 0

@[simp] theorem coeff_component (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) (T : F →ₗ[F2] E) :
    linearCoeff (component P f) T = if P T then linearCoeff f T else 0 := by
  exact coeff_synthesis _ _

theorem component_energy (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, component P f X ^ 2) = ∑ T with P T, linearCoeff f T ^ 2 := by
  rw [component, synthesis_energy, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  split_ifs <;> simp

theorem component_energy_le (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, component P f X ^ 2) ≤ 𝔼 X, f X ^ 2 := by
  rw [component_energy, ← linear_parseval]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun T _ _ => sq_nonneg _)

theorem component_inner_self (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, component P f X * f X) = 𝔼 X, component P f X ^ 2 := by
  rw [← linear_parseval_inner, component_energy, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  rw [coeff_component]
  split_ifs <;> simp [pow_two]

theorem component_comp (P Q : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) :
    component P (component Q f) = component (fun T => P T ∧ Q T) f := by
  apply eq_of_coeff_eq
  intro T
  simp only [coeff_component]
  by_cases hP : P T <;> by_cases hQ : Q T <;> simp [hP, hQ]

theorem component_orthogonal (P Q : (F →ₗ[F2] E) → Prop)
    (hPQ : ∀ T, ¬ (P T ∧ Q T)) (f g : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, component P f X * component Q g X) = 0 := by
  rw [← linear_parseval_inner]
  apply Finset.sum_eq_zero
  intro T _
  simp only [coeff_component]
  by_cases hP : P T
  · have hQ : ¬ Q T := fun hQ => hPQ T ⟨hP, hQ⟩
    simp [hP, hQ]
  · simp [hP]

def rankComponent (i : ℕ) (f : (E →ₗ[F2] F) → ℝ) : (E →ₗ[F2] F) → ℝ :=
  component (fun T => Module.finrank F2 T.range = i) f

theorem rankComponent_energy (i : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, rankComponent i f X ^ 2) =
      ∑ T with Module.finrank F2 T.range = i, linearCoeff f T ^ 2 := by
  unfold rankComponent
  rw [component_energy]
  apply Finset.sum_congr
  · ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · intro T _
    rfl

end
end DFVSGames.Inverse.KMSAnalytic

noncomputable section

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixCharacters (linearTraceCharacter)
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Fourier.MatrixRestrictions
open DFVSGames.Appendix DFVSGames.Appendix.Derivatives
open DFVSGames.Inverse.KMSAnalytic

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 E] in
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

variable {A U B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup U] [Module F2 U]
  [AddCommGroup B] [Module F2 B] [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C]

omit [FiniteDimensional F2 A] [FiniteDimensional F2 U] [FiniteDimensional F2 B] [FiniteDimensional F2 C] in

theorem productFrequencyEquiv_finrank
    (Z : (LinearMap.range (LinearMap.inl F2 B C)) →ₗ[F2]
      ((A × U) ⧸ LinearMap.range (LinearMap.inl F2 A U))) :
    Module.finrank F2 (productFrequencyEquiv Z).range = Module.finrank F2 Z.range := by
  change Module.finrank F2
    (((quotientRightEquiv (R := F2) (A := A) (U := U)).toLinearMap.comp Z).comp
      (leftRangeEquiv (R := F2) (B := B) (C := C)).toLinearMap).range = _
  rw [LinearEquiv.range_comp, LinearMap.range_comp]
  exact (quotientRightEquiv (R := F2) (A := A) (U := U)).finrank_map_eq Z.range

omit [FiniteDimensional F2 A] [FiniteDimensional F2 U] [FiniteDimensional F2 B] [FiniteDimensional F2 C] in

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

end DFVSGames.Inverse.KMSAnalyticHybridEnergy

end

end OAI

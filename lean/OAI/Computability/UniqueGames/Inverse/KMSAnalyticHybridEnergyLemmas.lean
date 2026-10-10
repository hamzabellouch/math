import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.Tactic.Positivity
import OAI.Computability.UniqueGames.Decoding.AdviceFibersLemmas
import OAI.Computability.UniqueGames.Inverse.KMSAnalyticHybridEnergyImageTransportCoreLemmas
import OAI.Computability.UniqueGames.Inverse.KMSAnalyticHybridEnergyImageTransportLemmas
import OAI.Computability.UniqueGames.Inverse.KMSBasisComparisonPseudorandomTupleMapLemmas
import OAI.Computability.UniqueGames.Inverse.KMSFourthMomentZoomInAlgebraLemmas
import OAI.Computability.UniqueGames.Inverse.KMSLowLevelLemmas
import OAI.Computability.UniqueGames.Inverse.RowErasureLemmas
import OAI.Computability.UniqueGames.Inverse.RowErasureMatrixLemmas

namespace OAI

section

/-! The actual arbitrary-subspace hybrid energy estimate. The proof changes
both ambient spaces to complement coordinates, invokes the proved image
decomposition, and obtains every mixed slice from the actual KMS mixed
restriction theorem. No derivative or moment estimate is assumed. -/

noncomputable section
namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix UniqueGamesTheorem.Appendix.Derivatives
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open KMSAnalytic KMSFourthMoment

universe u

attribute [local instance] mapFintype

section Product
variable {A U B C : Type u}
  [AddCommGroup A] [Module F2 A] [AddCommGroup U] [Module F2 U]
  [AddCommGroup B] [Module F2 B] [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C]
  [Fintype A] [Fintype U] [Fintype B] [Fintype C]

/-- Each image-adapted slice in the product proof is one of the actual
uniform mixed slices. The dimension equality exactly matches its weight. -/
theorem productMixedSliceBound_of_uniform (i : ℕ) (L : ℝ)
    (f : ((A × U) →ₗ[F2] (B × C)) → ℝ)
    (hMixed : UniformMixedBound i L f)
    (ho : Module.finrank F2 A + Module.finrank F2 C ≤ i)
    (T : (A × U) →ₗ[F2] (B × C)) : ProductMixedSliceBound i f T L := by
  intro W D hW hD κ hκ
  have hm := UniformMixedBound.pullback (imageAmbientEquiv (A := A) W D hD)
    (LinearEquiv.refl F2 (B × C)) f hMixed
  have hm' : UniformMixedBound i L (imagePullback W D hD f) := by
    exact hm
  have hr : Module.finrank F2 A + Module.finrank F2 (W × C) ≤ i := by
    rw [Module.finrank_prod, hW]
    omega
  have hπ : Function.Surjective (LinearMap.snd F2 W C) := by
    intro c
    exact ⟨(0, c), rfl⟩
  have hh := hm' A (W × C) C κ hκ (primalA (imageTranslate W D hD T))
    (LinearMap.snd F2 W C) hπ (LinearMap.snd F2 B C) hr
  have hdim : Module.finrank F2 (A × (W × D)) = Module.finrank F2 (A × U) :=
    (imageAmbientEquiv (A := A) W D hD).finrank_eq
  have hexp : (Module.finrank F2 (W × C) + Module.finrank F2 C) *
      Module.finrank F2 (A × (W × D)) =
      (2 * Module.finrank F2 C + (i - (Module.finrank F2 A + Module.finrank F2 C))) *
        Module.finrank F2 (A × U) := by
    rw [Module.finrank_prod, hW, hdim]
    congr 1
    omega
  rw [hexp] at hh
  apply (le_div_iff₀ (by positivity)).mpr
  convert hh using 1
  simp only [mul_comm]

end Product

section General
variable {E F : Type u}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype E] [Fintype F]

omit [FiniteDimensional F2 E] [Fintype E] in
theorem map_leftRange_complement (A U : Submodule F2 E) (h : IsCompl A U) :
    (LinearMap.range (LinearMap.inl F2 A U)).map
      (Submodule.prodEquivOfIsCompl A U h).toLinearMap = A := by
  rw [← LinearMap.range_comp]
  have hc : (Submodule.prodEquivOfIsCompl A U h).toLinearMap.comp
      (LinearMap.inl F2 A U) = A.subtype := by
    apply LinearMap.ext
    intro a
    change (a : E) + (0 : E) = (a : E)
    simp
  rw [hc, Submodule.range_subtype]

/-- The actual hybrid derivative is uniformly bounded whenever all actual
mixed slices are bounded. Both selector subspaces and every affine translate
are arbitrary. -/
theorem hybridDerivative_energy_le_of_uniform
    (i : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
    (hMixed : UniformMixedBound i L f) (hi : i ≤ Module.finrank F2 E)
    (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F) :
    (𝔼 N, hybridDerivative A B T (rankComponent i f) N ^ 2) ≤ L := by
  obtain ⟨U, hU⟩ := A.exists_isCompl
  obtain ⟨C, hC⟩ := B.exists_isCompl
  let a : (A × U) ≃ₗ[F2] E := Submodule.prodEquivOfIsCompl A U hU
  let b : (B × C) ≃ₗ[F2] F := Submodule.prodEquivOfIsCompl B C hC
  let f' : ((A × U) →ₗ[F2] (B × C)) → ℝ :=
    fun M => f (LinearEquiv.arrowCongr a b M)
  let T' : (A × U) →ₗ[F2] (B × C) := (LinearEquiv.arrowCongr a b).symm T
  have hf' : KMSBasisInvariant.IsBasisInvariant f' := basisInvariant_pullback a b f hf
  have hm' : UniformMixedBound i L f' := UniformMixedBound.pullback a b f hMixed
  have hi' : i ≤ Module.finrank F2 (A × U) := by rw [a.finrank_eq]; exact hi
  have hcoord : (𝔼 N, hybridDerivative
      (LinearMap.range (LinearMap.inl F2 A U))
      (LinearMap.range (LinearMap.inl F2 B C)) T' (rankComponent i f') N ^ 2) ≤ L := by
    by_cases ho : Module.finrank F2 A + Module.finrank F2 C ≤ i
    · exact product_hybrid_energy_le_of_mixed i f' hf' T' L hL hi'
        (productMixedSliceBound_of_uniform i L f' hm' ho T')
    · have hzero := hybridDerivative_rankComponent_eq_zero_of_lt_order
        (LinearMap.range (LinearMap.inl F2 A U))
        (LinearMap.range (LinearMap.inl F2 B C)) T' f' i
        (by rw [product_restriction_order]
            change i < Module.finrank F2 A + Module.finrank F2 C
            omega)
      simpa [hzero] using hL
  have he := hybridDerivative_rankComponent_energy_pullback a b f i
    (LinearMap.range (LinearMap.inl F2 A U))
    (LinearMap.range (LinearMap.inl F2 B C)) T'
  have hA : (LinearMap.range (LinearMap.inl F2 A U)).map a.toLinearMap = A :=
    map_leftRange_complement A U hU
  have hB : (LinearMap.range (LinearMap.inl F2 B C)).map b.toLinearMap = B :=
    map_leftRange_complement B C hC
  have hT : LinearEquiv.arrowCongr a b T' = T :=
    (LinearEquiv.arrowCongr a b).apply_symm_apply T
  rw [hA, hB, hT] at he
  exact he ▸ hcoord

/-- Genuine KMS hybrid energy bound from basis invariance and actual local
squared density. This is the analytic input to the permitted generic fourth
moment inequality; no hybrid estimate is included among its hypotheses. -/
theorem hybridDerivative_energy_bound
    (i : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
    (hd : AffineDensityBound i ε f) (hi : i ≤ Module.finrank F2 E)
    (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F) :
    (𝔼 N, hybridDerivative A B T (rankComponent i f) N ^ 2) ≤ mixedRankConstant i * ε :=
  hybridDerivative_energy_le_of_uniform i (mixedRankConstant i * ε)
    (mul_nonneg (mixedRankConstant_nonneg i) hε) f hf
    (uniformMixedBound_of_affineDensityBound i ε hε f hf hd) hi A B T

end General
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end

section

/-!
# The actual hybrid energy estimate at every rank

The established estimate applies within the ambient dimension. Above that
dimension the actual Fourier component, and hence its derivative energy,
is zero. No rank cutoff hypothesis remains in the resulting interface.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.Derivatives
open KMSAnalytic KMSFourthMoment

attribute [local instance] mapFintype

universe u

variable {E F : Type u}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype E] [Fintype F]

/-- The genuine hybrid derivative bound, including ranks above the ambient
dimension where the selected Fourier component vanishes. -/
theorem hybridDerivative_energy_bound_allRanks
    (i : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
    (hd : AffineDensityBound i ε f)
    (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F) :
    (𝔼 N, hybridDerivative A B T (rankComponent i f) N ^ 2) ≤ mixedRankConstant i * ε := by
  by_cases hi : i ≤ Module.finrank F2 E
  · exact hybridDerivative_energy_bound i ε hε f hf hd hi A B T
  · rw [hybridDerivative_rankComponent_energy_eq_zero_of_finrank_lt
      A B T f i (Nat.lt_of_not_ge hi)]
    exact mul_nonneg (mixedRankConstant_nonneg i) hε

end
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

section

/-! Explicit dimension-independent constants for the KMS mixed-energy
argument and the generic A5 aggregation. The eventual expansion theorem only
uses positivity and finiteness of these constants, so no rank cutoff exception
or comparison with another rank-level constant is needed. -/

namespace UniqueGamesTheorem.Inverse.KMSMomentConstants
noncomputable section
open KMSFourthMoment

/-- The constant after the genuine mixed-energy estimate and A5 aggregation. -/
def fourthMomentConstant (r : ℕ) : ℝ := 2 ^ (109 * r * r + 2 * r)

theorem fourthMomentConstant_pos (r : ℕ) : 0 < fourthMomentConstant r := by
  unfold fourthMomentConstant
  positivity

theorem fourthMomentConstant_nonneg (r : ℕ) : 0 ≤ fourthMomentConstant r :=
  (fourthMomentConstant_pos r).le

/-- The closed mixed estimate's literal constant has a quadratic exponent. -/
theorem mixedRankConstant_eq (r : ℕ) :
    mixedRankConstant r = (2 : ℝ) ^ (6 * r * r + 2 * r) := by
  unfold mixedRankConstant mixedStepFactor
  rw [← pow_mul, ← pow_add]
  congr 1
  ring

/-- Multiplying by the actual selector-count and A5 constant is exact. -/
theorem a5_mul_mixedRankConstant (r : ℕ) :
    (2 : ℝ) ^ (103 * r * r) * mixedRankConstant r = fourthMomentConstant r := by
  rw [mixedRankConstant_eq, ← pow_add]
  unfold fourthMomentConstant
  congr 1
  ring

theorem fourthMomentConstant_mono {i r : ℕ} (hi : i ≤ r) :
    fourthMomentConstant i ≤ fourthMomentConstant r := by
  unfold fourthMomentConstant
  apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
  exact Nat.add_le_add
    (Nat.mul_le_mul (Nat.mul_le_mul_left 109 hi) hi)
    (Nat.mul_le_mul_left 2 hi)

/-- The complete numerical closure, retaining the density and projection
energy factors in the order used by the expansion interface. -/
theorem a5_mixed_bound {i r : ℕ} (hi : i ≤ r) (ε η : ℝ)
    (hε : 0 ≤ ε) (hη : 0 ≤ η) :
    (2 : ℝ) ^ (103 * i * i) * (mixedRankConstant i * ε) * η ≤
      fourthMomentConstant r * η * ε := by
  calc
    _ = fourthMomentConstant i * (η * ε) := by
      rw [← a5_mul_mixedRankConstant]
      ring
    _ ≤ fourthMomentConstant r * (η * ε) :=
      mul_le_mul_of_nonneg_right (fourthMomentConstant_mono hi) (mul_nonneg hη hε)
    _ = _ := by ring

end
end UniqueGamesTheorem.Inverse.KMSMomentConstants

end

section

/-! The actual upper fourth-moment theorem for the full-rank lift of a
Grassmann set. Its hypotheses are literal tuple probabilities. The affine
sampling law, mixed estimate and hybrid derivative estimate are all discharged
by proved lemmas; there is no analytic estimate among the hypotheses. -/

namespace UniqueGamesTheorem.Inverse.KMSMomentTheorem
noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison KMSBasisComparisonPseudorandom
open KMSAnalytic KMSFourthMoment KMSMomentConstants

/-- The upper moment has a constant depending only on the cutoff. Its tuple
budget is 2r and its domain threshold is r, both fixed before the dimensions. -/
theorem lifted_fourth_moment_bound
    (r : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (ell : ℕ) (hell : r ≤ ell) (n : ℕ)
    (S : Finset (Vertex n ell)) (hS : TuplePseudorandom S (2 * r) ε)
    (i : ℕ) (hi : i ≤ r) :
    (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 4) ≤
      fourthMomentConstant r *
        (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 2) * ε := by
  have hf := liftedIndicator_basisInvariant S
  have hd : AffineDensityBound i ε (liftedIndicator S) :=
    AffineDensityBound.mono hi ε (liftedIndicator S)
      (KMSBasisComparisonAffineDensity.lifted_affineDensityBound_of_tuple S hS)
  have hidim : i ≤ Module.finrank F2 (Ambient ell) := by
    simpa [KMS.Ambient] using hi.trans hell
  have hm := rankComponent_fourth_moment_le_of_hybrid i (liftedIndicator S)
    (mixedRankConstant i * ε) (mul_nonneg (mixedRankConstant_nonneg i) hε)
    (by
      intro A B T _
      have hh := KMSAnalyticHybridEnergy.hybridDerivative_energy_bound
        i ε hε (liftedIndicator S) hf hd hidim A B T
      have hp : KMSAnalyticHybridEnergy.mapFintype
          (V := Ambient ell) (W := Ambient n) = basisMapFintype n ell :=
        Subsingleton.elim _ _
      have hq : KMSAnalyticHybridEnergy.mapFintype
          (V := Ambient n) (W := Ambient ell) = basisMapFintype ell n :=
        Subsingleton.elim _ _
      rw [hp, hq] at hh
      exact hh)
  exact hm.trans (a5_mixed_bound hi ε _ hε
    (Finset.expect_nonneg (fun _ _ => sq_nonneg _)))

end
end UniqueGamesTheorem.Inverse.KMSMomentTheorem

end

section

/-! The proved KMS Grassmann expansion principle. Its quantitative analytic
input is the actual basis-invariant fourth-moment theorem, whose proof uses
the fixed-character and fixed-point inductions. No expansion, inverse,
rank-level, or missing-moment premise occurs in this theorem. -/

namespace UniqueGamesTheorem.Inverse.KMSExpansion
noncomputable section

/-- The KMS expansion theorem with constants independent of both dimensions
and with the ambient threshold chosen after the plane dimension. -/
theorem kms_expansion : KMS.ExpansionPrinciple := by
  apply KMSMomentToExpansion.expansion_of_upperMoments
    KMSMomentConstants.fourthMomentConstant
    KMSMomentConstants.fourthMomentConstant_nonneg
    (fun r => 2 * r) (fun r => r)
  intro r ε hε _hε1 ell hell n S hS i hi
  exact KMSMomentTheorem.lifted_fourth_moment_bound r ε hε ell hell n S hS i hi

end
end UniqueGamesTheorem.Inverse.KMSExpansion

end

section

/-!
Exact mass of a nonempty column slice within a fixed row-advice fiber. A
column span of dimension at most `r` costs at most `ell*r` binary degrees of
freedom. All inhomogeneous values are represented by the chosen base point.
-/

namespace UniqueGamesTheorem.Inverse.RowErasureColumnMass

noncomputable section

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Decoder.AdviceFibers
open UniqueGamesTheorem.Inverse.RowErasureSliceQuotient

variable {E K R : Type*}
  [AddCommGroup E] [Module F2 E] [FiniteDimensional F2 E]
  [AddCommGroup K] [Module F2 K] [FiniteDimensional F2 K]
  [AddCommGroup R] [Module F2 R]

theorem card_affineSlice (A : K →ₗ[F2] R) (Q : Submodule F2 E)
    (M₀ : E →ₗ[F2] K) :
    Nat.card (AffineSlice A Q M₀) =
      2 ^ (Module.finrank F2 (E ⧸ Q) * Module.finrank F2 A.ker) := by
  rw [Nat.card_congr (equiv A Q M₀).symm,
    Module.natCard_eq_pow_finrank (K := F2), Module.finrank_linearMap]
  simp [F2]

theorem card_rowFiber (A : K →ₗ[F2] R) (M₀ : E →ₗ[F2] K) :
    Nat.card (RowFiber A (A.comp M₀)) =
      2 ^ (Module.finrank F2 E * Module.finrank F2 A.ker) := by
  rw [Nat.card_congr (rowFiberEquiv A (A.comp M₀) M₀ rfl).symm,
    Module.natCard_eq_pow_finrank (K := F2), Module.finrank_linearMap]
  simp [F2]

/-- The exact number of row-fiber points for each compatible specification on
the column span. Dependent column equations cost only their actual rank. -/
theorem card_rowFiber_eq_mul (A : K →ₗ[F2] R) (Q : Submodule F2 E)
    (M₀ : E →ₗ[F2] K) :
    Nat.card (RowFiber A (A.comp M₀)) = Nat.card (AffineSlice A Q M₀) *
      2 ^ (Module.finrank F2 Q * Module.finrank F2 A.ker) := by
  rw [card_rowFiber, card_affineSlice, ← pow_add, ← Nat.add_mul,
    Q.finrank_quotient_add_finrank]

/-- A denominator-free bound by the listed column count and ambient output
dimension, with no independence or full-rank hypothesis. -/
theorem card_rowFiber_le_mul (A : K →ₗ[F2] R) (Q : Submodule F2 E)
    (M₀ : E →ₗ[F2] K) (ell r : ℕ)
    (hQ : Module.finrank F2 Q ≤ r) (hK : Module.finrank F2 K ≤ ell) :
    Nat.card (RowFiber A (A.comp M₀)) ≤
      Nat.card (AffineSlice A Q M₀) * 2 ^ (ell * r) := by
  have hker : Module.finrank F2 A.ker ≤ ell := A.ker.finrank_le.trans hK
  have hexponent : Module.finrank F2 Q * Module.finrank F2 A.ker ≤ ell * r := by
    simpa only [Nat.mul_comm r ell] using Nat.mul_le_mul hQ hker
  rw [card_rowFiber_eq_mul A Q M₀]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hexponent)

/-- The exact uniform fraction of the row fiber occupied by its compatible
affine column slice. -/
theorem column_fraction_eq (A : K →ₗ[F2] R) (Q : Submodule F2 E)
    (M₀ : E →ₗ[F2] K) :
    (Nat.card (AffineSlice A Q M₀) : ℝ) /
        (Nat.card (RowFiber A (A.comp M₀)) : ℝ) =
      1 / (2 : ℝ) ^ (Module.finrank F2 Q * Module.finrank F2 A.ker) := by
  have hs : (0 : ℝ) < Nat.card (AffineSlice A Q M₀) := by
    rw [card_affineSlice]
    positivity
  rw [card_rowFiber_eq_mul A Q M₀]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [div_mul_cancel_left₀ hs.ne', one_div]

/-- At most `r` independent column constraints retain at least the fraction
`2^(-ell*r)` of any nonempty row-advice fiber. -/
theorem column_fraction_ge (A : K →ₗ[F2] R) (Q : Submodule F2 E)
    (M₀ : E →ₗ[F2] K) (ell r : ℕ)
    (hQ : Module.finrank F2 Q ≤ r) (hK : Module.finrank F2 K ≤ ell) :
    1 / (2 : ℝ) ^ (ell * r) ≤
      (Nat.card (AffineSlice A Q M₀) : ℝ) /
        (Nat.card (RowFiber A (A.comp M₀)) : ℝ) := by
  rw [column_fraction_eq]
  have hker : Module.finrank F2 A.ker ≤ ell := A.ker.finrank_le.trans hK
  have hexponent : Module.finrank F2 Q * Module.finrank F2 A.ker ≤ ell * r := by
    simpa only [Nat.mul_comm r ell] using Nat.mul_le_mul hQ hker
  exact one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexponent)

end
end UniqueGamesTheorem.Inverse.RowErasureColumnMass

end

section

/-!
The actual finite matrix column event occupies at least `2^(-ell*r)` of its
row-advice fiber. This connects the intrinsic quotient-map count to the padded
descriptions used by the selector, without assuming independent equations.
-/

namespace UniqueGamesTheorem.Inverse.RowErasureDescriptionColumnMass

noncomputable section
open UniqueGamesTheorem.Inverse.Shortcode
open UniqueGamesTheorem.Inverse.RowErasureDescriptions
open UniqueGamesTheorem.Inverse.RowErasureMatrix
open scoped BigOperators Classical

def rowFiber {ell m r : ℕ} (A : RowMap ell r) (s : Mat r m) :
    Finset (Mat ell m) :=
  Finset.univ.filter fun M => rowAdvice A M = s

@[simp] theorem mem_rowFiber {ell m r : ℕ} (A : RowMap ell r) (s : Mat r m)
    (M : Mat ell m) : M ∈ rowFiber A s ↔ rowAdvice A M = s := by
  simp [rowFiber]

/-- Forget only the column equations of a slice. -/
def rowOnly {ell m : ℕ} (S : Slice ell m) : Slice ell m where
  rows := S.rows
  columns := 0
  rowCoefficient := S.rowCoefficient
  rowValue := S.rowValue
  columnCoefficient := Fin.elim0
  columnValue := Fin.elim0

theorem rowOnly_contains_iff {ell m : ℕ} (S : Slice ell m) (M : Mat ell m) :
    (rowOnly S).Contains M ↔ rowAdvice S.rowCoefficient M = S.rowValue := by
  constructor
  · intro h
    funext i j
    exact h.1 i j
  · intro h
    constructor
    · intro i j
      exact congrFun (congrFun h i) j
    · intro i
      exact Fin.elim0 i

theorem rowOnly_points {ell m : ℕ} (S : Slice ell m) :
    (rowOnly S).points = rowFiber S.rowCoefficient S.rowValue := by
  ext M
  simp only [Slice.points, rowFiber, Finset.mem_filter, Finset.mem_univ, true_and,
    rowOnly_contains_iff]

theorem contains_rowOnly {ell m : ℕ} (S : Slice ell m) {M : Mat ell m}
    (hM : S.Contains M) : (rowOnly S).Contains M := by
  exact ⟨hM.1, fun i => Fin.elim0 i⟩

theorem rowOnly_columnSpan {ell m : ℕ} (S : Slice ell m) :
    (rowOnly S).columnSpan = ⊥ := by
  apply Submodule.span_eq_bot.mpr
  rintro _ ⟨i, _⟩
  exact Fin.elim0 i

theorem rowOnly_quotient_finrank {ell m : ℕ} (S : Slice ell m) :
    Module.finrank F2 (Shortcode.Vector m ⧸ (rowOnly S).columnSpan) = m := by
  have h := (rowOnly S).columnSpan.finrank_quotient_add_finrank
  have hz : Module.finrank F2 (rowOnly S).columnSpan = 0 := by
    rw [rowOnly_columnSpan]
    simp
  have hm : Module.finrank F2 (Shortcode.Vector m) = m := by simp [Shortcode.Vector]
  rw [hz, add_zero, hm] at h
  exact h

/-- The size of an actual nonempty row fiber, in the same coordinates used by
the selector's uniform matrix sample. -/
theorem rowFiber_card {ell m : ℕ} (S : Slice ell m) (M₀ : Mat ell m)
    (h₀ : S.Contains M₀) :
    (rowFiber S.rowCoefficient S.rowValue).card =
      2 ^ (m * Module.finrank F2 S.rowMap.ker) := by
  rw [← rowOnly_points S,
    (rowOnly S).card_points_eq_directions M₀ (contains_rowOnly S h₀),
    (rowOnly S).card_directions, rowOnly_quotient_finrank]
  rfl

theorem rowFiber_nonempty {ell m r : ℕ} (d : Description ell m r)
    (hne : d.toSlice.points.Nonempty) : (rowFiber d.1 d.2.1).Nonempty := by
  obtain ⟨M, hM⟩ := hne
  have hc : d.toSlice.Contains M := (Finset.mem_filter.mp hM).2
  refine ⟨M, (mem_rowFiber _ _ _).mpr ?_⟩
  funext i j
  exact hc.1 i j

/-- The chosen nonempty column event has the required mass inside its actual
row-advice fiber. The target coefficient and intercept do not affect its size. -/
theorem column_fraction_ge {ell m r : ℕ} (d : Description ell m r)
    (hne : d.toSlice.points.Nonempty) :
    1 / (2 : ℝ) ^ (ell * r) ≤
      (d.toSlice.points.card : ℝ) / ((rowFiber d.1 d.2.1).card : ℝ) := by
  obtain ⟨M₀, hM₀⟩ := hne
  have h₀ : d.toSlice.Contains M₀ := (Finset.mem_filter.mp hM₀).2
  have hs : d.toSlice.points.card = Nat.card
      (RowErasureSliceQuotient.AffineSlice d.toSlice.rowMap d.toSlice.columnSpan
        (Matrix.toLin' M₀)) := by
    rw [d.toSlice.card_points_eq_directions M₀ h₀, d.toSlice.card_directions,
      RowErasureColumnMass.card_affineSlice]
  have hr : (rowFiber d.1 d.2.1).card = Nat.card
      (UniqueGamesTheorem.Decoder.AdviceFibers.RowFiber d.toSlice.rowMap
        (d.toSlice.rowMap.comp (Matrix.toLin' M₀))) := by
    have hm : Module.finrank F2 (Shortcode.Vector m) = m := by simp [Shortcode.Vector]
    rw [RowErasureColumnMass.card_rowFiber, hm]
    exact rowFiber_card d.toSlice M₀ h₀
  have h := RowErasureColumnMass.column_fraction_ge
    d.toSlice.rowMap d.toSlice.columnSpan (Matrix.toLin' M₀) ell r
    d.toSlice.columnSpan_finrank_le (by simp [Shortcode.Vector])
  rwa [← hs, ← hr] at h

end
end UniqueGamesTheorem.Inverse.RowErasureDescriptionColumnMass

end

section

/-!
The selected column event under the actual uniform matrix and row-map samples.
The witness is fixed by visible row advice before testing the hidden matrix.
Fiber sizes are retained explicitly; no uniformity of row values is assumed.
The final averaging lemmas also allow arbitrary nonnegative context weights.
-/

namespace UniqueGamesTheorem.Inverse.RowErasure

noncomputable section
open scoped BigOperators

variable {X Y A S D : Type*}

def SliceFamily.selectedPoints (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) : Finset X :=
  match F.selectedDescription f α a s with
  | none => ∅
  | some d => F.points d

def SliceFamily.selectedHit (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) (x : X) : Prop :=
  ∃ d, F.selectedDescription f α a s = some d ∧ f x = F.target d x

theorem SliceFamily.selectedPoints_of_good (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) :
    F.selectedPoints f α a s = F.points (F.chosenDescription f α a s hgood) := by
  unfold SliceFamily.selectedPoints
  rw [F.selectedDescription_of_good f α a s hgood]

theorem SliceFamily.selectedHit_of_good (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) (x : X) :
    F.selectedHit f α a s x ↔ f x = F.target (F.chosenDescription f α a s hgood) x := by
  unfold SliceFamily.selectedHit
  rw [F.selectedDescription_of_good f α a s hgood]
  constructor
  · rintro ⟨d, hd, hhit⟩
    have he := Option.some.inj hd
    simpa only [he] using hhit
  · intro hhit
    exact ⟨_, rfl, hhit⟩

theorem SliceFamily.selectedPoints_support (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) (x : X)
    (hx : x ∈ F.selectedPoints f α a s) : F.advice a x = s := by
  classical
  cases hd : F.selectedDescription f α a s with
  | none => simp [SliceFamily.selectedPoints, hd] at hx
  | some d =>
    have hspec := F.selectedDescription_spec f α a s hd
    have hmem : x ∈ F.points d := by
      simpa only [SliceFamily.selectedPoints, hd] using hx
    have h := F.points_row d x hmem
    rw [hspec.1, hspec.2.1] at h
    exact h

theorem SliceFamily.selectedEvent_iff_points (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X) :
    F.selectedEvent f α a x ↔
      F.GoodAdvice f α a (F.advice a x) ∧
        x ∈ F.selectedPoints f α a (F.advice a x) := by
  classical
  by_cases hg : F.GoodAdvice f α a (F.advice a x)
  · rw [F.selectedEvent_iff_of_advice f α a (F.advice a x) hg x rfl,
      F.selectedPoints_of_good f α a (F.advice a x) hg]
    simp only [hg, true_and]
  · constructor
    · intro hx
      exact (hg (F.selectedEvent_good f α a x hx)).elim
    · intro hx
      exact (hg hx.1).elim

theorem SliceFamily.selectedMatch_iff_points (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X) :
    F.selectedMatch f α a x ↔
      (F.GoodAdvice f α a (F.advice a x) ∧
        x ∈ F.selectedPoints f α a (F.advice a x)) ∧
          F.selectedHit f α a (F.advice a x) x := by
  classical
  by_cases hg : F.GoodAdvice f α a (F.advice a x)
  · rw [F.selectedMatch_iff_of_advice f α a (F.advice a x) hg x rfl,
      F.selectedPoints_of_good f α a (F.advice a x) hg,
      F.selectedHit_of_good f α a (F.advice a x) hg x]
    simp only [hg, true_and]
  · constructor
    · intro hx
      exact (hg (F.selectedEvent_good f α a x (F.selectedMatch_event f α a x hx))).elim
    · intro hx
      exact (hg hx.1.1).elim

theorem SliceFamily.selectedPoints_match_sum (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) :
    (α / 2) * ((F.selectedPoints f α a s).card : ℝ) ≤
      ∑ x ∈ F.selectedPoints f α a s, indicator (F.selectedHit f α a s x) := by
  classical
  have hspec := F.chosenDescription_spec f α a s hgood
  have hcard : (0 : ℝ) < (F.points (F.chosenDescription f α a s hgood)).card :=
    Nat.cast_pos.mpr hspec.2.2.1.card_pos
  have hagree := hspec.2.2.2
  rw [SliceFamily.agreement, Finset.expect_eq_sum_div_card] at hagree
  rw [F.selectedPoints_of_good f α a s hgood]
  simp_rw [F.selectedHit_of_good f α a s hgood]
  exact (le_div_iff₀ hcard).mp hagree

end
end UniqueGamesTheorem.Inverse.RowErasure

namespace UniqueGamesTheorem.Inverse.RowErasureMatrix

noncomputable section
open UniqueGamesTheorem.Inverse.Shortcode
open UniqueGamesTheorem.Inverse.RowErasure
open UniqueGamesTheorem.Inverse.RowErasureDescriptions
open UniqueGamesTheorem.Inverse.RowErasureDescriptionColumnMass
open scoped BigOperators

variable {ell m r : ℕ}

theorem selectedPoints_column_mass (f : Mat ell m → Vector ell) (α : ℝ)
    (A : RowMap ell r) (s : Mat r m)
    (hgood : (family ell m r).GoodAdvice f α A s) :
    (1 / (2 : ℝ) ^ (ell * r)) * ((rowFiber A s).card : ℝ) ≤
      (((family ell m r).selectedPoints f α A s).card : ℝ) := by
  let d := (family ell m r).chosenDescription f α A s hgood
  have hspec := (family ell m r).chosenDescription_spec f α A s hgood
  have hne : d.toSlice.points.Nonempty := hspec.2.2.1
  have hcard : (0 : ℝ) < (rowFiber d.1 d.2.1).card :=
    Nat.cast_pos.mpr (rowFiber_nonempty d hne).card_pos
  have h := (le_div_iff₀ hcard).mp (column_fraction_ge d hne)
  have hA : d.1 = A := hspec.1
  have hs : d.2.1 = s := hspec.2.1
  rw [hA, hs] at h
  rw [(family ell m r).selectedPoints_of_good f α A s hgood]
  exact h

theorem selected_event_mass_ge (f : Mat ell m → Vector ell) (α : ℝ)
    (A : RowMap ell r) :
    (1 / (2 : ℝ) ^ (ell * r)) *
      uniformMass ((family ell m r).goodAt f α A) ≤
        uniformMass ((family ell m r).selectedEvent f α A) := by
  have h := SelectionPartition.mass_event_ge
    ((family ell m r).advice A) ((family ell m r).GoodAdvice f α A)
    ((family ell m r).selectedPoints f α A)
    ((family ell m r).selectedPoints_support f α A)
    (1 / (2 : ℝ) ^ (ell * r))
    (fun s hg => by
      have hfiber : SelectionPartition.fiber ((family ell m r).advice A) s =
          rowFiber A s := by
        ext M
        simp only [SelectionPartition.fiber, rowFiber, Finset.mem_filter,
          Finset.mem_univ, true_and]
        rfl
      rw [hfiber]
      exact selectedPoints_column_mass f α A s hg)
  have he : SelectionPartition.event ((family ell m r).advice A)
      ((family ell m r).GoodAdvice f α A) ((family ell m r).selectedPoints f α A) =
      (family ell m r).selectedEvent f α A := by
    funext M
    exact propext ((family ell m r).selectedEvent_iff_points f α A M).symm
  rw [he] at h
  exact h

theorem selected_match_mass_ge (f : Mat ell m → Vector ell) (α : ℝ)
    (A : RowMap ell r) :
    (α / 2) * uniformMass ((family ell m r).selectedEvent f α A) ≤
      uniformMass ((family ell m r).selectedMatch f α A) := by
  have h := SelectionPartition.mass_match_ge
    ((family ell m r).advice A) ((family ell m r).GoodAdvice f α A)
    ((family ell m r).selectedPoints f α A)
    ((family ell m r).selectedPoints_support f α A)
    ((family ell m r).selectedHit f α A)
    (α / 2) ((family ell m r).selectedPoints_match_sum f α A)
  have he : SelectionPartition.event ((family ell m r).advice A)
      ((family ell m r).GoodAdvice f α A) ((family ell m r).selectedPoints f α A) =
      (family ell m r).selectedEvent f α A := by
    funext M
    exact propext ((family ell m r).selectedEvent_iff_points f α A M).symm
  have hm : SelectionPartition.matchEvent ((family ell m r).advice A)
      ((family ell m r).GoodAdvice f α A) ((family ell m r).selectedPoints f α A)
      ((family ell m r).selectedHit f α A) =
      (family ell m r).selectedMatch f α A := by
    funext M
    exact propext ((family ell m r).selectedMatch_iff_points f α A M).symm
  rw [he, hm] at h
  exact h

def selectedEventMass (r : ℕ) (f : Mat ell m → Vector ell) (α : ℝ) : ℝ :=
  𝔼 A : RowMap ell r, uniformMass ((family ell m r).selectedEvent f α A)

def selectedMatchMass (r : ℕ) (f : Mat ell m → Vector ell) (α : ℝ) : ℝ :=
  𝔼 A : RowMap ell r, uniformMass ((family ell m r).selectedMatch f α A)

theorem selectedEventMass_ge (f : Mat ell m → Vector ell) (α : ℝ) :
    (1 / (2 : ℝ) ^ (ell * r)) * adviceMass ((family ell m r).goodAt f α) ≤
      selectedEventMass r f α := by
  have h := Finset.expect_le_expect (s := Finset.univ)
    (fun (A : RowMap ell r) _ => selected_event_mass_ge f α A)
  rw [← Finset.mul_expect] at h
  have hadvice : (𝔼 A : RowMap ell r, uniformMass ((family ell m r).goodAt f α A)) =
      adviceMass ((family ell m r).goodAt f α) := by
    simp only [uniformMass, adviceMass]
    exact Finset.expect_comm _ _ _
  rw [hadvice] at h
  exact h

theorem selectedMatchMass_ge (f : Mat ell m → Vector ell) (α : ℝ) :
    (α / 2) * selectedEventMass r f α ≤ selectedMatchMass r f α := by
  have h := Finset.expect_le_expect (s := Finset.univ)
    (fun (A : RowMap ell r) _ => selected_match_mass_ge f α A)
  rw [← Finset.mul_expect] at h
  exact h

/-- Context weights may be the pushforward of verifier seeds and need not be
uniform on distinct questions. Normalization is not needed for this inequality. -/
theorem selectedEventMass_weighted_ge {Q : Type*} [Fintype Q]
    (w : Q → ℝ) (hw : ∀ q, 0 ≤ w q) (f : Q → Mat ell m → Vector ell)
    (α g₀ : ℝ)
    (hgood : g₀ ≤ ∑ q, w q * adviceMass ((family ell m r).goodAt (f q) α)) :
    (1 / (2 : ℝ) ^ (ell * r)) * g₀ ≤ ∑ q, w q * selectedEventMass r (f q) α := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun q _ =>
    mul_le_mul_of_nonneg_left (selectedEventMass_ge (r := r) (f q) α) (hw q))
  have heq : (∑ q, w q * ((1 / (2 : ℝ) ^ (ell * r)) *
      adviceMass ((family ell m r).goodAt (f q) α))) =
      (1 / (2 : ℝ) ^ (ell * r)) *
        ∑ q, w q * adviceMass ((family ell m r).goodAt (f q) α) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [heq] at h
  exact (mul_le_mul_of_nonneg_left hgood (by positivity)).trans h

theorem selectedMatchMass_weighted_ge {Q : Type*} [Fintype Q]
    (w : Q → ℝ) (hw : ∀ q, 0 ≤ w q) (f : Q → Mat ell m → Vector ell) (α : ℝ) :
    (α / 2) * (∑ q, w q * selectedEventMass r (f q) α) ≤
      ∑ q, w q * selectedMatchMass r (f q) α := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun q _ =>
    mul_le_mul_of_nonneg_left (selectedMatchMass_ge (r := r) (f q) α) (hw q))
  have heq : (∑ q, w q * ((α / 2) * selectedEventMass r (f q) α)) =
      (α / 2) * (∑ q, w q * selectedEventMass r (f q) α) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rwa [heq] at h

theorem selectedMatchMass_conditional_ge {Q : Type*} [Fintype Q]
    (w : Q → ℝ) (hw : ∀ q, 0 ≤ w q) (f : Q → Mat ell m → Vector ell) (α : ℝ)
    (hpositive : 0 < ∑ q, w q * selectedEventMass r (f q) α) :
    α / 2 ≤ (∑ q, w q * selectedMatchMass r (f q) α) /
      (∑ q, w q * selectedEventMass r (f q) α) :=
  (le_div_iff₀ hpositive).mpr (selectedMatchMass_weighted_ge w hw f α)

/-- The same bound for a uniform finite seed space, allowing repeated contexts. -/
theorem selectedEventMass_contextual_ge {Q : Type*} [Fintype Q]
    (f : Q → Mat ell m → Vector ell) (α g₀ : ℝ)
    (hgood : g₀ ≤ 𝔼 q, adviceMass ((family ell m r).goodAt (f q) α)) :
    (1 / (2 : ℝ) ^ (ell * r)) * g₀ ≤ 𝔼 q, selectedEventMass r (f q) α := by
  have h := Finset.expect_le_expect (s := Finset.univ)
    (fun q _ => selectedEventMass_ge (r := r) (f q) α)
  rw [← Finset.mul_expect] at h
  exact (mul_le_mul_of_nonneg_left hgood (by positivity)).trans h

theorem selectedMatchMass_contextual_ge {Q : Type*} [Fintype Q]
    (f : Q → Mat ell m → Vector ell) (α : ℝ) :
    (α / 2) * (𝔼 q, selectedEventMass r (f q) α) ≤
      𝔼 q, selectedMatchMass r (f q) α := by
  have h := Finset.expect_le_expect (s := Finset.univ)
    (fun q _ => selectedMatchMass_ge (r := r) (f q) α)
  rwa [← Finset.mul_expect] at h

end
end UniqueGamesTheorem.Inverse.RowErasureMatrix

end

end OAI

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import OAI.Computability.UniqueGames.Analysis.MatrixCharactersLemmas
import OAI.Computability.UniqueGames.Analysis.RestrictionLemmas
import OAI.Computability.UniqueGames.Inverse.KMSAffineRestrictionComplementLemmas
import OAI.Computability.UniqueGames.Inverse.KMSAffineRestrictionPresentationLemmas
import OAI.Computability.UniqueGames.Inverse.KMSAnalyticHybridCoordinatesRankLemmas
import OAI.Computability.UniqueGames.Inverse.KMSAnalyticHybridEnergyTransport
import OAI.Computability.UniqueGames.Inverse.KMSFourthMomentMixedScalarLemmas

namespace OAI

section

/-!
# Transport of a prescribed compressed image to adapted coordinates

The complement is an arbitrary actual complement to the image subspace.
The resulting coordinate change carries each original Fourier fiber to the
adapted fiber, preserving coefficients, phases, and the actual selector.
-/

noncomputable section
namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixCharacters (linearTraceCharacter linearTraceCharacter_apply linearTracePair)
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Appendix
open KMSAnalytic KMSAnalyticHybridCoordinates

variable {A U B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup U] [Module F2 U]
  [AddCommGroup B] [Module F2 B] [AddCommGroup C] [Module F2 C]

/-- Keep the selected first factor and split the remaining space along its
prescribed compressed image. -/
def imageAmbientEquiv (W D : Submodule F2 U) (h : IsCompl W D) :
    (A × (W × D)) ≃ₗ[F2] (A × U) :=
  (LinearEquiv.refl F2 A).prodCongr (imageCoordinates W D h).symm

/-- The original function expressed in the adapted primal coordinates. -/
def imagePullback (W D : Submodule F2 U) (h : IsCompl W D)
    (f : ((A × U) →ₗ[F2] (B × C)) → ℝ)
    (X : (A × (W × D)) →ₗ[F2] (B × C)) : ℝ :=
  f (X.comp (imageAmbientEquiv (A := A) W D h).symm.toLinearMap)

/-- The same affine translate expressed in adapted coordinates. -/
def imageTranslate (W D : Submodule F2 U) (h : IsCompl W D)
    (T : (A × U) →ₗ[F2] (B × C)) :
    (A × (W × D)) →ₗ[F2] (B × C) :=
  T.comp (imageAmbientEquiv W D h).toLinearMap

theorem imageAmbientEquiv_leftRange (W D : Submodule F2 U) (h : IsCompl W D) :
    (LinearMap.range (LinearMap.inl F2 A (W × D))).map
      (imageAmbientEquiv (A := A) W D h).toLinearMap =
      LinearMap.range (LinearMap.inl F2 A U) := by
  rw [← LinearMap.range_comp]
  congr 1
  apply LinearMap.ext
  intro a
  change (a, (imageCoordinates W D h).symm 0) = (a, 0)
  rw [map_zero]

theorem image_hybrid_iff (W D : Submodule F2 U) (h : IsCompl W D)
    (S : (B × C) →ₗ[F2] (A × (W × D))) :
    LinearIdentities.Hybrid ((imageAmbientEquiv W D h).toLinearMap.comp S)
      (LinearMap.range (LinearMap.inl F2 A U))
      (LinearMap.range (LinearMap.inl F2 B C)) ↔
    LinearIdentities.Hybrid S (LinearMap.range (LinearMap.inl F2 A (W × D)))
      (LinearMap.range (LinearMap.inl F2 B C)) := by
  have hh := hybrid_arrowCongr (imageAmbientEquiv (A := A) W D h)
    (LinearEquiv.refl F2 (B × C)) S
    (LinearMap.range (LinearMap.inl F2 A (W × D)))
    (LinearMap.range (LinearMap.inl F2 B C))
  have he : LinearEquiv.arrowCongr (LinearEquiv.refl F2 (B × C))
      (imageAmbientEquiv (A := A) W D h) S =
      (imageAmbientEquiv W D h).toLinearMap.comp S := by
    apply LinearMap.ext
    intro x
    rfl
  rw [imageAmbientEquiv_leftRange, he] at hh
  simpa only [LinearEquiv.refl_toLinearMap, Submodule.map_id] using hh

theorem image_compression_eq_iff (W D : Submodule F2 U) (h : IsCompl W D)
    (z : B →ₗ[F2] W) (S : (B × C) →ₗ[F2] (A × (W × D))) :
    (LinearMap.snd F2 A U).comp
        (((imageAmbientEquiv W D h).toLinearMap.comp S).comp (LinearMap.inl F2 B C)) =
      W.subtype.comp z ↔ compressBlock S = z.prod (0 : B →ₗ[F2] D) := by
  have hc : (imageCoordinates W D h).toLinearMap.comp
      ((LinearMap.snd F2 A U).comp
        (((imageAmbientEquiv W D h).toLinearMap.comp S).comp (LinearMap.inl F2 B C))) =
      compressBlock S := by
    apply LinearMap.ext
    intro b
    change imageCoordinates W D h ((imageCoordinates W D h).symm (S (b, 0)).2) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  constructor
  · intro he
    rw [← hc, he, imageCoordinates_frequency]
  · intro he
    apply LinearMap.ext
    intro b
    apply (imageCoordinates W D h).injective
    have he' : (imageCoordinates W D h).toLinearMap.comp
        ((LinearMap.snd F2 A U).comp
          (((imageAmbientEquiv W D h).toLinearMap.comp S).comp (LinearMap.inl F2 B C))) =
        (imageCoordinates W D h).toLinearMap.comp (W.subtype.comp z) := by
      rw [hc, imageCoordinates_frequency, he]
    exact congrArg (fun L : B →ₗ[F2] (W × D) => L b) he'

theorem image_character (W D : Submodule F2 U) (h : IsCompl W D)
    (S : (B × C) →ₗ[F2] (A × (W × D))) (T : (A × U) →ₗ[F2] (B × C)) :
    linearTraceCharacter ((imageAmbientEquiv W D h).toLinearMap.comp S) T =
      linearTraceCharacter S (imageTranslate W D h T) := by
  simp only [imageTranslate, linearTraceCharacter_apply, linearTracePair, LinearMap.comp_assoc]

variable [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C]
  [Fintype ((A × U) →ₗ[F2] (B × C))] [Fintype ((B × C) →ₗ[F2] (A × U))]

theorem image_rank_coefficient (W D : Submodule F2 U) (h : IsCompl W D)
    [Fintype ((A × (W × D)) →ₗ[F2] (B × C))]
    [Fintype ((B × C) →ₗ[F2] (A × (W × D)))]
    (f : ((A × U) →ₗ[F2] (B × C)) → ℝ) (i : ℕ)
    (S : (B × C) →ₗ[F2] (A × (W × D))) :
    linearCoeff (rankComponent i (imagePullback W D h f)) S =
      linearCoeff (rankComponent i f) ((imageAmbientEquiv W D h).toLinearMap.comp S) := by
  change linearCoeff (rankComponent i (fun X => f
      (LinearEquiv.arrowCongr (imageAmbientEquiv W D h) (LinearEquiv.refl F2 (B × C)) X))) S = _
  rw [rankComponent_pullback, NaturalTransport.linearCoeff_pullback]
  rfl

/-- Exact reindexing of a selected coefficient at a prescribed compressed
image. No rank, surjectivity, or basis-invariance assumption is needed. -/
theorem image_coefficient_sum_transport (W D : Submodule F2 U) (h : IsCompl W D)
    [Fintype ((A × (W × D)) →ₗ[F2] (B × C))]
    [Fintype ((B × C) →ₗ[F2] (A × (W × D)))]
    (z : B →ₗ[F2] W) (f : ((A × U) →ₗ[F2] (B × C)) → ℝ)
    (T : (A × U) →ₗ[F2] (B × C)) (i : ℕ) :
    (∑ S : (B × C) →ₗ[F2] (A × U),
      if LinearIdentities.Hybrid S (LinearMap.range (LinearMap.inl F2 A U))
          (LinearMap.range (LinearMap.inl F2 B C)) ∧
          (LinearMap.snd F2 A U).comp (S.comp (LinearMap.inl F2 B C)) = W.subtype.comp z
      then linearCoeff (rankComponent i f) S * (linearTraceCharacter S T).re else 0) =
    ∑ S : (B × C) →ₗ[F2] (A × (W × D)),
      if LinearIdentities.Hybrid S (LinearMap.range (LinearMap.inl F2 A (W × D)))
          (LinearMap.range (LinearMap.inl F2 B C)) ∧
          compressBlock S = z.prod (0 : B →ₗ[F2] D)
      then linearCoeff (rankComponent i (imagePullback W D h f)) S *
        (linearTraceCharacter S (imageTranslate W D h T)).re else 0 := by
  symm
  apply Fintype.sum_equiv
    (LinearEquiv.arrowCongr (LinearEquiv.refl F2 (B × C))
      (imageAmbientEquiv (A := A) W D h)).toEquiv
  intro S
  change _ = if LinearIdentities.Hybrid ((imageAmbientEquiv W D h).toLinearMap.comp S)
      (LinearMap.range (LinearMap.inl F2 A U))
      (LinearMap.range (LinearMap.inl F2 B C)) ∧
      (LinearMap.snd F2 A U).comp
        (((imageAmbientEquiv W D h).toLinearMap.comp S).comp (LinearMap.inl F2 B C)) =
          W.subtype.comp z
    then linearCoeff (rankComponent i f) ((imageAmbientEquiv W D h).toLinearMap.comp S) *
      (linearTraceCharacter ((imageAmbientEquiv W D h).toLinearMap.comp S) T).re else 0
  rw [image_hybrid_iff, image_compression_eq_iff, ← image_rank_coefficient,
    image_character]

end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end

section

/-!
# Vanishing above the ambient rank

The actual Fourier component is zero when its selected rank exceeds either
matrix-space dimension. Its hybrid derivatives therefore vanish directly,
without Fourier analysis on the quotient restriction domain.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix.Derivatives
open UniqueGamesTheorem.Inverse.KMSAnalytic

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- No dual frequency has image dimension larger than the primal domain. -/
theorem rankComponent_eq_zero_of_finrank_lt
    (f : (E →ₗ[F2] F) → ℝ) (i : ℕ) (hi : Module.finrank F2 E < i) :
    rankComponent i f = 0 := by
  apply eq_of_coeff_eq
  intro S
  have hne : Module.finrank F2 S.range ≠ i :=
    ne_of_lt (lt_of_le_of_lt S.range.finrank_le hi)
  rw [rankComponent, coeff_component, ite_eq_right hne]
  simp [linearCoeff]

/-- The dual frequency rank is also bounded by its domain, the primal
codomain. This includes rectangular spaces in either orientation. -/
theorem rankComponent_eq_zero_of_codomain_finrank_lt
    (f : (E →ₗ[F2] F) → ℝ) (i : ℕ) (hi : Module.finrank F2 F < i) :
    rankComponent i f = 0 := by
  apply eq_of_coeff_eq
  intro S
  have hne : Module.finrank F2 S.range ≠ i :=
    ne_of_lt (lt_of_le_of_lt (LinearMap.finrank_range_le S) hi)
  rw [rankComponent, coeff_component, ite_eq_right hne]
  simp [linearCoeff]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
/-- The zero function remains zero under the actual hybrid projection and
affine restriction. No enumeration of quotient frequencies is required. -/
theorem hybridDerivative_zero (A : Submodule F2 E) (B : Submodule F2 F)
    (T : E →ₗ[F2] F) :
    hybridDerivative A B T (0 : (E →ₗ[F2] F) → ℝ) = 0 := by
  funext N
  simp [hybridDerivative, hybridProjector, spectralProjector, restrict, linearCoeff]

theorem hybridDerivative_rankComponent_eq_zero_of_finrank_lt
    (A : Submodule F2 E) (B : Submodule F2 F)
    (T : E →ₗ[F2] F) (f : (E →ₗ[F2] F) → ℝ) (i : ℕ)
    (hi : Module.finrank F2 E < i) :
    hybridDerivative A B T (rankComponent i f) = 0 := by
  rw [rankComponent_eq_zero_of_finrank_lt f i hi]
  exact hybridDerivative_zero A B T

theorem hybridDerivative_rankComponent_eq_zero_of_codomain_finrank_lt
    (A : Submodule F2 E) (B : Submodule F2 F)
    (T : E →ₗ[F2] F) (f : (E →ₗ[F2] F) → ℝ) (i : ℕ)
    (hi : Module.finrank F2 F < i) :
    hybridDerivative A B T (rankComponent i f) = 0 := by
  rw [rankComponent_eq_zero_of_codomain_finrank_lt f i hi]
  exact hybridDerivative_zero A B T

/-- Finite primal restriction domains suffice to evaluate the zero energy;
there is no additional `Fintype` requirement on the compressed dual space. -/
theorem hybridDerivative_rankComponent_energy_eq_zero_of_finrank_lt
    [Finite E] [Finite F]
    (A : Submodule F2 E) (B : Submodule F2 F)
    (T : E →ₗ[F2] F) (f : (E →ₗ[F2] F) → ℝ) (i : ℕ)
    (hi : Module.finrank F2 E < i) :
    (𝔼 N, hybridDerivative A B T (rankComponent i f) N ^ 2) = 0 := by
  rw [hybridDerivative_rankComponent_eq_zero_of_finrank_lt A B T f i hi]
  simp

end
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

section

/-!
# The actual small-space Fourier component

An injection from the small domain into the large domain lifts dual
frequencies by composition. Only surjective small-space frequencies are
retained. The identities below use the actual trace-character coefficients
and normalized primal expectation; no fourth-moment estimate is assumed.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier

variable {E F I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]

/-- The Fourier array of the small full-rank component. -/
def smallCoeff (ι : I →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ)
    (T : F →ₗ[F2] I) : ℝ :=
  if Function.Surjective T then linearCoeff f (ι.comp T) else 0

/-- A genuine function on the small primal matrix space, synthesized in its
own orthonormal trace-character basis. -/
def smallComponent (ι : I →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ) :
    (I →ₗ[F2] F) → ℝ := synthesis (smallCoeff ι f)

omit [FiniteDimensional F2 E] [Fintype (F →ₗ[F2] E)] in
@[simp] theorem coeff_smallComponent (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (T : F →ₗ[F2] I) :
    linearCoeff (smallComponent ι f) T = smallCoeff ι f T :=
  coeff_synthesis _ _

omit [FiniteDimensional F2 E] [Fintype (F →ₗ[F2] E)] in
theorem coeff_smallComponent_of_surjective (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (T : F →ₗ[F2] I)
    (hT : Function.Surjective T) :
    linearCoeff (smallComponent ι f) T = linearCoeff f (ι.comp T) := by
  simp only [coeff_smallComponent, smallCoeff, ite_eq_left hT]

omit [FiniteDimensional F2 E] [Fintype (F →ₗ[F2] E)] in
theorem coeff_smallComponent_of_not_surjective (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (T : F →ₗ[F2] I)
    (hT : ¬ Function.Surjective T) : linearCoeff (smallComponent ι f) T = 0 := by
  simp only [coeff_smallComponent, smallCoeff, ite_eq_right hT]

omit [FiniteDimensional F2 E] [Fintype (F →ₗ[F2] E)] in
/-- Exact normalization: primal expectation equals an unnormalized sum over
surjective small-space frequencies. -/
theorem smallComponent_energy (ι : I →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, smallComponent ι f X ^ 2) =
      ∑ T ∈ Finset.univ.filter (fun T : F →ₗ[F2] I => Function.Surjective T),
        linearCoeff f (ι.comp T) ^ 2 := by
  rw [smallComponent, synthesis_energy, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hT : Function.Surjective T <;> simp [smallCoeff, hT]

omit [FiniteDimensional F2 E] [Fintype (F →ₗ[F2] E)] in
/-- Every retained frequency has rank equal to the small domain dimension. -/
theorem rankComponent_smallComponent (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) :
    rankComponent (Module.finrank F2 I) (smallComponent ι f) = smallComponent ι f := by
  apply eq_of_coeff_eq
  intro T
  simp only [rankComponent, coeff_component, coeff_smallComponent]
  by_cases hT : Function.Surjective T
  · have hr : Module.finrank F2 T.range = Module.finrank F2 I :=
      Submodule.eq_top_iff_finrank_eq.mp (LinearMap.range_eq_top.mpr hT)
    simp [hr]
  · simp [smallCoeff, hT]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)] in
/-- Composition with an injection preserves the actual kernel. -/
theorem ker_comp_of_injective (ι : I →ₗ[F2] E) (hι : Function.Injective ι)
    (T : F →ₗ[F2] I) : (ι.comp T).ker = T.ker :=
  LinearMap.ker_comp_of_ker_eq_bot T (LinearMap.ker_eq_bot.mpr hι)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)] in
/-- The small Fourier array is independent of the chosen injection once the
large function's actual coefficients are proved constant on kernel classes. -/
theorem smallCoeff_eq_of_kernel_coeff_const (ι κ : I →ₗ[F2] E)
    (hι : Function.Injective ι) (hκ : Function.Injective κ)
    (f : (E →ₗ[F2] F) → ℝ)
    (hcoeff : ∀ S T : F →ₗ[F2] E,
      S.ker = T.ker → linearCoeff f S = linearCoeff f T) :
    smallCoeff ι f = smallCoeff κ f := by
  funext T
  unfold smallCoeff
  by_cases hT : Function.Surjective T
  · simp only [ite_eq_left hT]
    exact hcoeff _ _ ((ker_comp_of_injective ι hι T).trans
      (ker_comp_of_injective κ hκ T).symm)
  · simp only [ite_eq_right hT]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] in
/-- Equality is of the actual synthesized functions, not merely their norms. -/
theorem smallComponent_eq_of_kernel_coeff_const (ι κ : I →ₗ[F2] E)
    (hι : Function.Injective ι) (hκ : Function.Injective κ)
    (f : (E →ₗ[F2] F) → ℝ)
    (hcoeff : ∀ S T : F →ₗ[F2] E,
      S.ker = T.ker → linearCoeff f S = linearCoeff f T) :
    smallComponent ι f = smallComponent κ f :=
  congrArg synthesis (smallCoeff_eq_of_kernel_coeff_const ι κ hι hκ f hcoeff)

omit [FiniteDimensional F2 E] [Fintype (F →ₗ[F2] E)] in
/-- A small component is orthogonal to any small-space function whose full
rank coefficients vanish. -/
theorem smallComponent_orthogonal (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (g : (I →ₗ[F2] F) → ℝ)
    (hg : ∀ T : F →ₗ[F2] I, Function.Surjective T → linearCoeff g T = 0) :
    (𝔼 X, smallComponent ι f X * g X) = 0 := by
  rw [← linear_parseval_inner]
  apply Finset.sum_eq_zero
  intro T _
  rw [coeff_smallComponent]
  by_cases hT : Function.Surjective T
  · rw [hg T hT, mul_zero]
  · simp [smallCoeff, hT]

/-- Injective frequency lifting cannot increase the total squared norm. -/
theorem smallComponent_energy_le (ι : I →ₗ[F2] E) (hι : Function.Injective ι)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, smallComponent ι f X ^ 2) ≤ 𝔼 X, f X ^ 2 := by
  have hinj : Function.Injective (fun T : F →ₗ[F2] I => ι.comp T) := by
    intro T U hTU
    apply LinearMap.ext
    intro x
    apply hι
    exact congrArg (fun S : F →ₗ[F2] E => S x) hTU
  rw [smallComponent_energy, ← linear_parseval]
  calc
    _ = ∑ S ∈ (Finset.univ.filter (fun T : F →ₗ[F2] I => Function.Surjective T)).image
        (fun T => ι.comp T), linearCoeff f S ^ 2 := by
      rw [Finset.sum_image]
      intro T _ U _ hTU
      exact hinj hTU
    _ ≤ ∑ S, linearCoeff f S ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun S _ _ => sq_nonneg _)

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-!
# Exact synthesis over small-space embeddings

Every rank-`dim I` frequency factors as an injection from `I` after a
surjection onto `I`. The number of these factorizations is exactly the
number of automorphisms of `I`, expressed as the square injection count.
Reindexing the actual Fourier synthesis gives a pointwise identity, before
any inequalities or basis-invariance assumptions are used.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixCharacters
  (linearTraceCharacter linearTraceCharacter_apply linearTracePair)
open UniqueGamesTheorem.Fourier.MatrixFourier
open KMSKernelFiberCard (RankFrequency FullFrequency rankKernel fullKernel)

variable {E F I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I]

/-- The actual injective maps from the comparison space. -/
abbrev SmallEmbedding (I E : Type*) [AddCommGroup I] [Module F2 I]
    [AddCommGroup E] [Module F2 E] :=
  {ι : I →ₗ[F2] E // Function.Injective ι}

/-- A map with the same kernel as a surjection descends to its target. -/
def factorThroughSurjection (S : F →ₗ[F2] E) (T : F →ₗ[F2] I)
    (hT : Function.Surjective T) (hker : T.ker = S.ker) : I →ₗ[F2] E :=
  (T.ker.liftQ S hker.le).comp (T.quotKerEquivOfSurjective hT).symm.toLinearMap

@[simp] theorem factorThroughSurjection_apply (S : F →ₗ[F2] E) (T : F →ₗ[F2] I)
    (hT : Function.Surjective T) (hker : T.ker = S.ker) (x : F) :
    factorThroughSurjection S T hT hker (T x) = S x := by
  simp [factorThroughSurjection]

@[simp] theorem factorThroughSurjection_comp (S : F →ₗ[F2] E) (T : F →ₗ[F2] I)
    (hT : Function.Surjective T) (hker : T.ker = S.ker) :
    (factorThroughSurjection S T hT hker).comp T = S := by
  ext x
  exact factorThroughSurjection_apply S T hT hker x

theorem factorThroughSurjection_injective (S : F →ₗ[F2] E) (T : F →ₗ[F2] I)
    (hT : Function.Surjective T) (hker : T.ker = S.ker) :
    Function.Injective (factorThroughSurjection S T hT hker) := by
  exact (LinearMap.ker_eq_bot.mp (T.ker.ker_liftQ_eq_bot S hker.le hker.ge)).comp
    (T.quotKerEquivOfSurjective hT).symm.injective

/-- Compose the two factors and retain the proved rank. -/
def factorFrequency (p : SmallEmbedding I E × FullFrequency F I) : RankFrequency F E I :=
  ⟨p.1.val.comp p.2.val, by
    rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr p.2.property)]
    exact LinearMap.finrank_range_of_inj p.1.property⟩

/-- Once the surjective factor is fixed, the injective factor is unique. -/
def factorizationFiberEquivFullKernel (S : RankFrequency F E I) :
    {p : SmallEmbedding I E × FullFrequency F I // factorFrequency p = S} ≃
      {T : FullFrequency F I // fullKernel T = rankKernel S} where
  toFun p := ⟨p.val.2, by
    apply Subtype.ext
    have hcomp : p.val.1.val.comp p.val.2.val = S.val :=
      congrArg Subtype.val p.property
    calc
      p.val.2.val.ker = (p.val.1.val.comp p.val.2.val).ker :=
        (LinearMap.ker_comp_of_ker_eq_bot p.val.2.val
          (LinearMap.ker_eq_bot.mpr p.val.1.property)).symm
      _ = S.val.ker := congrArg LinearMap.ker hcomp⟩
  invFun T :=
    ⟨(⟨factorThroughSurjection S.val T.val.val T.val.property
          (congrArg Subtype.val T.property),
        factorThroughSurjection_injective S.val T.val.val T.val.property
          (congrArg Subtype.val T.property)⟩, T.val),
      Subtype.ext (factorThroughSurjection_comp S.val T.val.val T.val.property
        (congrArg Subtype.val T.property))⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply LinearMap.ext
      intro y
      obtain ⟨x, rfl⟩ := p.val.2.property y
      have hk : p.val.2.val.ker = S.val.ker := by
        have hcomp : p.val.1.val.comp p.val.2.val = S.val :=
          congrArg Subtype.val p.property
        rw [← hcomp, LinearMap.ker_comp_of_ker_eq_bot p.val.2.val
          (LinearMap.ker_eq_bot.mpr p.val.1.property)]
      change factorThroughSurjection S.val p.val.2.val p.val.2.property hk
        (p.val.2.val x) = p.val.1.val (p.val.2.val x)
      rw [factorThroughSurjection_apply]
      exact (congrArg (fun Z : F →ₗ[F2] E => Z x)
        (congrArg Subtype.val p.property)).symm
    · rfl
  right_inv T := by
    apply Subtype.ext
    rfl

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)] [Fintype (I →ₗ[F2] E)]

omit [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] F)]
  [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] in
/-- The exact multiplicity in the embedding expansion is the square
injection count, independent of the ambient frequency. -/
theorem factorization_fiber_card (S : RankFrequency F E I) :
    (Finset.univ.filter (fun p : SmallEmbedding I E × FullFrequency F I =>
      factorFrequency p = S)).card = KMSInjectionCount.beta I I := by
  calc
    _ = Fintype.card {p : SmallEmbedding I E × FullFrequency F I //
        factorFrequency p = S} := (Fintype.card_subtype _).symm
    _ = Fintype.card {T : FullFrequency F I // fullKernel T = rankKernel S} :=
      Fintype.card_congr (factorizationFiberEquivFullKernel S)
    _ = (Finset.univ.filter (fun T : FullFrequency F I =>
        fullKernel T = rankKernel S)).card := Fintype.card_subtype _
    _ = KMSInjectionCount.beta I I := KMSKernelFiberCard.fullKernel_fiber_card _

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] [Fintype (I →ₗ[F2] E)] in
theorem smallComponent_apply_fullFrequency (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (X : I →ₗ[F2] F) :
    smallComponent ι f X = ∑ T : FullFrequency F I,
      linearCoeff f (ι.comp T.val) * (linearTraceCharacter T.val X).re := by
  unfold smallComponent synthesis
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun T : F →ₗ[F2] I =>
      Function.Surjective T)) (by simp)
      (fun T => linearCoeff f (ι.comp T) * (linearTraceCharacter T X).re),
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hT : Function.Surjective T <;> simp [smallCoeff, hT]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)] [Fintype (I →ₗ[F2] E)] in
theorem rankComponent_apply_rankFrequency (f : (E →ₗ[F2] F) → ℝ)
    (X : E →ₗ[F2] F) :
    rankComponent (Module.finrank F2 I) f X = ∑ S : RankFrequency F E I,
      linearCoeff f S.val * (linearTraceCharacter S.val X).re := by
  unfold rankComponent component synthesis
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun S : F →ₗ[F2] E =>
      Module.finrank F2 S.range = Module.finrank F2 I)) (by simp)
      (fun S => linearCoeff f S * (linearTraceCharacter S X).re),
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> simp

omit [FiniteDimensional F2 E] [Fintype (I →ₗ[F2] F)] in
/-- Exact pointwise orbit synthesis. No basis-invariance assumption is
required: every small component retains the coefficients from its own embedding. -/
theorem sum_smallComponent_embeddings (f : (E →ₗ[F2] F) → ℝ)
    (X : E →ₗ[F2] F) :
    (∑ ι : SmallEmbedding I E, smallComponent ι.val f (X.comp ι.val)) =
      (KMSInjectionCount.beta I I : ℝ) * rankComponent (Module.finrank F2 I) f X := by
  let b : RankFrequency F E I → ℝ := fun S =>
    linearCoeff f S.val * (linearTraceCharacter S.val X).re
  calc
    _ = ∑ p : SmallEmbedding I E × FullFrequency F I, b (factorFrequency p) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro ι _
      rw [smallComponent_apply_fullFrequency]
      apply Finset.sum_congr rfl
      intro T _
      change linearCoeff f (ι.val.comp T.val) *
          (linearTraceCharacter T.val (X.comp ι.val)).re =
        linearCoeff f (ι.val.comp T.val) *
          (linearTraceCharacter (ι.val.comp T.val) X).re
      simp only [linearTraceCharacter_apply, linearTracePair, LinearMap.comp_assoc]
    _ = ∑ S : RankFrequency F E I,
        ((Finset.univ.filter fun p : SmallEmbedding I E × FullFrequency F I =>
          factorFrequency p = S).card : ℝ) * b S := by
      calc
        _ = ∑ p : SmallEmbedding I E × FullFrequency F I,
            ∑ S : RankFrequency F E I, if factorFrequency p = S then b S else 0 := by
          apply Finset.sum_congr rfl
          intro p _
          simp
        _ = ∑ S : RankFrequency F E I,
            ∑ p : SmallEmbedding I E × FullFrequency F I,
              if factorFrequency p = S then b S else 0 := Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro S _
          rw [← Finset.sum_filter]
          simp
    _ = (KMSInjectionCount.beta I I : ℝ) * ∑ S : RankFrequency F E I, b S := by
      simp_rw [factorization_fiber_card]
      rw [Finset.mul_sum]
    _ = _ := by simp only [b, rankComponent_apply_rankFrequency]

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

namespace UniqueGamesTheorem.Inverse.KMSBasisInvariant
noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

/-- The invertible change of the ordered domain basis. -/
def primalChange (g : E ≃ₗ[F2] E) : (E →ₗ[F2] F) ≃ (E →ₗ[F2] F) where
  toFun X := X.comp g.toLinearMap
  invFun X := X.comp g.symm.toLinearMap
  left_inv X := by ext x; simp
  right_inv X := by ext x; simp

/-- The contragredient reindexing used in the trace pairing. -/
def frequencyChange (g : E ≃ₗ[F2] E) : (F →ₗ[F2] E) ≃ (F →ₗ[F2] E) where
  toFun S := g.toLinearMap.comp S
  invFun S := g.symm.toLinearMap.comp S
  left_inv S := by ext x; simp
  right_inv S := by ext x; simp

def IsBasisInvariant (f : (E →ₗ[F2] F) → ℝ) : Prop :=
  ∀ (g : E ≃ₗ[F2] E) X, f (X.comp g.toLinearMap) = f X

theorem character_change (g : E ≃ₗ[F2] E) (S : F →ₗ[F2] E)
    (X : E →ₗ[F2] F) :
    linearTraceCharacter (g.toLinearMap.comp S) X =
      linearTraceCharacter S (X.comp g.toLinearMap) := by
  simp only [linearTraceCharacter_apply, linearTracePair, LinearMap.comp_assoc]

variable [Fintype (E →ₗ[F2] F)]

/-- Invariance of the function transfers to its actual normalized coefficients. -/
theorem coefficient_change (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) (g : E ≃ₗ[F2] E) (S : F →ₗ[F2] E) :
    linearCoeff f (g.toLinearMap.comp S) = linearCoeff f S := by
  unfold linearCoeff
  apply Fintype.expect_equiv (primalChange g)
  intro X
  change f X * (linearTraceCharacter (g.toLinearMap.comp S) X).re =
    f (X.comp g.toLinearMap) * (linearTraceCharacter S (X.comp g.toLinearMap)).re
  rw [character_change, hf g X]

/-- The degree is the rank of the actual dual linear map. -/
def frequencyRank (S : F →ₗ[F2] E) : ℕ := Module.finrank F2 (LinearMap.range S)

omit [Fintype (E →ₗ[F2] F)] in
theorem frequencyRank_change (g : E ≃ₗ[F2] E) (S : F →ₗ[F2] E) :
    frequencyRank (g.toLinearMap.comp S) = frequencyRank S := by
  unfold frequencyRank
  rw [LinearMap.range_comp, g.finrank_map_eq]

variable [Fintype (F →ₗ[F2] E)]

/-- Exact rank projection, defined directly by trace characters. -/
def rankProjection (i : ℕ) (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) : ℝ :=
  ∑ S, if frequencyRank S = i then linearCoeff f S * (linearTraceCharacter S X).re else 0

/-- Each rank projection preserves basis invariance. -/
theorem rankProjection_invariant (i : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) : IsBasisInvariant (rankProjection i f) := by
  intro g X
  unfold rankProjection
  apply Fintype.sum_equiv (frequencyChange g)
  intro S
  change (if frequencyRank S = i then
      linearCoeff f S * (linearTraceCharacter S (X.comp g.toLinearMap)).re else 0) =
    if frequencyRank (g.toLinearMap.comp S) = i then
      linearCoeff f (g.toLinearMap.comp S) *
        (linearTraceCharacter (g.toLinearMap.comp S) X).re else 0
  rw [frequencyRank_change, coefficient_change f hf, character_change]

end
end UniqueGamesTheorem.Inverse.KMSBasisInvariant

end

section

/-! The analytic synthesis and the direct basis-invariant projection are the
same actual function. This identity fixes the interface for both moment and
spectral estimates. -/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Inverse.KMSBasisInvariant

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem rankComponent_eq_rankProjection (i : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    rankComponent i f = rankProjection i f := by
  funext X
  simp only [rankComponent, component, synthesis, rankProjection, frequencyRank,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> simp_all [UniqueGamesTheorem.Fourier.MatrixCharacters.F2]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem rankComponent_invariant (i : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) : IsBasisInvariant (rankComponent i f) := by
  rw [rankComponent_eq_rankProjection]
  exact rankProjection_invariant i f hf

/-- The degree bound follows from the literal coefficient filter. -/
theorem rankComponent_coeff_eq_zero_of_ne (i : ℕ)
    (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E)
    (hS : Module.finrank F2 S.range ≠ i) :
    linearCoeff (rankComponent i f) S = 0 := by
  simp only [rankComponent, coeff_component, ite_eq_right hS]

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-!
# Homogeneous restriction bounds for the KMS character induction

The restriction below samples linear maps into an actual subspace of the
output. Quantifying over injective presentations makes the bound invariant
under a choice of coordinates. This is a transparent squared-density
hypothesis, not a Fourier, inverse, or fourth-moment estimate.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Inverse.KMSBasisInvariant

universe u v
variable {E : Type u} {F B : Type v}
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [AddCommGroup B] [Module F2 B]

/-- Every homogeneous output restriction of codimension at most `r` has the
stated actual normalized squared norm. The dimension inequality avoids
truncated subtraction in the restriction-composition step. -/
def HomogeneousRestrictionBound (r : ℕ) (ε : ℝ) (f : (E →ₗ[F2] F) → ℝ) : Prop :=
  ∀ (C : Type v) [AddCommGroup C] [Module F2 C] [FiniteDimensional F2 C]
    [Fintype (E →ₗ[F2] C)],
    ∀ J : C →ₗ[F2] F, Function.Injective J →
      Module.finrank F2 F ≤ Module.finrank F2 C + r →
        (𝔼 X : E →ₗ[F2] C, f (J.comp X) ^ 2) ≤ ε

/-- Restricting to codimension `s` leaves the remaining budget `r`. The proof
uses only composition of actual injections and addition of dimensions. -/
theorem HomogeneousRestrictionBound.codomain_pullback
    [FiniteDimensional F2 B] (r s : ℕ) (ε : ℝ)
    (f : (E →ₗ[F2] F) → ℝ)
    (hf : HomogeneousRestrictionBound (r + s) ε f)
    (J : B →ₗ[F2] F) (hJ : Function.Injective J)
    (hcodim : Module.finrank F2 F ≤ Module.finrank F2 B + s) :
    HomogeneousRestrictionBound r ε (fun X : E →ₗ[F2] B => f (J.comp X)) := by
  intro C _ _ _ _ K hK hdim
  have hdim' : Module.finrank F2 F ≤ Module.finrank F2 C + (r + s) := by omega
  simpa only [LinearMap.comp_assoc] using hf C (J.comp K) (hJ.comp hK) hdim'

/-- The unrestricted squared norm is included by the identity presentation. -/
theorem HomogeneousRestrictionBound.energy_le
    [FiniteDimensional F2 F] [Fintype (E →ₗ[F2] F)]
    (r : ℕ) (ε : ℝ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : HomogeneousRestrictionBound r ε f) : (𝔼 X, f X ^ 2) ≤ ε := by
  simpa using hf F (LinearMap.id : F →ₗ[F2] F) Function.injective_id
    (Nat.le_add_right (Module.finrank F2 F) r)

/-- A homogeneous output restriction retains the original domain-basis
invariance, as required at every step of the fixed-character induction. -/
theorem basisInvariant_codomain_pullback (f : (E →ₗ[F2] F) → ℝ)
    (hf : IsBasisInvariant f) (J : B →ₗ[F2] F) :
    IsBasisInvariant (fun X : E →ₗ[F2] B => f (J.comp X)) := by
  intro g X
  simpa only [LinearMap.comp_assoc] using hf g (J.comp X)

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

end OAI

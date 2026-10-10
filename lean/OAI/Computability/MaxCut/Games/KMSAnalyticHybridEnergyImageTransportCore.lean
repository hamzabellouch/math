import Mathlib
import OAI.Computability.MaxCut.Games.KMSFourthMomentMixedRestriction
import OAI.Computability.MaxCut.Games.OperatorNorm

namespace OAI

/-!
# Transport of a prescribed compressed image to adapted coordinates

The complement is an arbitrary actual complement to the image subspace.
The resulting coordinate change carries each original Fourier fiber to the
adapted fiber, preserving coefficients, phases, and the actual selector.
-/

noncomputable section
namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixCharacters (linearTraceCharacter linearTraceCharacter_apply linearTracePair)
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Appendix
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

end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

/-! The exact transport into the actual adapted fiber used by the mixed bound. -/

namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixCharacters (linearTraceCharacter)
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Appendix
open KMSAnalytic KMSAnalyticHybridCoordinates

variable {A U B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup U] [Module F2 U]
  [AddCommGroup B] [Module F2 B] [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C]
  [Fintype ((A × U) →ₗ[F2] (B × C))] [Fintype ((B × C) →ₗ[F2] (A × U))]

/-- The original image contribution is the actual adapted fiber coefficient
used by the mixed-slice estimate. -/
theorem image_fiber_coefficient_transport (W D : Submodule F2 U) (h : IsCompl W D)
    [Fintype ((A × (W × D)) →ₗ[F2] (B × C))]
    [Fintype ((B × C) →ₗ[F2] (A × (W × D)))]
    (z : B →ₗ[F2] W) (f : ((A × U) →ₗ[F2] (B × C)) → ℝ)
    (T : (A × U) →ₗ[F2] (B × C)) :
    (∑ S : (B × C) →ₗ[F2] (A × U),
      if LinearIdentities.Hybrid S (LinearMap.range (LinearMap.inl F2 A U))
          (LinearMap.range (LinearMap.inl F2 B C)) ∧
          (LinearMap.snd F2 A U).comp (S.comp (LinearMap.inl F2 B C)) = W.subtype.comp z
      then linearCoeff (rankComponent (Module.finrank F2 (A × (W × C))) f) S *
        (linearTraceCharacter S T).re else 0) =
      adaptedFiberCoefficient z (imagePullback W D h f) (imageTranslate W D h T) := by
  rw [image_coefficient_sum_transport W D h z f T (Module.finrank F2 (A × (W × C)))]
  let weight : ((B × C) →ₗ[F2] (A × (W × D))) → ℝ := fun S =>
    (if LinearIdentities.Hybrid S (LinearMap.range (LinearMap.inl F2 A (W × D)))
      (LinearMap.range (LinearMap.inl F2 B C)) then
        linearCoeff (rankComponent (Module.finrank F2 (A × (W × C)))
          (imagePullback W D h f)) S else 0) *
      (linearTraceCharacter S (imageTranslate W D h T)).re
  have hs : (∑ S with compressBlock S = z.prod (0 : B →ₗ[F2] D), weight S) =
      adaptedFiberCoefficient z (imagePullback W D h f) (imageTranslate W D h T) := by
    exact Finset.sum_subtype
      (Finset.univ.filter fun S : (B × C) →ₗ[F2] (A × (W × D)) =>
        compressBlock S = z.prod (0 : B →ₗ[F2] D)) (by simp) weight
  rw [← hs, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hh : LinearIdentities.Hybrid S
      (LinearMap.range (LinearMap.inl F2 A (W × D)))
      (LinearMap.range (LinearMap.inl F2 B C)) <;>
    by_cases hc : compressBlock S = z.prod (0 : B →ₗ[F2] D) <;>
    simp [weight, hh, hc]

end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

/-!
# Small-component pullback under ambient coordinate equivalences

The small domain stays fixed while the ambient embedding and primal codomain
are transported together. These are exact identities for the actual Fourier
coefficients and synthesized functions; they require no analytic estimate.
-/

namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Appendix
open MaxCutGames.Inverse.KMSAnalytic

variable {E F E' F' I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup E'] [Module F2 E'] [AddCommGroup F'] [Module F2 F']
  [AddCommGroup I] [Module F2 I]

/-- Ambient coordinate pullback preserves invariance under every domain
basis change, by transporting that change through the domain equivalence. -/
theorem basisInvariant_pullback (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f) :
    KMSBasisInvariant.IsBasisInvariant
      (fun M => f (LinearEquiv.arrowCongr a b M)) := by
  intro g X
  change f (LinearEquiv.arrowCongr a b (X.comp g.toLinearMap)) =
    f (LinearEquiv.arrowCongr a b X)
  have h : LinearEquiv.arrowCongr a b (X.comp g.toLinearMap) =
      (LinearEquiv.arrowCongr a b X).comp ((a.symm.trans g).trans a).toLinearMap := by
    ext x
    change b (X (g (a.symm x))) = b (X (a.symm (a (g (a.symm x)))))
    rw [a.symm_apply_apply]
  rw [h]
  exact hf ((a.symm.trans g).trans a) (LinearEquiv.arrowCongr a b X)

private theorem surjective_comp_symm_iff_inline_KMSAnalyticHybridEnergyTransportSmall (b : F ≃ₗ[F2] F') (T : F →ₗ[F2] I) :
    Function.Surjective (T.comp b.symm.toLinearMap) ↔ Function.Surjective T := by
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h y
    exact ⟨b.symm x, hx⟩
  · intro h y
    obtain ⟨x, hx⟩ := h y
    refine ⟨b x, ?_⟩
    change T (b.symm (b x)) = y
    rw [b.symm_apply_apply, hx]

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F']
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (E' →ₗ[F2] F')] [Fintype (F' →ₗ[F2] E')]

omit [Fintype (F →ₗ[F2] E)] [Fintype (F' →ₗ[F2] E')]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
/-- Exact small Fourier coefficient transport. The embedding need not be
injective, and the observable need not be basis invariant. -/
theorem smallCoeff_pullback (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (ι : I →ₗ[F2] E) (f : (E' →ₗ[F2] F') → ℝ) (T : F →ₗ[F2] I) :
    smallCoeff ι (fun M => f (LinearEquiv.arrowCongr a b M)) T =
      smallCoeff (a.toLinearMap.comp ι) f (T.comp b.symm.toLinearMap) := by
  have hc : LinearEquiv.arrowCongr b a (ι.comp T) =
      (a.toLinearMap.comp ι).comp (T.comp b.symm.toLinearMap) := by
    ext y
    rfl
  unfold smallCoeff
  rw [surjective_comp_symm_iff_inline_KMSAnalyticHybridEnergyTransportSmall, NaturalTransport.linearCoeff_pullback, hc]

variable [FiniteDimensional F2 I]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]
  [Fintype (I →ₗ[F2] F')] [Fintype (F' →ₗ[F2] I)]

omit [Fintype (F →ₗ[F2] E)] [Fintype (F' →ₗ[F2] E')]
  [FiniteDimensional F2 E] [FiniteDimensional F2 E'] in
/-- The actual synthesized small component commutes with ambient pullback,
with the small domain fixed and the primal codomain transported by `b`. -/
theorem smallComponent_pullback (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (ι : I →ₗ[F2] E) (f : (E' →ₗ[F2] F') → ℝ) :
    smallComponent ι (fun M => f (LinearEquiv.arrowCongr a b M)) =
      fun X => smallComponent (a.toLinearMap.comp ι) f (b.toLinearMap.comp X) := by
  apply eq_of_coeff_eq
  intro T
  rw [coeff_smallComponent, smallCoeff_pullback]
  have hp (X : I →ₗ[F2] F) :
      LinearEquiv.arrowCongr (LinearEquiv.refl F2 I) b X = b.toLinearMap.comp X := by
    ext x
    rfl
  have hd : LinearEquiv.arrowCongr b (LinearEquiv.refl F2 I) T =
      T.comp b.symm.toLinearMap := by
    ext x
    rfl
  simpa only [coeff_smallComponent, hp, hd] using
    (NaturalTransport.linearCoeff_pullback (LinearEquiv.refl F2 I) b
      (smallComponent (a.toLinearMap.comp ι) f) T).symm

omit [Fintype (F →ₗ[F2] E)] [Fintype (F' →ₗ[F2] E')]
  [FiniteDimensional F2 E] [FiniteDimensional F2 E'] in
theorem smallComponent_pullback_apply (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (ι : I →ₗ[F2] E) (f : (E' →ₗ[F2] F') → ℝ) (X : I →ₗ[F2] F) :
    smallComponent ι (fun M => f (LinearEquiv.arrowCongr a b M)) X =
      smallComponent (a.toLinearMap.comp ι) f (b.toLinearMap.comp X) :=
  congrFun (smallComponent_pullback a b ι f) X

end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

end

/-!
Transport of actual small components when the ambient domain changes by a
linear equivalence. The coefficient and component identities hold for every
real function; basis invariance is separately transported when available.
-/

namespace MaxCutGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier

variable {E E' F I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup E'] [Module F2 E']
  [AddCommGroup F] [Module F2 F] [AddCommGroup I] [Module F2 I]

/-- Reindex primal matrices by changing the ambient domain. -/
def ambientPrimalEquiv (h : E ≃ₗ[F2] E') :
    (E' →ₗ[F2] F) ≃ (E →ₗ[F2] F) where
  toFun X := X.comp h.toLinearMap
  invFun X := X.comp h.symm.toLinearMap
  left_inv X := by ext x; simp
  right_inv X := by ext x; simp

theorem ambient_character_transport (h : E ≃ₗ[F2] E')
    (S : F →ₗ[F2] E) (X : E' →ₗ[F2] F) :
    linearTraceCharacter (h.toLinearMap.comp S) X =
      linearTraceCharacter S (X.comp h.toLinearMap) := by
  simp only [linearTraceCharacter_apply, linearTracePair, LinearMap.comp_assoc]

/-- The actual invariance property is independent of the ambient coordinates. -/
theorem ambient_basisInvariant_transport (h : E ≃ₗ[F2] E')
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f) :
    KMSBasisInvariant.IsBasisInvariant (fun X : E' →ₗ[F2] F =>
      f (X.comp h.toLinearMap)) := by
  intro g X
  let k : E ≃ₗ[F2] E := (h.trans g).trans h.symm
  have hc : (X.comp g.toLinearMap).comp h.toLinearMap =
      (X.comp h.toLinearMap).comp k.toLinearMap := by
    ext x
    simp [k]
  change f ((X.comp g.toLinearMap).comp h.toLinearMap) = f (X.comp h.toLinearMap)
  rw [hc]
  exact hf k (X.comp h.toLinearMap)

variable [Fintype (E →ₗ[F2] F)] [Fintype (E' →ₗ[F2] F)]

/-- Normalized Fourier coefficients are preserved by ambient reindexing. -/
theorem ambient_coeff_transport (h : E ≃ₗ[F2] E')
    (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (fun X : E' →ₗ[F2] F => f (X.comp h.toLinearMap))
      (h.toLinearMap.comp S) = linearCoeff f S := by
  unfold linearCoeff
  apply Fintype.expect_equiv (ambientPrimalEquiv h)
  intro X
  change f (X.comp h.toLinearMap) * (linearTraceCharacter (h.toLinearMap.comp S) X).re =
    f (X.comp h.toLinearMap) * (linearTraceCharacter S (X.comp h.toLinearMap)).re
  rw [ambient_character_transport]

variable [FiniteDimensional F2 E] [FiniteDimensional F2 E']
  [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (F →ₗ[F2] E)] [Fintype (F →ₗ[F2] E')]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 E'] [FiniteDimensional F2 F] [FiniteDimensional F2 I] [Fintype (F →ₗ[F2] E)] [Fintype (F →ₗ[F2] E')] [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)] in
theorem smallCoeff_ambient_transport (h : E ≃ₗ[F2] E') (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (T : F →ₗ[F2] I) :
    smallCoeff (h.toLinearMap.comp ι)
      (fun X : E' →ₗ[F2] F => f (X.comp h.toLinearMap)) T = smallCoeff ι f T := by
  unfold smallCoeff
  split_ifs
  · rw [LinearMap.comp_assoc, ambient_coeff_transport]
  · rfl

omit [FiniteDimensional F2 E] [FiniteDimensional F2 E'] [FiniteDimensional F2 F] [FiniteDimensional F2 I] [Fintype (F →ₗ[F2] E)] [Fintype (F →ₗ[F2] E')] [Fintype (I →ₗ[F2] F)] in
/-- Changing the large coordinate space does not change the actual small
function when both the injection and the input function are transported. -/
theorem smallComponent_ambient_transport (h : E ≃ₗ[F2] E') (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) :
    smallComponent (h.toLinearMap.comp ι)
      (fun X : E' →ₗ[F2] F => f (X.comp h.toLinearMap)) = smallComponent ι f := by
  unfold smallComponent
  congr 1
  funext T
  exact smallCoeff_ambient_transport h ι f T

end
end MaxCutGames.Inverse.KMSAnalytic

/-!
# Product Hybrid energy from actual mixed slices

The derivative's exact rank support is partitioned by its actual compressed
image. Each image is put in complement coordinates, and the proved coefficient
factorization bounds that contribution by an actual mixed slice. The finite
image, extension, and complementary-map counts fit the mixed denominator.
The sole analytic premise is the displayed uniform bound on actual slices.
-/

noncomputable section

namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixCharacters (linearTraceCharacter)
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Appendix MaxCutGames.Appendix.Derivatives
open KMSAnalytic KMSFourthMoment

local instance (priority := 2000) classicalSurjective {X Y : Type*} :
    DecidablePred (Function.Surjective : (X → Y) → Prop) :=
  fun g => Classical.propDecidable (Function.Surjective g)

local instance mapFintype {V W : Type*}
    [AddCommGroup V] [Module F2 V] [AddCommGroup W] [Module F2 W]
    [Fintype V] [Fintype W] : Fintype (V →ₗ[F2] W) :=
  Fintype.ofInjective (fun L : V →ₗ[F2] W => (L : V → W)) DFunLike.coe_injective

local instance submoduleFintype {V : Type*}
    [AddCommGroup V] [Module F2 V] [Fintype V] : Fintype (Submodule F2 V) :=
  Fintype.ofInjective (fun W : Submodule F2 V => (W : Set V)) SetLike.coe_injective

variable {A U B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup U] [Module F2 U]
  [AddCommGroup B] [Module F2 B] [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C]
  [Fintype A] [Fintype U] [Fintype B] [Fintype C]

/-- The actual mixed-slice hypothesis in all coordinates adapted to the
compressed image. It is a bound on `smallComponent`, with the original
function and translate transported by the explicit product equivalence. -/
def ProductMixedSliceBound (i : ℕ)
    (f : ((A × U) →ₗ[F2] (B × C)) → ℝ)
    (T : (A × U) →ₗ[F2] (B × C)) (L : ℝ) : Prop :=
  ∀ (W D : Submodule F2 U),
    Module.finrank F2 W = i - (Module.finrank F2 A + Module.finrank F2 C) →
    ∀ (hD : IsCompl W D)
      (κ : (A × (W × C)) →ₗ[F2] (A × (W × D))),
      Function.Injective κ →
      sliceEnergy (fun V : (B × C) →ₗ[F2] (W × C) =>
        (LinearMap.snd F2 W C).comp V = LinearMap.snd F2 B C)
        (partialRestrict (smallComponent κ (imagePullback W D hD f))
          (primalA (imageTranslate W D hD T))) ≤
        L / (2 : ℝ) ^ ((2 * Module.finrank F2 C +
          (i - (Module.finrank F2 A + Module.finrank F2 C))) *
            Module.finrank F2 (A × U))

/-- The selected coefficient at one ordinary product-compressed frequency. -/
def productFiberCoefficient (i : ℕ)
    (f : ((A × U) →ₗ[F2] (B × C)) → ℝ)
    (T : (A × U) →ₗ[F2] (B × C)) (Z : B →ₗ[F2] U) : ℝ :=
  ∑ S : (B × C) →ₗ[F2] (A × U),
    if LinearIdentities.Hybrid S (LinearMap.range (LinearMap.inl F2 A U))
        (LinearMap.range (LinearMap.inl F2 B C)) ∧
        (LinearMap.snd F2 A U).comp (S.comp (LinearMap.inl F2 B C)) = Z
    then linearCoeff (rankComponent i f) S * (linearTraceCharacter S T).re else 0

/-- The original coefficient wrapper agrees with the adapted coefficient
at the exact dimension of the small comparison space. -/
theorem productFiberCoefficient_imageTransport
    (W D : Submodule F2 U) (hD : IsCompl W D) (z : B →ₗ[F2] W)
    (f : ((A × U) →ₗ[F2] (B × C)) → ℝ)
    (T : (A × U) →ₗ[F2] (B × C)) (i : ℕ)
    (hi : Module.finrank F2 (A × (W × C)) = i) :
    productFiberCoefficient i f T (W.subtype.comp z) =
      adaptedFiberCoefficient z (imagePullback W D hD f) (imageTranslate W D hD T) := by
  simpa only [hi, productFiberCoefficient] using
    image_fiber_coefficient_transport W D hD z f T

/-- The exact energy identity using the product coefficient wrapper. -/
theorem product_energy_eq_filter_coefficient
    (T : (A × U) →ₗ[F2] (B × C))
    (f : ((A × U) →ₗ[F2] (B × C)) → ℝ) (i : ℕ) :
    (𝔼 N, hybridDerivative (LinearMap.range (LinearMap.inl F2 A U))
      (LinearMap.range (LinearMap.inl F2 B C)) T (rankComponent i f) N ^ 2) =
      ∑ Z : B →ₗ[F2] U with
        Module.finrank F2 Z.range = i - (Module.finrank F2 A + Module.finrank F2 C),
        productFiberCoefficient i f T Z ^ 2 := by
  have h := hybridDerivative_rankComponent_product_energy_eq_rank_fibers T f i
  convert h using 1
  unfold productFiberCoefficient
  congr 1
  ext Z
  congr 1
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> rfl

/-- One actual compressed-image contribution follows from the uniform
mixed-slice premise, retaining the exact finite-coordinate cost. -/
theorem product_image_energy_le_of_mixed
    (i : ℕ) (f : ((A × U) →ₗ[F2] (B × C)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f)
    (T : (A × U) →ₗ[F2] (B × C)) (L : ℝ)
    (hi : i ≤ Module.finrank F2 (A × U))
    (ho : Module.finrank F2 A + Module.finrank F2 C ≤ i)
    (hMixed : ProductMixedSliceBound i f T L)
    (W : RankImage F2 U (i - (Module.finrank F2 A + Module.finrank F2 C))) :
    (∑ z : {z : B →ₗ[F2] W.val // Function.Surjective z},
      productFiberCoefficient i f T (W.val.subtype.comp z.val) ^ 2) ≤
      ((2 : ℝ) ^ (Module.finrank F2 C * (Module.finrank F2 U -
        (i - (Module.finrank F2 A + Module.finrank F2 C))))) ^ 2 *
      (2 : ℝ) ^ (Module.finrank F2 C *
        (i - (Module.finrank F2 A + Module.finrank F2 C))) *
      (L / (2 : ℝ) ^ ((2 * Module.finrank F2 C +
        (i - (Module.finrank F2 A + Module.finrank F2 C))) *
        Module.finrank F2 (A × U))) := by
  let a := Module.finrank F2 A
  let b := Module.finrank F2 C
  let u := Module.finrank F2 U
  let q := i - (a + b)
  let d := u - q
  let den : ℝ := (2 : ℝ) ^ ((2 * b + q) * Module.finrank F2 (A × U))
  let v : ℝ := (2 : ℝ) ^ (b * d)
  let e : ℝ := (2 : ℝ) ^ (b * q)
  have hq : q + (a + b) = i := Nat.sub_add_cancel ho
  obtain ⟨D, hD⟩ := W.val.exists_isCompl
  have hWD : Module.finrank F2 W.val + Module.finrank F2 D = u :=
    imageCoordinates_finrank W.val D hD
  have hDdim : Module.finrank F2 D = d := by rw [W.property] at hWD; omega
  have hsmall : Module.finrank F2 (A × (W.val × C)) = i := by
    simp only [Module.finrank_prod, W.property]
    change a + (q + b) = i
    omega
  have hlarge : Module.finrank F2 (A × (W.val × D)) =
      Module.finrank F2 (A × U) := by
    simp only [Module.finrank_prod]
    rw [hWD]
  obtain ⟨κ, hκ⟩ := (finrank_le_iff_exists_linearMap
    (R := F2) (M := A × (W.val × C)) (M' := A × (W.val × D))).mp
      (by rw [hsmall, hlarge]; exact hi)
  have hm := hMixed W.val D W.property hD κ hκ
  have hbound := adapted_image_energy_le_of_mixed κ hκ
    (imagePullback W.val D hD f)
    (ambient_basisInvariant_transport (imageAmbientEquiv W.val D hD).symm f hf)
    (imageTranslate W.val D hD T) (L / den) hm
  have hco (z : B →ₗ[F2] W.val) :
      productFiberCoefficient i f T (W.val.subtype.comp z) =
        adaptedFiberCoefficient z (imagePullback W.val D hD f)
          (imageTranslate W.val D hD T) := by
    exact productFiberCoefficient_imageTransport W.val D hD z f T i hsmall
  change _ ≤ v ^ 2 * e * (L / den)
  calc
    _ = ∑ z : {z : B →ₗ[F2] W.val // Function.Surjective z},
        adaptedFiberCoefficient z.val (imagePullback W.val D hD f)
          (imageTranslate W.val D hD T) ^ 2 := by
      apply Finset.sum_congr rfl
      intro z _
      rw [hco]
    _ = ∑ z ∈ Finset.univ.filter (fun z : B →ₗ[F2] W.val => Function.Surjective z),
        adaptedFiberCoefficient z (imagePullback W.val D hD f)
          (imageTranslate W.val D hD T) ^ 2 := by
      exact (Finset.sum_subtype
        (p := fun z : B →ₗ[F2] W.val => Function.Surjective z)
        (Finset.univ.filter fun z : B →ₗ[F2] W.val => Function.Surjective z)
        (by simp) (fun z => adaptedFiberCoefficient z (imagePullback W.val D hD f)
          (imageTranslate W.val D hD T) ^ 2)).symm
    _ ≤ (Fintype.card (C →ₗ[F2] D) : ℝ) ^ 2 *
        (Fintype.card (C →ₗ[F2] W.val) : ℝ) * (L / den) := hbound
    _ = _ := by
      rw [card_linearMap_eq, card_linearMap_eq]
      simp only [Nat.cast_pow, Nat.cast_ofNat, W.property, hDdim]
      simp only [v, e, b, q, a]

/-- Actual product Hybrid derivative energy follows from the actual mixed
slice estimate. Orders above the selected rank are included automatically. -/
theorem product_hybrid_energy_le_of_mixed
    (i : ℕ) (f : ((A × U) →ₗ[F2] (B × C)) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f)
    (T : (A × U) →ₗ[F2] (B × C)) (L : ℝ) (hL : 0 ≤ L)
    (hi : i ≤ Module.finrank F2 (A × U))
    (hMixed : ProductMixedSliceBound i f T L) :
    (𝔼 N, hybridDerivative (LinearMap.range (LinearMap.inl F2 A U))
      (LinearMap.range (LinearMap.inl F2 B C)) T (rankComponent i f) N ^ 2) ≤ L := by
  by_cases ho : Module.finrank F2 A + Module.finrank F2 C ≤ i
  · let a := Module.finrank F2 A
    let b := Module.finrank F2 C
    let u := Module.finrank F2 U
    let q := i - (a + b)
    let d := u - q
    let den : ℝ := (2 : ℝ) ^ ((2 * b + q) * (a + u))
    let v : ℝ := (2 : ℝ) ^ (b * d)
    let e : ℝ := (2 : ℝ) ^ (b * q)
    have hi' : i ≤ a + u := by simpa only [Module.finrank_prod] using hi
    have ho' : a + b ≤ i := ho
    have hq : q + (a + b) = i := Nat.sub_add_cancel ho'
    have hqu : q ≤ u := by omega
    have hdim : a + u = a + q + d := by dsimp [d]; omega
    let weight : (B →ₗ[F2] U) → ℝ := fun Z => productFiberCoefficient i f T Z ^ 2
    have hEach (W : RankImage F2 U q) :
        (∑ z : {z : B →ₗ[F2] W.val // Function.Surjective z},
          weight (W.val.subtype.comp z.val)) ≤ v ^ 2 * e * (L / den) := by
      simpa only [Module.finrank_prod] using
        product_image_energy_le_of_mixed i f hf T L hi ho hMixed W
    have hcountW : (Fintype.card (RankImage F2 U q) : ℝ) ≤
        (2 : ℝ) ^ (q * (a + u - a)) := by
      have hn := card_rank_subspaces_le (U := U) q
      have hr : (Fintype.card (RankImage F2 U q) : ℝ) ≤ (2 : ℝ) ^ (q * u) := by
        exact_mod_cast hn
      simpa only [Nat.add_sub_cancel_left] using hr
    have hcount : (Fintype.card (RankImage F2 U q) : ℝ) * v ^ 2 * e ≤ den :=
      count_budget_le_of_dimension a b q d (a + u) hdim
        (Fintype.card (RankImage F2 U q)) v e (by positivity) (by positivity)
        hcountW le_rfl le_rfl
    have hden : 0 < den := by dsimp [den]; positivity
    calc
      _ = ∑ Z : B →ₗ[F2] U with Module.finrank F2 Z.range = q, weight Z :=
        product_energy_eq_filter_coefficient T f i
      _ = ∑ W : RankImage F2 U q,
          ∑ z : {z : B →ₗ[F2] W.val // Function.Surjective z},
            weight (W.val.subtype.comp z.val) := by
        rw [Finset.sum_subtype
          (p := fun z : B →ₗ[F2] U => Module.finrank F2 z.range = q)
          (Finset.univ.filter fun z : B →ₗ[F2] U => Module.finrank F2 z.range = q)
          (by simp) weight]
        calc
          _ = ∑ p : Σ W : RankImage F2 U q,
              {z : B →ₗ[F2] W.val // Function.Surjective z},
              weight (p.1.val.subtype.comp p.2.val) := by
            symm
            apply Fintype.sum_equiv
              (rankFrequencyImageEquiv (R := F2) (B := B) (U := U) q).symm
            intro p
            rfl
          _ = _ := Fintype.sum_sigma _
      _ ≤ ∑ _W : RankImage F2 U q, v ^ 2 * e * (L / den) := by
        apply Finset.sum_le_sum
        intro W _
        exact hEach W
      _ = ((Fintype.card (RankImage F2 U q) : ℝ) * v ^ 2 * e) * (L / den) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
      _ ≤ den * (L / den) :=
        mul_le_mul_of_nonneg_right hcount (div_nonneg hL hden.le)
      _ = L := mul_div_cancel₀ L (ne_of_gt hden)
  · let : Fintype ((LinearMap.range (LinearMap.inl F2 B C)) →ₗ[F2]
        ((A × U) ⧸ LinearMap.range (LinearMap.inl F2 A U))) :=
      Fintype.ofEquiv (B →ₗ[F2] U) productFrequencyEquiv.symm
    have hzero := hybridDerivative_rankComponent_eq_zero_of_lt_order
      (LinearMap.range (LinearMap.inl F2 A U))
      (LinearMap.range (LinearMap.inl F2 B C)) T f i
      (by rw [product_restriction_order]; omega)
    simpa [hzero] using hL

end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

/-!
# Exact transport of mixed small-component slices

A codomain equivalence transports the fixed primal coordinates and the
prescribed partial frequency together. The frequency reindexing is bijective,
so the actual slice energy has no multiplicity or normalization factor.
-/

namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Appendix
open MaxCutGames.Inverse.KMSAnalytic
open MaxCutGames.Inverse.KMSFourthMoment

variable {A I J F F' : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup I] [Module F2 I]
  [AddCommGroup J] [Module F2 J] [AddCommGroup F] [Module F2 F]
  [AddCommGroup F'] [Module F2 F']

/-- Transport of the fixed block and the free block commutes with the actual
partial restriction. -/
theorem partialRestrict_codomain_pullback (b : F ≃ₗ[F2] F')
    (g : ((A × I) →ₗ[F2] F') → ℝ) (u : A →ₗ[F2] F) :
    partialRestrict (fun Y => g (b.toLinearMap.comp Y)) u =
      fun X => partialRestrict g (b.toLinearMap.comp u) (b.toLinearMap.comp X) := by
  funext X
  change g (b.toLinearMap.comp (u.coprod X)) =
    g ((b.toLinearMap.comp u).coprod (b.toLinearMap.comp X))
  apply congrArg g
  apply LinearMap.ext
  intro p
  change b (u p.1 + X p.2) = b (u p.1) + b (X p.2)
  exact b.map_add _ _

private theorem arrowCongr_refl_left_apply_inline_KMSAnalyticHybridEnergyTransportSmallMixed (b : F ≃ₗ[F2] F') (X : I →ₗ[F2] F) :
    LinearEquiv.arrowCongr (LinearEquiv.refl F2 I) b X = b.toLinearMap.comp X := by
  ext x
  rfl

private theorem arrowCongr_refl_right_apply_inline_KMSAnalyticHybridEnergyTransportSmallMixed (b : F ≃ₗ[F2] F') (T : F →ₗ[F2] I) :
    LinearEquiv.arrowCongr b (LinearEquiv.refl F2 I) T =
      T.comp b.symm.toLinearMap := by
  ext x
  rfl

variable [FiniteDimensional F2 I] [FiniteDimensional F2 F] [FiniteDimensional F2 F']
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]
  [Fintype (I →ₗ[F2] F')] [Fintype (F' →ₗ[F2] I)]

omit [Fintype (F →ₗ[F2] I)] [Fintype (F' →ₗ[F2] I)]
  [FiniteDimensional F2 I] [FiniteDimensional F2 F] [FiniteDimensional F2 F'] in
/-- Exact coefficient transport for a function pulled back only in its
primal codomain. -/
theorem linearCoeff_postcomp_equiv (b : F ≃ₗ[F2] F')
    (g : (I →ₗ[F2] F') → ℝ) (T : F →ₗ[F2] I) :
    linearCoeff (fun X => g (b.toLinearMap.comp X)) T =
      linearCoeff g (T.comp b.symm.toLinearMap) := by
  simpa only [arrowCongr_refl_left_apply_inline_KMSAnalyticHybridEnergyTransportSmallMixed, arrowCongr_refl_right_apply_inline_KMSAnalyticHybridEnergyTransportSmallMixed] using
    NaturalTransport.linearCoeff_pullback (LinearEquiv.refl F2 I) b g T

omit [FiniteDimensional F2 I] [FiniteDimensional F2 F] [FiniteDimensional F2 F'] in
/-- Transport the prescribed frequency with the codomain. This identity
requires no surjectivity of the prescribed-frequency projection. -/
theorem sliceEnergy_codomain_pullback (b : F ≃ₗ[F2] F')
    (g : (I →ₗ[F2] F') → ℝ) (π : I →ₗ[F2] J) (ν : F →ₗ[F2] J) :
    sliceEnergy (fun T : F →ₗ[F2] I => π.comp T = ν)
      (fun X => g (b.toLinearMap.comp X)) =
      sliceEnergy (fun T : F' →ₗ[F2] I => π.comp T = ν.comp b.symm.toLinearMap) g := by
  unfold sliceEnergy
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Fintype.sum_equiv (LinearEquiv.arrowCongr b (LinearEquiv.refl F2 I)).toEquiv
  intro T
  have hp : π.comp (T.comp b.symm.toLinearMap) = ν.comp b.symm.toLinearMap ↔
      π.comp T = ν := by
    constructor
    · intro h
      ext x
      have hx := congrArg (fun M : F' →ₗ[F2] J => M (b x)) h
      simpa using hx
    · intro h
      rw [← LinearMap.comp_assoc, h]
  simp only [LinearEquiv.coe_toEquiv, arrowCongr_refl_right_apply_inline_KMSAnalyticHybridEnergyTransportSmallMixed,
    linearCoeff_postcomp_equiv, hp]

variable {E E' : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup E'] [Module F2 E']
  [FiniteDimensional F2 E] [FiniteDimensional F2 E'] [FiniteDimensional F2 A]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (E' →ₗ[F2] F')] [Fintype (F' →ₗ[F2] E')]
  [Fintype ((A × I) →ₗ[F2] F)] [Fintype (F →ₗ[F2] (A × I))]
  [Fintype ((A × I) →ₗ[F2] F')] [Fintype (F' →ₗ[F2] (A × I))]

omit [Fintype (F →ₗ[F2] E)] [Fintype (F' →ₗ[F2] E')]
  [FiniteDimensional F2 E] [FiniteDimensional F2 E'] in
/-- The actual mixed small-component energy is invariant when its ambient
coordinates, embedding, fixed primal map, and prescribed frequency are all
transported together. -/
theorem sliceEnergy_partialRestrict_smallComponent_pullback
    (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (ι : (A × I) →ₗ[F2] E) (f : (E' →ₗ[F2] F') → ℝ)
    (π : I →ₗ[F2] J) (ν : F →ₗ[F2] J) (u : A →ₗ[F2] F) :
    sliceEnergy (fun T : F →ₗ[F2] I => π.comp T = ν)
      (partialRestrict (smallComponent ι
        (fun M => f (LinearEquiv.arrowCongr a b M))) u) =
      sliceEnergy (fun T : F' →ₗ[F2] I => π.comp T = ν.comp b.symm.toLinearMap)
        (partialRestrict (smallComponent (a.toLinearMap.comp ι) f)
          (b.toLinearMap.comp u)) := by
  rw [smallComponent_pullback, partialRestrict_codomain_pullback]
  exact sliceEnergy_codomain_pullback b _ π ν

end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

end

end OAI

import Mathlib
import OAI.Computability.DirectedFeedback.Probability.KMSFourthMomentMixedRestriction
import OAI.Computability.DirectedFeedback.Games.NaturalTransport

namespace OAI

noncomputable section
namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixCharacters (linearTraceCharacter)
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Appendix
open KMSAnalytic KMSAnalyticHybridCoordinates

variable {A U B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup U] [Module F2 U]
  [AddCommGroup B] [Module F2 B] [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C]
  [Fintype ((A × U) →ₗ[F2] (B × C))] [Fintype ((B × C) →ₗ[F2] (A × U))]

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

end DFVSGames.Inverse.KMSAnalyticHybridEnergy

end

noncomputable section

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Appendix
open DFVSGames.Inverse.KMSAnalytic

variable {E F E' F' I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup E'] [Module F2 E'] [AddCommGroup F'] [Module F2 F']
  [AddCommGroup I] [Module F2 I]

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

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F']
  [Fintype (F →ₗ[F2] E)] [Fintype (F' →ₗ[F2] E')] in

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

omit [FiniteDimensional F2 E] [FiniteDimensional F2 E']
  [Fintype (F →ₗ[F2] E)] [Fintype (F' →ₗ[F2] E')] in
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

omit [FiniteDimensional F2 E] [FiniteDimensional F2 E']
  [Fintype (F →ₗ[F2] E)] [Fintype (F' →ₗ[F2] E')] in
theorem smallComponent_pullback_apply (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (ι : I →ₗ[F2] E) (f : (E' →ₗ[F2] F') → ℝ) (X : I →ₗ[F2] F) :
    smallComponent ι (fun M => f (LinearEquiv.arrowCongr a b M)) X =
      smallComponent (a.toLinearMap.comp ι) f (b.toLinearMap.comp X) :=
  congrFun (smallComponent_pullback a b ι f) X

end DFVSGames.Inverse.KMSAnalyticHybridEnergy

end

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Fourier.MatrixFourier

variable {E E' F I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup E'] [Module F2 E']
  [AddCommGroup F] [Module F2 F] [AddCommGroup I] [Module F2 I]

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

theorem smallComponent_ambient_transport (h : E ≃ₗ[F2] E') (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) :
    smallComponent (h.toLinearMap.comp ι)
      (fun X : E' →ₗ[F2] F => f (X.comp h.toLinearMap)) = smallComponent ι f := by
  unfold smallComponent
  congr 1
  funext T
  exact smallCoeff_ambient_transport h ι f T

end
end DFVSGames.Inverse.KMSAnalytic

noncomputable section

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixCharacters (linearTraceCharacter)
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Appendix DFVSGames.Appendix.Derivatives
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

def productFiberCoefficient (i : ℕ)
    (f : ((A × U) →ₗ[F2] (B × C)) → ℝ)
    (T : (A × U) →ₗ[F2] (B × C)) (Z : B →ₗ[F2] U) : ℝ :=
  ∑ S : (B × C) →ₗ[F2] (A × U),
    if LinearIdentities.Hybrid S (LinearMap.range (LinearMap.inl F2 A U))
        (LinearMap.range (LinearMap.inl F2 B C)) ∧
        (LinearMap.snd F2 A U).comp (S.comp (LinearMap.inl F2 B C)) = Z
    then linearCoeff (rankComponent i f) S * (linearTraceCharacter S T).re else 0

theorem productFiberCoefficient_imageTransport
    (W D : Submodule F2 U) (hD : IsCompl W D) (z : B →ₗ[F2] W)
    (f : ((A × U) →ₗ[F2] (B × C)) → ℝ)
    (T : (A × U) →ₗ[F2] (B × C)) (i : ℕ)
    (hi : Module.finrank F2 (A × (W × C)) = i) :
    productFiberCoefficient i f T (W.subtype.comp z) =
      adaptedFiberCoefficient z (imagePullback W D hD f) (imageTranslate W D hD T) := by
  simpa only [hi, productFiberCoefficient] using
    image_fiber_coefficient_transport W D hD z f T

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

end DFVSGames.Inverse.KMSAnalyticHybridEnergy

end

noncomputable section

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Appendix
open DFVSGames.Inverse.KMSAnalytic
open DFVSGames.Inverse.KMSFourthMoment

variable {A I J F F' : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup I] [Module F2 I]
  [AddCommGroup J] [Module F2 J] [AddCommGroup F] [Module F2 F]
  [AddCommGroup F'] [Module F2 F']

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

omit [FiniteDimensional F2 I] [FiniteDimensional F2 F] [FiniteDimensional F2 F']
  [Fintype (F →ₗ[F2] I)] [Fintype (F' →ₗ[F2] I)] in

theorem linearCoeff_postcomp_equiv (b : F ≃ₗ[F2] F')
    (g : (I →ₗ[F2] F') → ℝ) (T : F →ₗ[F2] I) :
    linearCoeff (fun X => g (b.toLinearMap.comp X)) T =
      linearCoeff g (T.comp b.symm.toLinearMap) := by
  simpa only [arrowCongr_refl_left_apply_inline_KMSAnalyticHybridEnergyTransportSmallMixed, arrowCongr_refl_right_apply_inline_KMSAnalyticHybridEnergyTransportSmallMixed] using
    NaturalTransport.linearCoeff_pullback (LinearEquiv.refl F2 I) b g T

omit [FiniteDimensional F2 I] [FiniteDimensional F2 F] [FiniteDimensional F2 F'] in
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

omit [FiniteDimensional F2 E] [FiniteDimensional F2 E']
  [Fintype (F →ₗ[F2] E)] [Fintype (F' →ₗ[F2] E')] in
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

end DFVSGames.Inverse.KMSAnalyticHybridEnergy

end

namespace DFVSGames.Inverse.KMSFourthMoment

noncomputable section
open scoped Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Inverse.KMSAnalytic

variable {A0 A I F : Type*}
  [AddCommGroup A0] [Module F2 A0]
  [AddCommGroup A] [Module F2 A]
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup F] [Module F2 F]

def pointShuffle (e : (A0 × F2) ≃ₗ[F2] A) :
    ((A0 × I) × F2) ≃ₗ[F2] (A × I) where
  toFun p := (e (p.1.1, p.2), p.1.2)
  invFun p := (((e.symm p.1).1, p.2), (e.symm p.1).2)
  left_inv p := by
    rcases p with ⟨⟨u, v⟩, c⟩
    simp
  right_inv p := by
    rcases p with ⟨u, v⟩
    simp
  map_add' p q := by
    apply Prod.ext
    · change e (p.1.1 + q.1.1, p.2 + q.2) =
        e (p.1.1, p.2) + e (q.1.1, q.2)
      exact map_add e (p.1.1, p.2) (q.1.1, q.2)
    · rfl
  map_smul' c p := by
    apply Prod.ext
    · change e (c • p.1.1, c • p.2) = c • e (p.1.1, p.2)
      exact map_smul e c (p.1.1, p.2)
    · rfl

@[simp] theorem pointShuffle_apply (e : (A0 × F2) ≃ₗ[F2] A)
    (u : A0) (v : I) (c : F2) :
    pointShuffle (I := I) e ((u, v), c) = (e (u, c), v) := rfl

@[simp] theorem pointShuffle_symm_apply (e : (A0 × F2) ≃ₗ[F2] A)
    (u : A) (v : I) :
    (pointShuffle (I := I) e).symm (u, v) =
      (((e.symm u).1, v), (e.symm u).2) := rfl

theorem coprod_comp_pointShuffle (e : (A0 × F2) ≃ₗ[F2] A)
    (a : A →ₗ[F2] F) (X : I →ₗ[F2] F) :
    (a.coprod X).comp (pointShuffle e).toLinearMap =
      pointAppend (((a.comp e.toLinearMap).comp (LinearMap.inl F2 A0 F2)).coprod X)
        (a (e (0, 1))) := by
  apply LinearMap.ext
  intro p
  rcases p with ⟨⟨u, v⟩, c⟩
  change a (e (u, c)) + X v =
    (a (e (u, 0)) + X v) + c • a (e (0, 1))
  have hp : (u, c) = (u, (0 : F2)) + c • ((0 : A0), (1 : F2)) := by
    simp
  have ha : a (e (u, c)) = a (e (u, 0)) + c • a (e (0, 1)) := by
    rw [hp]
    simp only [map_add, map_smul]
  rw [ha]
  abel

def pointShuffleTransport (e : (A0 × F2) ≃ₗ[F2] A)
    (f : ((A × I) →ₗ[F2] F) → ℝ) :
    (((A0 × I) × F2) →ₗ[F2] F) → ℝ :=
  fun Y => f (Y.comp (pointShuffle e).symm.toLinearMap)

theorem partialRestrict_pointRestrict_pointShuffleTransport
    (e : (A0 × F2) ≃ₗ[F2] A)
    (f : ((A × I) →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F) :
    partialRestrict
      (pointRestrict (pointShuffleTransport e f) (a (e (0, 1))))
      ((a.comp e.toLinearMap).comp (LinearMap.inl F2 A0 F2)) =
        partialRestrict f a := by
  funext X
  change f ((pointAppend
    (((a.comp e.toLinearMap).comp (LinearMap.inl F2 A0 F2)).coprod X)
    (a (e (0, 1)))).comp (pointShuffle e).symm.toLinearMap) = f (a.coprod X)
  rw [← coprod_comp_pointShuffle]
  congr 1
  apply LinearMap.ext
  intro p
  change (a.coprod X) ((pointShuffle e) ((pointShuffle e).symm p)) = (a.coprod X) p
  rw [LinearEquiv.apply_symm_apply]

end
end DFVSGames.Inverse.KMSFourthMoment

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Inverse.KMSBasisInvariant

variable {E F I J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I] [AddCommGroup J] [Module F2 J]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]

def fixedFrequencyEnergy (ι : I →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ)
    (π : I →ₗ[F2] J) (A : F →ₗ[F2] J) : ℝ :=
  ∑ T with π.comp T = A, smallCoeff ι f T ^ 2

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I] [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] in
theorem fixedFrequencyEnergy_nonneg (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (π : I →ₗ[F2] J) (A : F →ₗ[F2] J) :
    0 ≤ fixedFrequencyEnergy ι f π A :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I] [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] in

theorem fixedFrequencyEnergy_eq (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (π : I →ₗ[F2] J) (A : F →ₗ[F2] J) :
    fixedFrequencyEnergy ι f π A =
      ∑ T ∈ Finset.univ.filter (fun T : F →ₗ[F2] I => π.comp T = A ∧ Function.Surjective T),
        linearCoeff f (ι.comp T) ^ 2 := by
  unfold fixedFrequencyEnergy
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hT : Function.Surjective T <;> by_cases hA : π.comp T = A <;>
    simp [smallCoeff, hT, hA]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I] [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] in

theorem fixedFrequencyEnergy_eq_zero_of_not_surjective
    (ι : I →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ)
    (π : I →ₗ[F2] J) (hπ : Function.Surjective π)
    (A : F →ₗ[F2] J) (hA : ¬ Function.Surjective A) :
    fixedFrequencyEnergy ι f π A = 0 := by
  rw [fixedFrequencyEnergy_eq]
  apply Finset.sum_eq_zero
  intro T hT
  have ht := (Finset.mem_filter.mp hT).2
  exact (hA (ht.1 ▸ hπ.comp ht.2)).elim

omit [FiniteDimensional F2 E] [Fintype (F →ₗ[F2] E)] in

theorem fixedFrequencyEnergy_le (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (π : I →ₗ[F2] J) (A : F →ₗ[F2] J) :
    fixedFrequencyEnergy ι f π A ≤ 𝔼 X, smallComponent ι f X ^ 2 := by
  rw [smallComponent, synthesis_energy]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => sq_nonneg _)

omit [FiniteDimensional F2 E] [Fintype (F →ₗ[F2] E)] in

theorem fixedFrequencyEnergy_zero (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) :
    fixedFrequencyEnergy ι f (0 : I →ₗ[F2] J) 0 =
      𝔼 X, smallComponent ι f X ^ 2 := by
  rw [smallComponent, synthesis_energy]
  simp [fixedFrequencyEnergy]

omit [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (F →ₗ[F2] E)] [Fintype (I →ₗ[F2] F)] in
theorem fixedFrequencyEnergy_eq_of_basisInvariant (ι κ : I →ₗ[F2] E)
    (hι : Function.Injective ι) (hκ : Function.Injective κ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : IsBasisInvariant f)
    (π : I →ₗ[F2] J) (A : F →ₗ[F2] J) :
    fixedFrequencyEnergy ι f π A = fixedFrequencyEnergy κ f π A := by
  unfold fixedFrequencyEnergy
  rw [smallCoeff_eq_of_basisInvariant ι κ hι hκ f hf]

end
end DFVSGames.Inverse.KMSAnalytic

end OAI

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
import OAI.Computability.UniqueGames.Analysis.MatrixCharactersLemmas
import OAI.Computability.UniqueGames.Inverse.KMSAffineRestrictionPresentationLemmas
import OAI.Computability.UniqueGames.Inverse.KMSAnalyticHybridEnergyImageTransportCoreLemmas
import OAI.Computability.UniqueGames.Inverse.KMSBasisComparisonPseudorandomTupleMapLemmas

namespace OAI

section

/-!
The frequency dichotomy behind the KMS point-restriction recursion.
A row appended to a surjective frequency is either independent, or is the
unique pullback of a functional on the smaller frequency space.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters

variable {E F J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup J] [Module F2 J]

/-- Append the primal value at the last coordinate. -/
def pointAppend (X : E →ₗ[F2] F) (a : F) : (E × F2) →ₗ[F2] F :=
  X.coprod (LinearMap.toSpanSingleton F2 F a)

@[simp] theorem pointAppend_apply (X : E →ₗ[F2] F) (a : F) (x : E) (c : F2) :
    pointAppend X a (x, c) = X x + c • a := rfl

/-- Fix one primal column, with no averaging or normalization. -/
def pointRestrict (f : ((E × F2) →ₗ[F2] F) → ℝ) (a : F) :
    (E →ₗ[F2] F) → ℝ := fun X => f (pointAppend X a)

/-- Extend an injection while retaining the newly fixed coordinate. -/
def pointLift (ι : J →ₗ[F2] E) : (J × F2) →ₗ[F2] (E × F2) :=
  ι.prodMap LinearMap.id

/-- The lower-dimensional embedding into the old coordinates. -/
def pointPad (ι : J →ₗ[F2] E) : J →ₗ[F2] (E × F2) :=
  ι.prod 0

theorem pointLift_injective (ι : J →ₗ[F2] E) (hι : Function.Injective ι) :
    Function.Injective (pointLift ι) := by
  rintro ⟨x, c⟩ ⟨y, d⟩ h
  have hxy : ι x = ι y := congrArg (fun z : E × F2 => z.1) h
  have hcd : c = d := congrArg (fun z : E × F2 => z.2) h
  exact Prod.ext (hι hxy) hcd

theorem pointPad_injective (ι : J →ₗ[F2] E) (hι : Function.Injective ι) :
    Function.Injective (pointPad ι) := by
  intro x y h
  exact hι (congrArg Prod.fst h)

theorem pointLift_comp_prod (ι : J →ₗ[F2] E) (T : F →ₗ[F2] J)
    (ell : F →ₗ[F2] F2) :
    (pointLift ι).comp (T.prod ell) = (ι.comp T).prod ell := by
  ext x <;> rfl

theorem pointPad_comp (ι : J →ₗ[F2] E) (T : F →ₗ[F2] J) :
    (pointPad ι).comp T = (ι.comp T).prod 0 := rfl

/-- A non-surjective appended row vanishes on the kernel of a surjective
base frequency; the proof explicitly constructs a preimage otherwise. -/
theorem ker_le_of_not_surjective_prod (T : F →ₗ[F2] J)
    (hT : Function.Surjective T) (ell : F →ₗ[F2] F2)
    (h : ¬ Function.Surjective (T.prod ell)) : T.ker ≤ ell.ker := by
  intro w hw
  change ell w = 0
  by_contra hn
  have hwT : T w = 0 := hw
  have hwell : ell w = 1 :=
    (UniqueGamesTheorem.Integration.BinaryLinear.scalar_cases (ell w)).resolve_left hn
  apply h
  rintro ⟨y, c⟩
  obtain ⟨x, hx⟩ := hT y
  refine ⟨x + (c - ell x) • w, ?_⟩
  apply Prod.ext
  · change T (x + (c - ell x) • w) = y
    simp [hx, hwT]
  · change ell (x + (c - ell x) • w) = c
    simp [hwell]

/-- Exact factorization, including uniqueness, of every dependent row. -/
theorem not_surjective_prod_iff (T : F →ₗ[F2] J)
    (hT : Function.Surjective T) (ell : F →ₗ[F2] F2) :
    ¬ Function.Surjective (T.prod ell) ↔
      ∃! φ : J →ₗ[F2] F2, φ.comp T = ell := by
  constructor
  · intro h
    let φ := (T.ker.liftQ ell (ker_le_of_not_surjective_prod T hT ell h)).comp
      (T.quotKerEquivOfSurjective hT).symm.toLinearMap
    have hφ : φ.comp T = ell := by
      ext x
      simp [φ]
    refine ⟨φ, hφ, ?_⟩
    intro ψ hψ
    ext y
    obtain ⟨x, rfl⟩ := hT y
    exact (congrArg (fun L : F →ₗ[F2] F2 => L x) hψ).trans
      (congrArg (fun L : F →ₗ[F2] F2 => L x) hφ).symm
  · rintro ⟨φ, hφ, _⟩ hsurj
    obtain ⟨x, hx⟩ := hsurj (0, 1)
    have hTx : T x = 0 := congrArg Prod.fst hx
    have hellx : ell x = 1 := congrArg Prod.snd hx
    have he := congrArg (fun L : F →ₗ[F2] F2 => L x) hφ
    simp only [LinearMap.comp_apply, hTx, map_zero, hellx] at he
    exact zero_ne_one he

theorem surjective_of_surjective_prod (T : F →ₗ[F2] J)
    (ell : F →ₗ[F2] F2) (h : Function.Surjective (T.prod ell)) :
    Function.Surjective T := by
  intro y
  obtain ⟨x, hx⟩ := h (y, 0)
  exact ⟨x, congrArg Prod.fst hx⟩

/-- Pullback along a surjection parametrizes the dependent rows exactly. -/
def dependentRowEquiv (T : F →ₗ[F2] J) (hT : Function.Surjective T) :
    (J →ₗ[F2] F2) ≃ {ell : F →ₗ[F2] F2 // ¬ Function.Surjective (T.prod ell)} where
  toFun φ := ⟨φ.comp T, (not_surjective_prod_iff T hT _).mpr
    ⟨φ, rfl, fun ψ hψ => by
      ext y
      obtain ⟨x, rfl⟩ := hT y
      exact congrArg (fun L : F →ₗ[F2] F2 => L x) hψ⟩⟩
  invFun ell := Classical.choose ((not_surjective_prod_iff T hT ell.val).mp ell.property)
  left_inv φ := by
    exact (Classical.choose_spec ((not_surjective_prod_iff T hT (φ.comp T)).mp
      ((not_surjective_prod_iff T hT _).mpr
        ⟨φ, rfl, fun ψ hψ => by
          ext y
          obtain ⟨x, rfl⟩ := hT y
          exact congrArg (fun L : F →ₗ[F2] F2 => L x) hψ⟩))).2 φ rfl |>.symm
  right_inv ell := by
    apply Subtype.ext
    exact (Classical.choose_spec
      ((not_surjective_prod_iff T hT ell.val).mp ell.property)).1

/-- Dependent extension preserves the base kernel. -/
theorem ker_prod_pullback (T : F →ₗ[F2] J) (φ : J →ₗ[F2] F2) :
    (T.prod (φ.comp T)).ker = T.ker := by
  ext x
  change (T x, φ (T x)) = (0, 0) ↔ T x = 0
  constructor
  · exact fun h => congrArg Prod.fst h
  · intro h
    simp [h]

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-!
Exact Fourier merging when one primal column is fixed. All frequency sums
are unnormalized; the primal Fourier coefficient uses normalized expectation.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]

/-- Splitting the last frequency row is an exact bijection. -/
def frequencyProdEquiv : ((F →ₗ[F2] E) × (F →ₗ[F2] F2)) ≃
    (F →ₗ[F2] (E × F2)) where
  toFun p := p.1.prod p.2
  invFun S := ((LinearMap.fst F2 E F2).comp S,
    (LinearMap.snd F2 E F2).comp S)
  left_inv _ := rfl
  right_inv _ := rfl

theorem sum_frequency_prod {A : Type*} [AddCommMonoid A]
    [Fintype (F →ₗ[F2] E)] [Fintype (F →ₗ[F2] F2)]
    [Fintype (F →ₗ[F2] (E × F2))]
    (g : (F →ₗ[F2] (E × F2)) → A) :
    ∑ S, g S = ∑ T : F →ₗ[F2] E, ∑ ell : F →ₗ[F2] F2, g (T.prod ell) := by
  rw [← frequencyProdEquiv.sum_comp g, Fintype.sum_prod_type]
  rfl

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 E] in
theorem tracePair_pointAppend (T : F →ₗ[F2] E) (ell : F →ₗ[F2] F2)
    (X : E →ₗ[F2] F) (a : F) :
    linearTracePair (pointAppend X a) (T.prod ell) =
      linearTracePair X T + ell a := by
  have hc : (pointAppend X a).comp (T.prod ell) =
      X.comp T + ell.smulRight a := by
    ext x
    rfl
  simp only [linearTracePair, hc, map_add, LinearMap.trace_smulRight]

omit [FiniteDimensional F2 E] in
theorem character_pointAppend (T : F →ₗ[F2] E) (ell : F →ₗ[F2] F2)
    (X : E →ₗ[F2] F) (a : F) :
    (linearTraceCharacter (T.prod ell) (pointAppend X a)).re =
      (linearTraceCharacter T X).re * (binarySign (ell a)).re := by
  simp [linearTraceCharacter_apply, tracePair_pointAppend, binarySign_add,
    Complex.mul_re]

omit [FiniteDimensional F2 E] in
theorem tracePair_pointShift (T : F →ₗ[F2] E) (φ : E →ₗ[F2] F2)
    (X : E →ₗ[F2] F) (a : F) :
    linearTracePair (X + φ.smulRight a) T = linearTracePair X T + φ (T a) := by
  have hc : (X + φ.smulRight a).comp T =
      X.comp T + (φ.comp T).smulRight a := by
    ext x
    rfl
  simp only [linearTracePair, hc, map_add, LinearMap.trace_smulRight,
    LinearMap.comp_apply]

omit [FiniteDimensional F2 E] in
theorem character_pointShift (T : F →ₗ[F2] E) (φ : E →ₗ[F2] F2)
    (X : E →ₗ[F2] F) (a : F) :
    (linearTraceCharacter T (X + φ.smulRight a)).re =
      (linearTraceCharacter T X).re * (binarySign (φ (T a))).re := by
  simp [linearTraceCharacter_apply, tracePair_pointShift, binarySign_add,
    Complex.mul_re]

variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype ((E × F2) →ₗ[F2] F)] [Fintype (F →ₗ[F2] (E × F2))]
  [Fintype (F →ₗ[F2] F2)]

omit [Fintype (E →ₗ[F2] F)] in
/-- Fixing a primal column merges exactly its dual frequency row. -/
theorem pointRestrict_eq_synthesis (f : ((E × F2) →ₗ[F2] F) → ℝ) (a : F) :
    pointRestrict f a = synthesis (fun T : F →ₗ[F2] E =>
      ∑ ell : F →ₗ[F2] F2, linearCoeff f (T.prod ell) * (binarySign (ell a)).re) := by
  funext X
  change f (pointAppend X a) = _
  rw [← linear_fourier_inversion f (pointAppend X a), sum_frequency_prod]
  simp only [synthesis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro T _
  apply Finset.sum_congr rfl
  intro ell _
  rw [character_pointAppend]
  ring

theorem coeff_pointRestrict (f : ((E × F2) →ₗ[F2] F) → ℝ) (a : F)
    (T : F →ₗ[F2] E) :
    linearCoeff (pointRestrict f a) T =
      ∑ ell : F →ₗ[F2] F2, linearCoeff f (T.prod ell) * (binarySign (ell a)).re := by
  rw [pointRestrict_eq_synthesis, coeff_synthesis]

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-!
Point restrictions inherit basis invariance in the remaining coordinates.
Translations split into a shift of the fixed point and a translation of the
remaining matrix; both identities are exact, with no probability loss.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]

theorem pointAppend_comp_basis (X : E →ₗ[F2] F) (a : F) (g : E ≃ₗ[F2] E) :
    pointAppend (X.comp g.toLinearMap) a =
      (pointAppend X a).comp (g.prodCongr (LinearEquiv.refl F2 F2)).toLinearMap := by
  apply LinearMap.ext
  intro x
  rfl

/-- Fixing a column preserves invariance under changes of the other columns. -/
theorem pointRestrict_invariant (f : ((E × F2) →ₗ[F2] F) → ℝ)
    (hf : KMSBasisInvariant.IsBasisInvariant f) (a : F) :
    KMSBasisInvariant.IsBasisInvariant (pointRestrict f a) := by
  intro g X
  change f (pointAppend (X.comp g.toLinearMap) a) = f (pointAppend X a)
  rw [pointAppend_comp_basis]
  exact hf (g.prodCongr (LinearEquiv.refl F2 F2)) (pointAppend X a)

theorem pointAppend_add (X : E →ₗ[F2] F) (a : F)
    (Z : (E × F2) →ₗ[F2] F) :
    pointAppend X a + Z =
      pointAppend (X + Z.comp (LinearMap.inl F2 E F2)) (a + Z (0, 1)) := by
  have hZ (x : E) (c : F2) : Z (x, c) = Z (x, 0) + c • Z (0, 1) := by
    calc
      Z (x, c) = Z ((x, 0) + c • (0, 1)) := by simp
      _ = Z (x, 0) + c • Z (0, 1) := by rw [map_add, map_smul]
  apply LinearMap.ext
  intro p
  rcases p with ⟨x, c⟩
  simp only [LinearMap.add_apply, pointAppend_apply, LinearMap.comp_apply,
    LinearMap.inl_apply, smul_add]
  rw [hZ]
  abel

/-- A translation of the full matrix merely translates the remaining
coordinates and shifts the fixed primal value. -/
theorem pointRestrict_translate (f : ((E × F2) →ₗ[F2] F) → ℝ)
    (Z : (E × F2) →ₗ[F2] F) (a : F) :
    pointRestrict (fun Y => f (Y + Z)) a =
      fun X => pointRestrict f (a + Z (0, 1))
        (X + Z.comp (LinearMap.inl F2 E F2)) := by
  funext X
  change f (pointAppend X a + Z) = _
  rw [pointAppend_add]
  rfl

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-!
A transparent local squared-density hypothesis for the new KMS point and
character inductions. The sampled maps are actual affine restrictions,
presented by a surjective domain quotient and an injective codomain map.
No Fourier, hybrid-derivative, rank-level, or inverse estimate is included.
The Grassmann application discharges this predicate from its actual local
density bounds; the analytic induction must still be proved separately.
-/

namespace UniqueGamesTheorem.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Inverse.KMSAnalytic

universe u v
variable {E : Type u} {F : Type v}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]

/-- All affine restrictions with at most r prescribed input/output dimensions
have normalized squared density at most ε. The dimension sum avoids any
truncated-subtraction ambiguity. -/
def AffineDensityBound (r : ℕ) (ε : ℝ) (f : (E →ₗ[F2] F) → ℝ) : Prop :=
  ∀ (D : Type u) [AddCommGroup D] [Module F2 D] [FiniteDimensional F2 D]
    (C : Type v) [AddCommGroup C] [Module F2 C] [FiniteDimensional F2 C]
    [Fintype (D →ₗ[F2] C)],
    ∀ L : E →ₗ[F2] D, Function.Surjective L →
    ∀ J : C →ₗ[F2] F, Function.Injective J →
    ∀ T : E →ₗ[F2] F,
      Module.finrank F2 E + Module.finrank F2 F ≤
        Module.finrank F2 D + Module.finrank F2 C + r →
      (𝔼 X : D →ₗ[F2] C, f (T + J.comp (X.comp L)) ^ 2) ≤ ε

/-- A stronger restriction budget supplies every smaller budget. -/
theorem AffineDensityBound.mono {r s : ℕ} (hrs : r ≤ s) (ε : ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : AffineDensityBound s ε f) :
    AffineDensityBound r ε f := by
  intro D _ _ _ C _ _ _ _ L hL J hJ T hdim
  exact hf D C L hL J hJ T (by omega)

/-- The homogeneous output restriction required for Lemma 3.19 is an actual
special case, using the identity domain quotient and zero affine center. -/
theorem AffineDensityBound.homogeneous [FiniteDimensional F2 E]
    (r : ℕ) (ε : ℝ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : AffineDensityBound r ε f) : HomogeneousRestrictionBound r ε f := by
  intro C _ _ _ _ J hJ hdim
  have h := hf E C (LinearMap.id : E →ₗ[F2] E) Function.surjective_id
    J hJ 0 (by omega)
  simpa using h

/-- Fixing one additional primal column consumes exactly one dimension of
local-density budget. Its prescribed value is arbitrary, including zero. -/
theorem AffineDensityBound.pointRestrict [FiniteDimensional F2 E]
    (r : ℕ) (ε : ℝ) (f : ((E × F2) →ₗ[F2] F) → ℝ)
    (hf : AffineDensityBound (r + 1) ε f) (a : F) :
    AffineDensityBound r ε (pointRestrict f a) := by
  intro D _ _ _ C _ _ _ _ L hL J hJ T hdim
  let L' : (E × F2) →ₗ[F2] D := L.comp (LinearMap.fst F2 E F2)
  have hL' : Function.Surjective L' := by
    intro y
    obtain ⟨x, hx⟩ := hL y
    exact ⟨(x, 0), hx⟩
  have hdim' : Module.finrank F2 (E × F2) + Module.finrank F2 F ≤
      Module.finrank F2 D + Module.finrank F2 C + (r + 1) := by
    rw [Module.finrank_prod, Module.finrank_self]
    omega
  have he (X : D →ₗ[F2] C) :
      pointAppend (T + J.comp (X.comp L)) a =
        pointAppend T a + J.comp (X.comp L') := by
    apply LinearMap.ext
    intro p
    rcases p with ⟨x, c⟩
    simp only [pointAppend_apply, LinearMap.add_apply, LinearMap.comp_apply,
      L', LinearMap.fst_apply]
    abel
  have h := hf D C L' hL' J hJ (pointAppend T a) hdim'
  simpa only [KMSAnalytic.pointRestrict, he] using h

end
end UniqueGamesTheorem.Inverse.KMSFourthMoment

end

section

/-! The actual Grassmann local-density hypothesis discharges the affine
squared-density predicate used by the new KMS point/character inductions. -/

namespace UniqueGamesTheorem.Inverse.KMSAffineRestriction
noncomputable section
open scoped BigOperators
open KMS KMSBasisComparison KMSBasisComparisonPseudorandom
open UniqueGamesTheorem.Fourier.MatrixRestrictions

/-- This supplies the local-density input of the genuine analytic induction
from the actual lifted Grassmann indicator, with the exact order-two loss. -/
theorem lifted_affineDensityBound {n ell d : ℕ} {ε : ℝ}
    (S : Finset (Vertex n ell)) (hS : GrassmannPseudorandom S (2 * d) ε)
    (hε : 0 ≤ ε) : KMSFourthMoment.AffineDensityBound d ε (liftedIndicator S) := by
  intro D _ _ _ C _ _ _ _ L hL J hJ T hdim
  calc
    (𝔼 X : D →ₗ[F2] C, liftedIndicator S (T + J.comp (X.comp L)) ^ 2) =
        𝔼 A : Parameter L.ker J.range,
          (restrict (liftedIndicator S) L.ker J.range T A) ^ 2 :=
      KMSAffineRestrictionPresentation.expect_presentation_sq L hL J hJ T _
    _ ≤ ε := affine_squared_expect_bound S hS hε L.ker J.range T
      (KMSAffineRestrictionPresentation.order_le_of_dimensions L hL J hJ d hdim)

end
end UniqueGamesTheorem.Inverse.KMSAffineRestriction

end

section

/-!
# Tuple pseudorandomness controls the actual affine squared density

This is the input conversion needed by the ordered-basis expansion theorem.
It starts directly from its tuple pseudorandomness assumption. All affine
intercepts and the full uniform parameter law are preserved by the checked
adapted-complement, split, and presentation equivalences.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparisonAffineDensity

noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison KMSBasisComparisonPseudorandom
open KMSAffineRestriction KMSAffineRestrictionSplit
open UniqueGamesTheorem.Fourier.MatrixRestrictions

variable {n ell q t r : ℕ} {ε : ℝ}

/-- The tuple hypothesis bounds the lift in every domain basis: the lift
depends only on the range, which is the span of the same prescribed tuple. -/
theorem lifted_expect_in_basis_of_tuple (S : Finset (Vertex n ell))
    (hS : TuplePseudorandom S r ε)
    (b : Module.Basis (Fin q ⊕ Fin t) F2 (Ambient ell))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (hbudget : q + (n - Module.finrank F2 W) ≤ r) :
    (𝔼 z : Fin t → W, liftedIndicator S (b.constr F2 (joinedTuple Q W z))) ≤ ε := by
  have hdim : ell = q + t := by
    simpa [KMS.Ambient] using Module.finrank_eq_card_basis b
  subst ell
  have hc : restrictedLiftDensity S Q W ≤ ε := hS q t rfl Q W hbudget
  rw [restrictedLiftDensity_eq_expect] at hc
  convert hc using 1
  apply Finset.expect_congr rfl
  intro z _
  unfold liftedIndicator InLift
  rw [b.constr_range F2, tupleMap_range]

/-- Translation of the free coordinates retains the full uniform tuple law. -/
theorem lifted_expect_shifted_basis_of_tuple {E0 : Type*}
    [AddCommGroup E0] [Module F2 E0]
    (S : Finset (Vertex n ell)) (hS : TuplePseudorandom S r ε)
    (b : Module.Basis (Fin q ⊕ Fin t) F2 (Ambient ell))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    [Fintype (E0 →ₗ[F2] W)]
    (b0 : Module.Basis (Fin t) F2 E0) (T0 : E0 →ₗ[F2] W)
    (hbudget : q + (n - Module.finrank F2 W) ≤ r) :
    (𝔼 H : E0 →ₗ[F2] W, liftedIndicator S
      (b.constr F2 (joinedTuple Q W (fun i => T0 (b0 i) + H (b0 i))))) ≤ ε := by
  have heq : (𝔼 H : E0 →ₗ[F2] W, liftedIndicator S
      (b.constr F2 (joinedTuple Q W (fun i => T0 (b0 i) + H (b0 i))))) =
      𝔼 z : Fin t → W, liftedIndicator S (b.constr F2 (joinedTuple Q W z)) := by
    apply Fintype.expect_equiv (affineCoordinates b0 T0)
    intro H
    rfl
  rw [heq]
  exact lifted_expect_in_basis_of_tuple S hS b Q W hbudget

/-- The adapted prefix contains all directions whose affine center lies
outside W. After splitting, each fixed constrained parameter gives an allowed
arbitrary prefix, and all free coordinates remain uniform in W. -/
theorem affine_expect_of_complement_of_tuple
    (S : Finset (Vertex n ell)) (hS : TuplePseudorandom S r ε)
    (D U E0 : Submodule F2 (Ambient ell)) (W : Submodule F2 (Ambient n))
    (hDU : D ≤ U) (hc : IsCompl U E0) (T : BasisMap n ell)
    (hE0 : E0 ≤ LinearMap.ker (W.mkQ.comp T))
    (hbudget : Module.finrank F2 U + (n - Module.finrank F2 W) ≤ r) :
    (𝔼 A : Parameter D W, restrict (liftedIndicator S) D W T A) ≤ ε := by
  rw [expect_restrict D U E0 W hDU hc T]
  apply Finset.expect_le Finset.univ_nonempty
  intro B _
  let bU := Module.finBasis F2 U
  let b0 := Module.finBasis F2 E0
  have heq :
      (𝔼 C : E0 →ₗ[F2] W,
        liftedIndicator S (translate D W T (join D U E0 W hDU hc B C))) =
      𝔼 C : E0 →ₗ[F2] W,
        liftedIndicator S ((complementBasis U E0 hc bU b0).constr F2
          (joinedTuple
            (fun i => T (bU i) + (B ((localVanishing D U).mkQ (bU i)) : Ambient n)) W
            (fun i => freeCenter E0 W T hE0 (b0 i) + C (b0 i)))) := by
    apply Finset.expect_congr rfl
    intro C _
    rw [translate_join_eq_constr D U E0 W hDU hc T hE0 bU b0 B C]
  rw [heq]
  exact lifted_expect_shifted_basis_of_tuple S hS (complementBasis U E0 hc bU b0)
    _ W b0 (freeCenter E0 W T hE0) hbudget

/-- Order d affine restrictions require at most 2d tuple restriction budget. -/
theorem affine_expect_bound_of_tuple {d : ℕ}
    (S : Finset (Vertex n ell)) (hS : TuplePseudorandom S (2 * d) ε)
    (D : Submodule F2 (Ambient ell)) (W : Submodule F2 (Ambient n))
    (T : BasisMap n ell) (horder : order D W ≤ d) :
    (𝔼 A : Parameter D W, restrict (liftedIndicator S) D W T A) ≤ ε := by
  obtain ⟨U, E0, hDU, hE0, hc, hdim⟩ :=
    KMSAffineRestrictionComplement.exists_bounded_complement D W T
  have hcodim : n - Module.finrank F2 W = Module.finrank F2 (KMS.Ambient n ⧸ W) := by
    have hd := W.finrank_quotient_add_finrank
    have hn : Module.finrank F2 (KMS.Ambient n) = n := by simp [KMS.Ambient]
    rw [hn] at hd
    omega
  apply affine_expect_of_complement_of_tuple S hS D U E0 W hDU hc T hE0
  rw [hcodim]
  change Module.finrank F2 D + Module.finrank F2 (KMS.Ambient n ⧸ W) ≤ d at horder
  omega

/-- Booleanity turns the exact restriction probability into its squared norm. -/
theorem affine_squared_expect_bound_of_tuple {d : ℕ}
    (S : Finset (Vertex n ell)) (hS : TuplePseudorandom S (2 * d) ε)
    (D : Submodule F2 (Ambient ell)) (W : Submodule F2 (Ambient n))
    (T : BasisMap n ell) (horder : order D W ≤ d) :
    (𝔼 A : Parameter D W, (restrict (liftedIndicator S) D W T A) ^ 2) ≤ ε := by
  have heq : (𝔼 A : Parameter D W, (restrict (liftedIndicator S) D W T A) ^ 2) =
      𝔼 A : Parameter D W, restrict (liftedIndicator S) D W T A := by
    apply Finset.expect_congr rfl
    intro A _
    unfold restrict liftedIndicator
    split <;> norm_num
  rw [heq]
  exact affine_expect_bound_of_tuple S hS D W T horder

/-- Directly discharge the fourth-moment affine density input from the
literal tuple pseudorandomness input of the ordered-basis expansion theorem. -/
theorem lifted_affineDensityBound_of_tuple {d : ℕ}
    (S : Finset (Vertex n ell)) (hS : TuplePseudorandom S (2 * d) ε) :
    KMSFourthMoment.AffineDensityBound d ε (liftedIndicator S) := by
  intro D _ _ _ C _ _ _ _ L hL J hJ T hdim
  calc
    (𝔼 X : D →ₗ[F2] C, liftedIndicator S (T + J.comp (X.comp L)) ^ 2) =
        𝔼 A : Parameter L.ker J.range,
          (restrict (liftedIndicator S) L.ker J.range T A) ^ 2 :=
      KMSAffineRestrictionPresentation.expect_presentation_sq L hL J hJ T _
    _ ≤ ε := affine_squared_expect_bound_of_tuple S hS L.ker J.range T
      (KMSAffineRestrictionPresentation.order_le_of_dimensions L hL J hJ d hdim)

end
end UniqueGamesTheorem.Inverse.KMSBasisComparisonAffineDensity

end

section

/-!
The local-density predicate is invariant under an ambient basis presentation
and consumes exactly the output codimension under a homogeneous restriction.
These are changes of the actual sampled affine maps, without an estimate loss.
-/

namespace UniqueGamesTheorem.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

universe u v
variable {E E' : Type u} {F B : Type v}
  [AddCommGroup E] [Module F2 E] [AddCommGroup E'] [Module F2 E']
  [AddCommGroup F] [Module F2 F] [AddCommGroup B] [Module F2 B]

/-- Exact ambient coordinate transport of all sampled affine restrictions. -/
theorem AffineDensityBound.domain_equiv
    [FiniteDimensional F2 E] [FiniteDimensional F2 E']
    (r : ℕ) (ε : ℝ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : AffineDensityBound r ε f) (e : E ≃ₗ[F2] E') :
    AffineDensityBound r ε (fun X : E' →ₗ[F2] F => f (X.comp e.toLinearMap)) := by
  intro D _ _ _ C _ _ _ _ L hL J hJ T hdim
  have hdim' : Module.finrank F2 E + Module.finrank F2 F ≤
      Module.finrank F2 D + Module.finrank F2 C + r := by
    rw [e.finrank_eq]
    exact hdim
  have h := hf D C (L.comp e.toLinearMap) (hL.comp e.surjective) J hJ
    (T.comp e.toLinearMap) hdim'
  simpa only [LinearMap.add_comp, LinearMap.comp_assoc] using h

/-- Homogeneous codomain restriction uses its actual codimension budget. -/
theorem AffineDensityBound.codomain_pullback
    [FiniteDimensional F2 B] (r s : ℕ) (ε : ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : AffineDensityBound (r + s) ε f)
    (K : B →ₗ[F2] F) (hK : Function.Injective K)
    (hdimK : Module.finrank F2 F ≤ Module.finrank F2 B + s) :
    AffineDensityBound r ε (fun X : E →ₗ[F2] B => f (K.comp X)) := by
  intro D _ _ _ C _ _ _ _ L hL J hJ T hdim
  have hdim' : Module.finrank F2 E + Module.finrank F2 F ≤
      Module.finrank F2 D + Module.finrank F2 C + (r + s) := by omega
  have h := hf D C L hL (K.comp J) (hK.comp hJ) (K.comp T) hdim'
  simpa only [LinearMap.comp_add, LinearMap.comp_assoc] using h

end
end UniqueGamesTheorem.Inverse.KMSFourthMoment

end

section

/-!
Transport of actual small components when the ambient domain changes by a
linear equivalence. The coefficient and component identities hold for every
real function; basis invariance is separately transported when available.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier

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

omit [FiniteDimensional F2 E] [FiniteDimensional F2 E']
  [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (F →ₗ[F2] E)] [Fintype (F →ₗ[F2] E')]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)] in
theorem smallCoeff_ambient_transport (h : E ≃ₗ[F2] E') (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (T : F →ₗ[F2] I) :
    smallCoeff (h.toLinearMap.comp ι)
      (fun X : E' →ₗ[F2] F => f (X.comp h.toLinearMap)) T = smallCoeff ι f T := by
  unfold smallCoeff
  split_ifs
  · rw [LinearMap.comp_assoc, ambient_coeff_transport]
  · rfl

omit [FiniteDimensional F2 E] [FiniteDimensional F2 E']
  [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (F →ₗ[F2] E)] [Fintype (F →ₗ[F2] E')]
  [Fintype (I →ₗ[F2] F)] in
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
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-!
The exact Fourier coefficient merging law for a codomain restriction. This
is the Fourier step of KMS's zoom-out recursion: the subsequent orbit argument
groups the genuine extension fiber using basis invariance. Neither an inverse
nor a rank-level estimate is a premise.
-/

namespace UniqueGamesTheorem.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier

variable {E F B : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup B] [Module F2 B]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 B]

/-- Restricting the codomain of a primal map restricts the domain of its dual
frequency. This identity is independent of the choice of bases. -/
theorem character_codomain_composition (J : B →ₗ[F2] F)
    (S : F →ₗ[F2] E) (X : E →ₗ[F2] B) :
    linearTraceCharacter S (J.comp X) = linearTraceCharacter (S.comp J) X := by
  simp only [linearTraceCharacter_apply]
  congr 1
  rw [linearTracePair_swap (J.comp X) S, linearTracePair_swap X (S.comp J)]
  simp only [linearTracePair, LinearMap.comp_assoc]

variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (E →ₗ[F2] B)] [Fintype (B →ₗ[F2] E)]

omit [Fintype (B →ₗ[F2] E)] in
/-- Coefficients of the actual restricted function are the unnormalized sum
over exactly those original frequencies whose restriction is the new one.
The statement allows arbitrary linear `J`; injections are the KMS use case. -/
theorem coefficient_codomain_pullback (J : B →ₗ[F2] F)
    (f : (E →ₗ[F2] F) → ℝ) (T : B →ₗ[F2] E) :
    linearCoeff (fun X => f (J.comp X)) T =
      ∑ S : F →ₗ[F2] E, if S.comp J = T then linearCoeff f S else 0 := by
  have hexpand : (fun X => f (J.comp X)) =
      ∑ S : F →ₗ[F2] E, linearCoeff f S •
        (fun X => (linearTraceCharacter (S.comp J) X).re) := by
    funext X
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simpa only [character_codomain_composition] using
      (linear_fourier_inversion f (J.comp X)).symm
  rw [hexpand, linearCoeff_sum]
  simp only [linearCoeff_smul, linearCoeff_character]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : S.comp J = T
  · simp [hS]
  · simp [hS, Ne.symm hS]

omit [Fintype (B →ₗ[F2] E)] in
/-- The same merging identity on the actual fiber type. This form is ready
for the hyperplane extension bijection, without changing normalization. -/
theorem coefficient_codomain_pullback_fiber (J : B →ₗ[F2] F)
    (f : (E →ₗ[F2] F) → ℝ) (T : B →ₗ[F2] E) :
    linearCoeff (fun X => f (J.comp X)) T =
      ∑ S : {S : F →ₗ[F2] E // S.comp J = T}, linearCoeff f S.val := by
  rw [coefficient_codomain_pullback]
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun S _ => S.val) ?_ ?_ ?_ ?_
  · intro S _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, S.property⟩
  · intro S _ R _ h
    exact Subtype.ext h
  · intro S hS
    exact ⟨⟨S, (Finset.mem_filter.mp hS).2⟩, Finset.mem_univ _, rfl⟩
  · intro S _
    rfl

end
end UniqueGamesTheorem.Inverse.KMSFourthMoment

end

end OAI

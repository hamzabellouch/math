import OAI.Combinatorics.Progressions.Lattices.ForecastOriginalSampleResidueFactor
import OAI.Combinatorics.Progressions.Sampling.ForecastNormalizedTwistExtension

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X]
  [Fintype Zsp] [DecidableEq Zsp]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, DecidableEq (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Output" => (Σ _a : Active, Unit)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Domain" => ((Spatial → ℝ) × (Output → ℝ))
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short
local notation "hamin" => unitProfilePrincipalLowerBound_pos B

variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
  {δ : ℝ} (hδ : 0 < δ)
  (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)

local notation "density" => allocatedOriginalSampleForecastDensity (X := X)
  B U basis S s root D hp hW hL hB lower width
local notation "cap" => allocatedOriginalForecastCap (X := X) B U basis S s hδ
local notation "lip" => allocatedOriginalForecastLip (X := X) B U basis S s hδ

local notation "normalized" => allocatedOriginalSampleNormalizedForecast (X := X)
  B U basis S s root D hp hW hL hB lower width hδ

include hR hσ hw hl in

theorem exists_allocatedOriginalSampleNormalizedTwist
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + W)
    {A Site : Type*} [Fintype A]
    {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
    (selected : A → Σ j : Fin m, Fin (n j))
    (hR1 : ∀ a, R (selected a).1 ≤ 1)
    {Nmod : ℕ} [NeZero Nmod]
    (χ : AddChar (Sigma (AllocatedCongruenceRankOutput X Eout short) → ZMod Nmod) ℂ)
    (M : ℕ) [NeZero M] (hM : orderOf χ ∣ M)
    (e : A → ScalarSiteExpansion Site)
    {Tsite Dsite Csite Hsite : A → ℝ} {Lsite : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Tsite a) (Dsite a) (Csite a) Lsite (Hsite a))
    (k : ∀ a, (e a).Term) (site : Site)
    (hd : ∀ a, (e a).period (k a) ∣ M)
    (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ) (hτ : 0 < τ)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
      projectedIntegerLattice (euclideanSubspace (U j)))
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤
      Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K) :
    let Lcoord : ℝ≥0 := max ⟨8 / τ, by positivity⟩
      (K * ∑ j, Cforward j * Fintype.card (J j))
    let Lfactor := (lip + Fintype.card A * Lsite) * Lcoord
    ∃ twist : NormalizedPolynomialTwist X (Σ j, J j) M M
        (max (Lfactor * max 1 (M : ℝ≥0)) (4 * M)),
      twist.modulus = M ∧ twist.cover = M ∧
      ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ)
        (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, Eout j → ℤ),
        (∀ j i, eval (fun a => (u a : ℝ)) (poly j) i =
          (normalizedLatticeRepresentative (euclideanSubspace (U j)) (basis j) (hb j)
            (orthonormalMixedChart (o j) (w j)) +
              ((bW j).equivFun.symm (deck j)).val).val i) →
        (∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (basis j)
          (orthonormalMixedChart (o j) (w j)) i| ≤ 1 / 4) →
        (density sample
          ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
            forecastNormalizedActiveCoordinates short
              (allocatedFullMixedSiteValue (R := R) U basis w)) : ℂ) *
          star (χ (fun output => (forecastCongruenceOutput (R := ℤ) short u
            (fun j => Sum.elim (w j).2 (deck j)) output : ZMod Nmod))) *
          siteFamilyFactor e k site
            (fun a => ((w (selected a).1).2 (selected a).2 : ZMod ((e a).period (k a))))
            (fun a => ((w (selected a).1).2 (selected a).2 : ℝ) /
              basisAxisScale (basis (selected a).1) (selected a).2) =
        2 * (((cap : ℝ) + 1 : ℝ) : ℂ) * twist.eval physicalN poly u := by
  intro Lcoord Lfactor
  obtain ⟨mask, F, hmask, hF, hFL, hvalue⟩ :=
    exists_forecastOriginalSampleResidueFactor (X := X)
      B U basis hR hσ S s root D hp hW hL hB lower width hδ hw hl
      sample hs hroot selected hR1 χ M hM e he k site hd
  let Fcomp := fun label => F label ∘
    forecastNormalizedAmbientCoordinates U basis o R base physicalN τ
  have hcoord : LipschitzWith Lcoord
      (forecastNormalizedAmbientCoordinates U basis o R base physicalN τ) :=
    forecastNormalizedAmbientCoordinates_lipschitz U basis o R base physicalN τ
      hR hτ Cforward hforward K hK
  have hFcomp : ∀ label, LipschitzWith Lfactor (Fcomp label) :=
    fun label => (hFL label).comp hcoord
  obtain ⟨twist, hmodulus, hcover, htwist⟩ :=
    exists_forecast_normalized_twist_extension U bW basis hb M
      (fun a => star (mask a)) (fun a => by rw [norm_star, hmask])
      Fcomp Lfactor hFcomp (fun label x => hF label _)
  refine ⟨twist, hmodulus, hcover, ?_⟩
  intro poly u w deck heval hquarter
  have ht := htwist physicalN poly u (fun j => orthonormalMixedChart (o j) (w j))
    deck heval hquarter
  change twist.eval physicalN poly u = star (mask (fun i => (u i : ZMod M))) *
    F (fun j => Sum.elim (fun i => ((w j).2 i : ZMod M))
      (fun i => (deck j i : ZMod M)))
      (forecastNormalizedAmbientCoordinates U basis o R base physicalN τ
        (fun i => (u i : ℝ) / physicalN i,
          fun a => normalizedLatticePoint (euclideanSubspace (U a.1)) (basis a.1)
            (orthonormalMixedChart (o a.1) (w a.1)) a.2)) / 2 at ht
  rw [forecastNormalizedAmbientCoordinates_mixed] at ht
  rw [hvalue u deck w, ht]
  ring

end Erdos3.VectorPolynomial

end

end OAI

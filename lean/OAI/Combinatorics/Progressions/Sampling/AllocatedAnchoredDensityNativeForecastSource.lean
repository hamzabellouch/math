import OAI.Combinatorics.Progressions.Sampling.AllocatedRecoveredForecastDecay

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*} [Fintype A]

attribute [local instance] ScalarSiteExpansion.termFinite
variable {X : Type*} [Fintype X]
variable {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (hm : 0 < m)
variable (Dmod : ℕ)
variable (hDmod : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
variable {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G) (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩)
variable (base : X → ℤ)
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (ambientPoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (ambientPoly j) d ∈ U j)

local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U b S.value))
local notation "Cmod" => (modularForecastRankConstant m Dmod : ℝ)

local instance anchoredNativeDensitySourceModulusNeZero (Pr : Finset ℕ) (Aexp : ℕ → ℕ)
    [∀ q : Pr, NeZero q.val] : NeZero (∏ q : Pr, q.val ^ Aexp q.val) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun q _ => pow_ne_zero _ (NeZero.ne q.val))⟩

local instance (N : ℕ) [NeZero N] (χ : AddChar (Out → ZMod N) ℂ) : NeZero (orderOf χ) :=
  ⟨(isOfFinOrder_of_finite χ).orderOf_pos.ne'⟩

section RationalSite

variable (selected : A → Σ j : Fin m, Fin (n j))

variable (hselected : Function.Injective selected)

variable [siteInst1 : ∀ a, Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩)]

variable (T : ℕ)

variable (hT : 0 < T)

variable {D P p v δ E : ℝ}

variable (hD : AllocatedComparisonDimensions (G := G) B Empty
      (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D)

variable (hP : 1 ≤ P)

variable (hp : 0 ≤ p)

variable (hv : 0 ≤ v)

variable (hPp : P ≤ Real.exp p)

variable (hTv : (T : ℝ) ≤ Real.exp v)

variable (hδ : 0 < δ)

variable (hE : 0 ≤ E)

variable (hδE : δ⁻¹ ≤ Real.exp E)

variable (hsize : T ≤ S.value)

variable (hR1 : ∀ a, R (selected a).1 ≤ 1)

variable (hsmall : ∀ a, basisAxisScale (b (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))

variable (hσ1 : ∀ a, σ (selected a).1 ≤ 1)

variable (L : ℝ≥0)

variable (hL : LipschitzWith L Real.smoothTransition)

variable (hprimitive : scalarCubePrimitiveEnvelope Empty L 1 0 T ≤ P)

variable (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))

variable {Pscale : ℝ}

variable (hPscale : 0 ≤ Pscale)

variable (hRinv : ∀ a, (R (selected a).1)⁻¹ ≤ Real.exp Pscale)

variable (hslots : ∀ a, ((layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2).card : ℝ) ≤ Pscale)

include selected hselected siteInst1 T hT hD hP hp hv hPp hTv hδ hE hδE hsize
  hR1 hsmall hσ1 L hL hprimitive hB hPscale hRinv hslots
  hm hDmod

theorem exists_allocated_anchored_density_native_forecast_source
    {Pcap pcap : ℝ} (hPcap : 1 ≤ Pcap) (hpcap : 0 ≤ pcap)
    (hPcapp : Pcap ≤ Real.exp pcap)
    (hprimitiveCap : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ Pcap)
    (physicalN : X → ℕ) (τ : ℝ) (hτ : 0 < τ)
    (forward : Fin m → ℝ≥0)
    (hforward : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ forward j * ‖w‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (radius : ℝ≥0) (hr : 0 < radius) (hr3 : (3 : ℝ) ≤ radius)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ radius)
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j w, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    (hbudget : ∀ j, inverse j * (((Fintype.card (I j) : ℝ) + 1) *
      (2 * (radius : ℝ) * R j)) ≤ 1 / 4)
    (hexhaustive : ∀ a, allocatedShortAxis (I := I) U b S.value a → ∃ i,
      (⟨(selected i).1, Sum.inr (selected i).2⟩ : LayerSamplerAxis I n) = a) :
    ∃ (sample : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
        CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
      (read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
        AllocatedActualCoefficientIndex G X I Eout n B → ℤ),
      (∀ z, allocatedReadNoise (read z) = z ∧
        (allocatedCoefficientDensity B U b hb o hR hσ S
          (affineSampleCoefficientTorus U ambientPoly hmem (fun k x => ((integerBaseTranslation base (k,x) + z (k,x) : ℤ) : ℝ))) ≠ 0 →
        (canonicalCoefficientSample U b hb o (sample z) =
          affineSampleCoefficientTorus U ambientPoly hmem (fun k x => ((integerBaseTranslation base (k,x) + z (k,x) : ℤ) : ℝ))) ∧
        (∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (sample z j) ∧
          mixedArraySupported (allocatedLayerCenters B U b S j)
            (allocatedLayerWidths B U b S j)
            (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample z j)) ∧
        (∀ (j : Fin m) (i : Fin (n j))
          (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
          allocatedReadProjection (read z) ⟨j, Sum.inr i⟩ e = (sample z j).2 i e) ∧
        ∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
          ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n Eout q → Prop,
            coefficientDeckChartEvent U bW b hb o q event
              (affineCoefficientCoverSample U ambientPoly hmem q (fun k x => ((integerBaseTranslation base (k,x) + z (k,x) : ℤ) : ℝ))) ↔
            event (allocatedReadCoefficientChartResidues (fun i => (read z i : ZMod q)))) ) ∧
      ∀ (z : Option (LayerSamplerVariables G I n B) × X → ℤ),
        allocatedCoefficientDensity B U b hb o hR hσ S
          (affineSampleCoefficientTorus U ambientPoly hmem (fun k x => ((integerBaseTranslation base (k,x) + z (k,x) : ℤ) : ℝ))) ≠ 0 →
      ∀ (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
        ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}, Unit) → ℝ)) → ℝ)
        (cap lip : ℝ≥0),
        (∀ y, |density y| ≤ (cap : ℝ)) → LipschitzWith lip density →
        (∀ y, density y ≠ 0 → ∀ a, |y.2 a| ≤ 3) →
      ∀ (Pr : Finset ℕ) (primeNZ : ∀ q : Pr, NeZero q.val), letI := primeNZ;
      ∀ (Aexp epres : ℕ → ℕ) (hPr : ∀ q ∈ Pr, q.Prime) (Rbad : ℕ),
        (∏ q ∈ Pr, q ^ largestTestedBadDepth Aexp
          (fun q a z => allocatedActualPrimeBad (allocatedShortAxis (I := I) U b S.value)
            spatial kernel block Pr Cmod q a (read z)) q z) ≤ Rbad →
      ∀ (origin : ∀ q : Pr,
          LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B →
            ZMod (q.val ^ Aexp q.val)),
    let N := ∏ q : Pr, q.val ^ Aexp q.val
    let poly := allocatedForecastPolynomial (allocatedShortAxis (I := I) U b S.value)
      base z (allocatedReadDeck (read z))
      (fun j a => allocatedReadProjection (read z) ⟨j, a.val⟩)
    let pRat := crtPolynomialInputLaw (fun q : Pr => q.val)
      (fun q : Pr => Aexp q.val) (fun q : Pr => epres q.val)
      (primePower_crt_coprime (fun q : Pr => q.val) (fun q : Pr => Aexp q.val)
        (fun q => hPr q.val q.property) Subtype.val_injective) origin
    let Cdecay := (((Rbad * ∏ q : Pr, q.val ^ epres q.val : ℕ) : ℝ) ^
      (modularRankDecayExponent m Cmod * modularRankChargeFactor m))
    let law := principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let Ch := Finset.univ.filter (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ≤ T)
    let Pos := fun χ : Ch =>
      {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod (orderOf χ.val) //
        0 < law.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r))}
    letI : ∀ χ : Ch, Fintype (Pos χ) := fun χ => by
      dsimp only [Pos]
      infer_instance
    let scale := fun a => basisAxisScale (b (selected a).1) (selected a).2
    let W := 4 * (Pscale + 8)
    let O := allocatedInactiveJointSiteLog m D p v (E + D * W) + W
    let Ig := Fintype.card A * (allocatedInactivePointCapLog m D pcap 0 + 4 * (Pscale + 8))
    let weight := fun (χ : Ch) (r : Pos χ) =>
      (law.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
        forecastInactiveCharacterCoefficient poly N pRat χ.val r.val
    let H : ℝ := (cap : ℝ) + 1
    let Lspatial : ℝ≥0 := max ⟨8 / τ, by positivity⟩ 1
    let Lfactor := (lip + Fintype.card A * ⟨Real.exp O, Real.exp_nonneg _⟩) * Lspatial
    let Lcoord := K * ∑ j, forward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound /
      (2 * radius)) * Lcoord
    ∀ {Pnative : ℝ}, 0 ≤ Pnative → v + Fintype.card A * O ≤ Pnative →
      (Lfactor : ℝ) ≤ Real.exp Pnative → (Lcoord : ℝ) ≤ Real.exp Pnative →
      (Lcut : ℝ) ≤ Real.exp Pnative →
    ∃ e : ∀ χ : Ch, Pos χ → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ χ r a, (e χ r a).Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp (allocatedInactiveSupportLog D))) ∧
      let Term := Σ χ : Ch, Σ r : Pos χ, ∀ a, (e χ r a).Term
      let coeff := fun t : Term => (H : ℂ) * forecastSiteMixtureCoefficient (e t.1) (weight t.1) t.2
      ∃ twists : Term → NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp (3 * Pnative + 3)) (Real.exp (3 * Pnative + 3))
        ⟨Real.exp (3 * Pnative + 3), Real.exp_nonneg _⟩,
        (∀ t, (twists t).modulus = orderOf t.1.val * commonSitePeriod (e t.1 t.2.1) t.2.2 ∧
          (twists t).cover = orderOf t.1.val * commonSitePeriod (e t.1 t.2.1) t.2.2) ∧
        (∑ t : Term, ‖(2 : ℂ) * coeff t‖) ≤
          2 * H * ((T : ℝ) ^ (Fintype.card Out + 1) * Real.exp (Fintype.card A * O)) ∧
        ∀ (x : G → IntegerScalarCubeBox Empty S.value)
          (physicalPoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (hphysical : ∀ j v, coefficients (physicalPoly j) v ∈ U j) (u : X → ℤ),
          ‖forecastDensityPhysicalTarget B U b S density selected (sample z) x (fun _ => pRat)
            (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
            N (∏ a, (scale a : ℝ)) base physicalN τ o hb bW physicalPoly hphysical u -
              ∑ t : Term, ((2 : ℂ) * coeff t) * (twists t).eval physicalN physicalPoly u‖ ≤
            H * (Real.exp Ig * (Cdecay / T) + (T : ℝ) ^ (Fintype.card Out + 1) * δ) := by
  obtain ⟨sample, read, hread⟩ := exists_allocatedAnchored_recovered_sample_read
    B U bW b hb o S hR hσ ambientPoly hmem base
  refine ⟨sample, read, hread, ?_⟩
  intro z hz density cap lip hbound hLips hactive Pr primeNZ
  let _ := primeNZ
  intro Aexp epres hPr Rbad htail origin
  have hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j)
      (sample z j) := fun j => (((hread z).2 hz).2.1 j).2
  have hbad := allocatedPhysical_forecast_bad_product_le
    (allocatedShortAxis (I := I) U b S.value) spatial kernel block Pr Cmod Aexp
    read z (hread z).1 Rbad htail
  exact fun {Pnative} hPnative hperiod hfactor hcoord hcut =>
    exists_allocated_density_native_forecast_source
    (B := B) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
    (hm := hm) (Pr := Pr) (Aexp := Aexp) (epres := epres)
    (hPr := hPr) (Dmod := Dmod) (hDmod := hDmod)
    (noise := z) (rdeck := allocatedReadDeck (read z))
    (projection := fun j a => allocatedReadProjection (read z) ⟨j, a.val⟩)
    (spatial := spatial) (kernel := kernel) (block := block)
    (Rbad := Rbad) (hbad := hbad) (base := base) (origin := origin) (Pnative := Pnative)
    (selected := selected) (hselected := hselected) (T := T) (hT := hT)
    (hD := hD) (hP := hP) (hp := hp) (hv := hv) (hPp := hPp) (hTv := hTv)
    (hδ := hδ) (hE := hE) (hδE := hδE) (hsize := hsize)
    (hR1 := hR1) (hsmall := hsmall) (sample := sample z) (hs := hs)
    (hσ1 := hσ1) (L := L) (hL := hL) (hprimitive := hprimitive) (hB := hB)
    (hPscale := hPscale) (hRinv := hRinv) (hslots := hslots)
    hPcap hpcap hPcapp hprimitiveCap density cap lip hbound hLips hactive
    physicalN τ hτ o bW hb forward hforward K hK radius hr hr3 hradius
    inverse hinverse hchart hbudget hexhaustive hPnative hperiod hfactor hcoord hcut

end RationalSite

end Erdos3.VectorPolynomial

end

end OAI

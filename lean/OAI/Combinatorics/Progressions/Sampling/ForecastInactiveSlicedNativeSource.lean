import OAI.Combinatorics.Progressions.Sampling.ForecastLawNativeRawJointMean

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable {A : Type*} [Fintype A]
attribute [local instance] ScalarSiteExpansion.termFinite

variable {Vact : Type*} [Fintype Vact] [DecidableEq Vact]
variable {X : Type*} [Fintype X]
variable {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Active" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)

local instance forecastInactiveSlicedNativeSourceCharacterOrderNeZero
    (N : ℕ) [NeZero N] (χ : AddChar (Out → ZMod N) ℂ) : NeZero (orderOf χ) :=
  ⟨(isOfFinOrder_of_finite χ).orderOf_pos.ne'⟩

theorem exists_forecastInactive_sliced_native_source
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    (poly : Out → MvPolynomial (Vact ⊕ (PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty)) ℤ)
    (N : ℕ) [NeZero N] (pRat : FiniteProbabilityWeights (Vact → ZMod N))
    (T : ℕ) (hT : 0 < T)
    (δ P : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ ≤
        (H ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ)) ∧
       (∀ b v, 0 < step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩)))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hP : 1 ≤ P) (hsP : scalarCubePrimitiveEnvelope Empty L 1 0 T ≤ P)
    (hstride : ∀ a b v, ((step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ * T : ℕ) : ℝ) ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (Cactual δout Q Nt Vt Ct Ht : ℝ) (Lt : ℝ≥0)
    (hCactual : 0 ≤ Cactual) (hCtNonneg : 0 ≤ Ct) (hδout : 0 < δout) (hQ : 0 ≤ Q)
    (hnumerics : ∀ q : ℕ, 0 < q → q ≤ T →
      forecastInactiveSlicedSiteNumerics (G := G) B (R := R) selected q Hchild
        δ P Cactual δout Q Nt Vt Ct Ht Lt)
    {Cdecay Pdecay : ℝ} (hCdecay : 0 ≤ Cdecay)
    (hPdecay : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ Pdecay)
    (hdecay : ∀ (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
        (allocatedPrincipalSides B U basis S)) (χ : AddChar (Out → ZMod N) ℂ),
      ‖finiteImageCharacteristic pRat
        (fun t j => (integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j : ZMod N)) χ‖ ≤
        Cdecay * (orderOf χ : ℝ) ^ (-Pdecay))
    (density : ((Spatial → ℝ) × (Active → ℝ)) → ℝ)
    (cap lip : ℝ≥0) (hbound : ∀ y, |density y| ≤ (cap : ℝ))
    (hLips : LipschitzWith lip density)
    (hactive : ∀ y, density y ≠ 0 → ∀ a, |y.2 a| ≤ 3)
    (hR1 : ∀ a, R (selected a).1 ≤ 1)
    (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ) (hτ : 0 < τ)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (forward : Fin m → ℝ≥0)
    (hforward : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) w‖ ≤ forward j * ‖w‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (radius : ℝ≥0) (hr : 0 < radius) (hr3 : (3 : ℝ) ≤ radius)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ radius)
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j w, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm w‖ ≤ inverse j * ‖w‖)
    (hbudget : ∀ j, inverse j * (((Fintype.card (I j) : ℝ) + 1) *
      (2 * (radius : ℝ) * R j)) ≤ 1 / 4)
    (hexhaustive : ∀ a, short a → ∃ i,
      (⟨(selected i).1, Sum.inr (selected i).2⟩ : LayerSamplerAxis I n) = a) :
    let p := principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH
    let map := containedProgressionTupleMap B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hsubset
    let law := p.fiberLaw map
    let Ch := Finset.univ.filter (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ≤ T)
    let Pos := fun χ : Ch =>
      {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod (orderOf χ.val) //
        0 < p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r))}
    letI : ∀ χ : Ch, Fintype (Pos χ) := fun χ => by
      dsimp only [Pos]
      infer_instance
    let height := fun a => basisAxisScale (basis (selected a).1) (selected a).2
    let weight := fun (χ : Ch) (r : Pos χ) =>
      (p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
        forecastInactiveCharacterCoefficient poly N pRat χ.val
          (progressionPrincipalResidue B (layerSamplerDegree I n) step c (orderOf χ.val) r.val)
    let Hdensity : ℝ := (cap : ℝ) + 1
    let Lspatial : ℝ≥0 := max ⟨8 / τ, by positivity⟩ 1
    let Lfactor := (lip + Fintype.card A * Lt) * Lspatial
    let Lcoord := K * ∑ j, forward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound /
      (2 * radius)) * Lcoord
    ∀ {Pnative : ℝ}, 0 ≤ Pnative →
      (T : ℝ) * Vt ^ Fintype.card A ≤ Real.exp Pnative →
      (Lfactor : ℝ) ≤ Real.exp Pnative → (Lcoord : ℝ) ≤ Real.exp Pnative →
      (Lcut : ℝ) ≤ Real.exp Pnative →
    ∃ e : ∀ χ : Ch, Pos χ → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ χ r a, (e χ r a).Bounds Nt Vt Ct Lt Ht) ∧
      let Term := Σ χ : Ch, Σ r : Pos χ, ∀ a, (e χ r a).Term
      let coeff := fun t : Term => (Hdensity : ℂ) * forecastSiteMixtureCoefficient (e t.1) (weight t.1) t.2
      ∃ twists : Term → NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp (3 * Pnative + 3)) (Real.exp (3 * Pnative + 3))
        ⟨Real.exp (3 * Pnative + 3), Real.exp_nonneg _⟩,
        (∀ t, (twists t).modulus = orderOf t.1.val * commonSitePeriod (e t.1 t.2.1) t.2.2 ∧
          (twists t).cover = orderOf t.1.val * commonSitePeriod (e t.1 t.2.1) t.2.2) ∧
        (∑ t : Term, ‖(2 : ℂ) * coeff t‖) ≤
          2 * Hdensity * ((T : ℝ) ^ (Fintype.card Out + 1) * Ct ^ Fintype.card A) ∧
        ∀ (x : G → IntegerScalarCubeBox Empty S.value)
          (physicalPoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (hphysical : ∀ j v, coefficients (physicalPoly j) v ∈ U j) (u : X → ℤ),
          ‖forecastLawDensityPhysicalTarget B U basis S law density selected sample x (fun _ => pRat)
            (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
            N (∏ a, (height a : ℝ)) base physicalN τ o hb bW physicalPoly hphysical u -
              ∑ t : Term, ((2 : ℂ) * coeff t) * (twists t).eval physicalN physicalPoly u‖ ≤
            Hdensity * (Cactual ^ Fintype.card A * (Cdecay / T) +
              (T : ℝ) ^ (Fintype.card Out + 1) * δout) := by
  intro p map law Ch Pos height weight Hdensity Lspatial Lfactor Lcoord Lcut
    Pnative hPnative hperiod hfactor hcoord hcut
  have hHdensity : 1 ≤ Hdensity := by dsimp only [Hdensity]; linarith [cap.property]
  have hdensity : ∀ y, ‖density y‖ ≤ Hdensity := fun y =>
    (show ‖density y‖ ≤ (cap : ℝ) by simpa only [Real.norm_eq_abs] using hbound y).trans
      (by dsimp only [Hdensity]; linarith)
  have hcoefficients := allocatedOriginalSampleInactiveCoefficients_supported
    B selected U basis hR hσ S sample hs
  obtain ⟨e, he, hmass, _, _, herror⟩ :=
    exists_forecastInactive_sliced_capped_continuous_rational_source
      B U basis hR hσ S H step c hH hsubset selected hselected poly N pRat T hT
      δ P Hchild hδ hreg hsmall hgrid
      (allocatedOriginalSampleInactiveCoefficients B selected sample) hcoefficients
      hσ1 L hL hP hsP hstride hB Cactual δout Q Nt Vt Ct Ht Lt hCactual hCtNonneg hδout hQ hnumerics
      hCdecay hPdecay hdecay density Hdensity hHdensity hdensity lip hLips
  let _ : ∀ χ : Ch, Fintype (Pos χ) := fun χ => by dsimp only [Pos]; infer_instance
  let Term := Σ χ : Ch, Σ r : Pos χ, ∀ a, (e χ r a).Term
  let _ : Fintype Term := by dsimp only [Term]; infer_instance
  let coeff := fun t : Term => (Hdensity : ℂ) * forecastSiteMixtureCoefficient (e t.1) (weight t.1) t.2
  have hperiodTerm (t : Term) :
      ((orderOf t.1.val * commonSitePeriod (e t.1 t.2.1) t.2.2 : ℕ) : ℝ) ≤ Real.exp Pnative := by
    have horder : (orderOf t.1.val : ℝ) ≤ T :=
      Nat.cast_le.mpr (Finset.mem_filter.mp t.1.property).2
    have hsite := commonSitePeriod_le_pow (e t.1 t.2.1) (he t.1 t.2.1)
      (fun _ => le_rfl) t.2.2
    rw [Nat.cast_mul]
    exact (mul_le_mul horder hsite (Nat.cast_nonneg _) (Nat.cast_nonneg T)).trans hperiod
  obtain ⟨twists, hmod, htransfer⟩ := exists_forecastDensityBufferedNativeExpansion
    B U basis hR S density cap lip hbound hLips selected hR1
    (fun t : Term => t.1.val) (fun t : Term => e t.1 t.2.1)
    (fun t a => he t.1 t.2.1 a) (fun t : Term => t.2.2) ∅ base physicalN τ hτ
    o bW hb forward hforward K hK radius hr inverse hinverse hchart hbudget
    hPnative hperiodTerm hfactor hcoord hcut
  refine ⟨e, he, twists, hmod, ?_, ?_⟩
  · simpa only [mul_assoc] using forecastPhysicalBufferedCoefficientMass coeff hmass
  · intro x physicalPoly hphysical
    let target := forecastLawDensityPhysicalTarget B U basis S law density selected sample x (fun _ => pRat)
      (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
      N (∏ a, (height a : ℝ)) base physicalN τ o hb bW physicalPoly hphysical
    have hε : 0 ≤ Hdensity * (Cactual ^ Fintype.card A * (Cdecay / T) +
        (T : ℝ) ^ (Fintype.card Out + 1) * δout) := by positivity
    apply (htransfer physicalPoly hphysical coeff target
      (Hdensity * ((T : ℝ) ^ (Fintype.card Out + 1) * Ct ^ Fintype.card A))
      (Hdensity * (Cactual ^ Fintype.card A * (Cdecay / T) +
        (T : ℝ) ^ (Fintype.card Out + 1) * δout))
      hmass hε ?_ ?_).2
    · intro u hu
      exact forecastLawDensityPhysicalTarget_cutoff_of_active_support
        B U basis S law density selected sample x (fun _ => pRat)
        (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
        N (∏ a, (height a : ℝ)) base physicalN τ o hb bW
        hR hσ hs hσ1 hexhaustive hactive radius hr hr3 hradius
        inverse hinverse hchart hbudget physicalPoly hphysical u hu
    · intro u w deck hdeck hquarter
      exact forecastLawDensityPhysicalApproximation B U basis S law density selected sample x
        (fun _ => pRat)
        (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
        N (∏ a, (height a : ℝ)) base physicalN τ o hb bW
        (fun t : Term => t.1.val) (fun t : Term => e t.1 t.2.1)
        (fun t : Term => t.2.2) ∅ coeff cap (herror x)
        physicalPoly hphysical u w deck hdeck hquarter

end Erdos3.VectorPolynomial

end

end OAI

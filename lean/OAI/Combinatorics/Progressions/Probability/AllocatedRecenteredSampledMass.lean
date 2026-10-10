import OAI.Combinatorics.Progressions.Estimates.AllocatedRecenteredProfileComparison
import OAI.Combinatorics.Progressions.Estimates.AllocatedRecenteredProfileError

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable (m dim : ℕ)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

theorem exists_allocated_recentered_sampled_mass_bound :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U b R σ) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d] (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (modulus : ℕ) [NeZero modulus]
    (_hperiod : ∀ j, integerScalarLattice (jets j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (jetRows j)).mulVecLin.range)
    {X : Type*} [Fintype X] [DecidableEq X]
    (q : X → ℕ) (_hq : ∀ t, 0 < q t)
    (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
    (wholeReference : (PrincipalTupleIndex B (layerSamplerDegree I n) →
      Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
    (N : X → ℕ) (_hN : ∀ t, 0 < N t)
    {W τ ξ ρ : ℝ} (_hW : 0 ≤ W) (_hτ : 0 < τ) (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hρ : 0 < ρ)
    (_hsizeSp : ∀ t, 8 * (1 + W) * (q t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
    (_hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
    (_hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
    (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    {P Rrank ε : ℝ} (_hP : 0 ≤ P) (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    (_hτP : 1 / τ ≤ Real.exp P) (_hstride : ∀ t, (q t : ℝ) ≤ Real.exp P)
    (_hε : 0 < ε) (_hεP : 1 / ε ≤ Real.exp P)
    (_hsize : ∀ t, Real.exp ((P + K) ^ K) ≤ (N t : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) Rrank (U j) (p j))
    (_hRank : Real.exp ((P + K) ^ K) ≤ Rrank)
    (η : ℝ≥0) {δf L : ℝ} (_hδf : 0 < δf) (_hL : 0 ≤ L)
    (_hamb : (Fintype.card (JetAmbientIndex jets J) : ℝ) ≤ L) (_hδL : δf⁻¹ ≤ Real.exp L),
    let A := Real.toNNReal (coefficientDeckPeriodCap jets Q modulus)
    (allocatedErrorKernelLip B U b S (O := jets) η A C V : ℝ) ≤ Real.exp L →
    Real.exp ((2 * L + 2) ^ 4) ≤ Real.exp P →
    Real.exp (2 * L * (2 * L + 2) ^ 4) * allocatedErrorKernelCap B U b S (O := jets) η A V ≤ Real.exp P →
    ∀ (hRefined : 0 < residueRefinedPeriod modulus q),
    let _ : NeZero (residueRefinedPeriod modulus q) := ⟨hRefined.ne'⟩
    ∀ (s : ∀ j, jets j ↪ BoundedIntegerExponent G (j.val+1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (jetRows j)).submatrix id (s j)).det ≠ 0)
    (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      ∀ j, Matrix (jets j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (hlengths : ∀ t, (Fintype.card (Fin dim)+1)*residueRefinedPeriod modulus q ≤
      principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S) t)
    (_href : ∀ u r, principalResidueLabel (residueRefinedPeriod modulus q) (reference u r) = r)
    (_hr : ∀ u r v,
      (allocatedLongResidueWeights B U b S (residueRefinedPeriod modulus q) hRefined r hlengths).weight v ≠ 0 → ∀ j,
      integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u jetRows j v) modulus = residue u r j)
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv 1 j)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) →
      EuclideanJetLayers U jets → ℝ)
    (_hg : ∀ y, Continuous (g y)) (_hg0 : ∀ y z, 0 ≤ g y z)
    (_hlaw : ∀ y, (realDensityMeasure μ (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
        (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d z))).map
      (euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U b S x y) jetRows) =
      realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j))) (g y))
    (_hprojected : ∀ y y₀ (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q),
      (∑ v ∈ spatialWindow (trimmedSpatialRootScale τ N q) 4,
        g y (physicalCubeEuclideanSample U d p hm (physicalResidueReconstruction
          (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y₀)
          (allocatedPhysicalCubeDirections B U b S x y₀) base
          (boundedColumnResidueRepresentative q a) q v))) ≤
        (4 * (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X)) *
          (∏ t, ∏ _i : Unit ⊕ Fin dim, trimmedSpatialRootScale τ N q t))
    (_hσ1 : ∀ j, σ j ≤ 1)
    (_hpoint : ∀ u r z,
      |(allocatedLongResidueWeights B U b S (residueRefinedPeriod modulus q) hRefined r hlengths).mean
        (fun v => (∏ a, allocatedLongJetOutputScale B U b S (O := jets) a) *
          allocatedLongJetDensity B U b hR hσ S x u v jetRows s hA _hσ1 z) -
        allocatedLongJetProxy B U b S x u jetRows s hA modulus (residue u r) z| ≤ (η : ℝ))
    (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, jets a.val.1) → ℝ) → ℝ)
    (Cm : ℝ≥0) (_hCm : 1 ≤ (Cm : ℝ))
    (_hmasks : ∀ u r j z, 0 ≤ allocatedIntegerKernelMask B U b S x jetRows j modulus (residue u r j) z ∧
      allocatedIntegerKernelMask B U b S x jetRows j modulus (residue u r j) z ≤ Cm)
    {Cf Cg Kf Kg : ℝ≥0}
    (_hproxy : ∀ u, LipschitzWith Kf (allocatedContinuousLongJetProxy B U b S x u jetRows s hA))
    (_hf : LipschitzWith Kg f)
    (_hproxyBound : ∀ u z, |allocatedContinuousLongJetProxy B U b S x u jetRows s hA z| ≤ Cf)
    (_hfBound : ∀ z, |f z| ≤ Cg)
    {δp Lp : ℝ} (_hδp : 0 < δp) (_hLp : 0 ≤ Lp)
    (_hambp : (Fintype.card (JetAmbientIndex jets J) : ℝ) ≤ Lp) (_hδLp : δp⁻¹ ≤ Real.exp Lp)
    {Z : ℝ} (_hZ : 0 < Z),
    let Aprof := Real.toNNReal (coefficientDeckPeriodCap jets Q modulus) * Cm ^ Fintype.card (LayerSamplerAxis I n)
    (allocatedProfileErrorLip B U b S (O := jets) Aprof Cf Cg Kf Kg C V : ℝ) ≤ Real.exp Lp →
    Real.exp ((2 * Lp + 2) ^ 4) ≤ Real.exp P →
    Real.exp (2 * Lp * (2 * Lp + 2) ^ 4) * allocatedProfileErrorCap B U b S (O := jets) Aprof Cf Cg V ≤ Real.exp P →
    (∀ u, Integrable (allocatedUnmaskedLongProfileDensity B U b S
      (fun z => |allocatedContinuousLongJetProxy B U b S x u jetRows s hA z - f z|))
      (allocatedLongJetReference B U b S jets)) →
    ∀ Mprofile : ℝ,
    (∀ u, (Aprof : ℝ) * (∫ z, allocatedUnmaskedLongProfileDensity B U b S
      (fun v => |allocatedContinuousLongJetProxy B U b S x u jetRows s hA v - f v|) z
        ∂allocatedLongJetReference B U b S jets) ≤ Mprofile) →
    let Vsp := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / S.value) ^ dim) ^ Fintype.card X
    let Merr := (η : ℝ) * A *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, jets a.1)
    let mass := (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mean
      (allocatedRecenteredProfileMass (G := G) (dim := dim) (W := W) (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x N base cells (physicalCubeEuclideanSample U d p hm)
        (fun y z => (allocatedWholeMaskedCoveredProfile B U b hR hσ S x jetRows hb o bW d y modulus f z : ℂ)))
    mass / Z ≤ (coarseReferenceMassConstant dim X W S.value +
      Vsp * ((Merr + 2 * δf + ε) + (Mprofile + 2 * δp + ε))) / Z ∧
    ∀ {Pbound D : ℝ}, 0 ≤ Pbound → ((dim + 1 : ℕ) : ℝ) ≤ Pbound →
      (Fintype.card X : ℝ) ≤ Pbound → D ≤ Real.exp Pbound → W ≤ D * S.value →
      Z⁻¹ ≤ 2 → (Merr + 2 * δf + ε) + (Mprofile + 2 * δp + ε) ≤ 1 →
      mass / Z ≤ Real.exp (coefficientErrorVolumeLog Pbound + 4) := by
  obtain ⟨Kc, hKc, hcoeff⟩ := exists_allocated_recentered_error_window_bound m dim
  obtain ⟨Kp, hKp, hprofile⟩ := exists_allocated_recentered_profile_window_bound m dim
  refine ⟨max Kc Kp, hKc.trans (le_max_left _ _), ?_⟩
  intro G _ _ I _ n B _ J _ U b R σ hR hσ S x _ hb o Q _ bW d _ C V hC hV ν _ _
    modulus _ hperiod X _ _ q hq reference wholeReference N hN W τ ξ ρ hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift
    base cells hmass p hp hm P Rrank ε hP hX hdim hτP hstride hε hεP hsize hrank hRank
    η δf L hδf hL hamb hδL A hLip hfreqP hcoeffP hRefined instRefined
    s hA residue hlengths href hr _ _ _ Cinv hCinv hchart hsmall μ _ _ g hg hg0 hlaw hprojected
    hσ1 hpoint f Cm hCm hmasks Cf Cg Kf Kg hproxy hf hproxyBound hfBound
    δp Lp hδp hLp hambp hδLp Z hZ Aprof hLipP hfreqPP hcoeffPP hInt Mprofile hMass Vsp Merr mass
  have hKccut : Real.exp ((P + Kc)^Kc) ≤ Real.exp ((P + (max Kc Kp : ℕ))^max Kc Kp) :=
    Real.exp_le_exp.mpr (shifted_power_self_mono hP (by omega) (le_max_left _ _))
  have hKpcut : Real.exp ((P + Kp)^Kp) ≤ Real.exp ((P + (max Kc Kp : ℕ))^max Kc Kp) :=
    Real.exp_le_exp.mpr (shifted_power_self_mono hP (by omega) (le_max_right _ _))
  have hc := hcoeff B U b hR hσ S x hb o bW d C V hC hV ν modulus hperiod q hq reference wholeReference
    N hN hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift base cells hmass p hp hm
    hP hX hdim hτP hstride hε hεP (fun t => hKccut.trans (hsize t)) hrank (hKccut.trans hRank)
    η hδf hL hamb hδL hLip hfreqP hcoeffP
  have hresref u r := allocatedLongResidueWeights_reference_matrix B U b S x jetRows u
    (residueRefinedPeriod modulus q) hRefined r hlengths (reference u r) (href u r)
    modulus ⟨∏ t, q t, rfl⟩ (residue u r) (hr u r)
  have hpwindow u r := hprofile B U b hR hσ S x hb o bW d C V hC hV ν modulus hperiod q hq
    reference wholeReference N hN hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift base cells hmass p hp hm
    hP hX hdim hτP hstride hε hεP (fun t => hKpcut.trans (hsize t)) hrank (hKpcut.trans hRank)
    s hA residue u r (hresref u r) f Cm hCm (hmasks u r) (hproxy u) hf (hproxyBound u) hfBound
    hδp hLp hambp hδLp hLipP hfreqPP hcoeffPP (hInt u) Mprofile (hMass u)
  let profileError := fun u r z =>
    |allocatedRefinedReferenceProfile B U b hR hσ S x jetRows X modulus s hA q reference residue hb o bW d u r z -
      allocatedWholeMaskedCoveredProfile B U b hR hσ S x jetRows hb o bW d
        (principalAxisJoin (allocatedGridAxis (I := I) U b S.value) u (reference u r)) modulus f z|
  have hraw : mass ≤ coarseReferenceMassConstant dim X W S.value +
      Vsp * (Merr + 2 * δf + ε) + Vsp * (Mprofile + 2 * δp + ε) := by
    exact (allocatedRecenteredMaskedMass_of_density (G := G) (dim := dim)
      B U b hR hσ S x jetRows hb o bW d
    modulus f hperiod X q reference wholeReference N base cells (physicalCubeEuclideanSample U d p hm)
    g hσ1 Cinv hCinv hchart hsmall μ ν hg hg0 hlaw
    s hA residue hRefined hlengths href hr (η : ℝ)
    (Vsp * (Merr + 2 * δf + ε)) (Vsp * (Mprofile + 2 * δp + ε)) profileError
    hpoint (fun _ _ _ => le_rfl) hW hτ hξ hN hq hmass hprojected (by exact hc) (by exact hpwindow)).1
  have hn : mass / Z ≤ (coarseReferenceMassConstant dim X W S.value +
      Vsp * ((Merr + 2 * δf + ε) + (Mprofile + 2 * δp + ε))) / Z :=
    (div_le_div_of_nonneg_right hraw hZ.le).trans_eq (by ring)
  refine ⟨hn, ?_⟩
  intro Pbound D hPbound hdimBound hXbound hD hWD hZi herror
  have hprofilePos := smoothProbabilityProfile_pos_zero
  have hVsp : 0 ≤ Vsp := by dsimp only [Vsp]; positivity
  apply referenceProxyMass_exp_bound dim X hPbound hdimBound hXbound
    (by exact_mod_cast S.positive) hW hD hWD hZ hZi hn
  simpa only [mul_one] using mul_le_mul_of_nonneg_left herror hVsp

end Erdos3.VectorPolynomial

end

end OAI

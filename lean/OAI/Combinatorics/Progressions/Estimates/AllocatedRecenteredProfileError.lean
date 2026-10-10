import OAI.Combinatorics.Progressions.Probability.AllocatedFixedReferenceMass
import OAI.Combinatorics.Progressions.Probability.AllocatedRecenteredDensityMass

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable (m dim : ℕ)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

theorem exists_allocated_recentered_error_window_bound :
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
    let Vsp := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / S.value) ^ dim) ^ Fintype.card X
    let Merr := (η : ℝ) * A *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, jets a.1)
    ∀ u r, (∑ a : cells,
      selectedResidueCellWeight q cells
        (narrowTrimmedSpatialWidths (G := G)
          (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) a *
      ((∑ v ∈ spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4,
        allocatedRefinedReferenceErrorProfile B U b hR hσ S x jetRows X modulus q reference hb o bW d
          (η : ℝ) u r (physicalCubeEuclideanSample U d p hm
            (allocatedRecenteredFiberReconstruction (G := G) (dim := dim)
              B U b S X modulus q wholeReference x base u r a.val v))) /
        (∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
          (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i))) ≤
      Vsp * (Merr + 2 * δf + ε) := by
  obtain ⟨K, hK, htail⟩ := exists_allocated_weighted_error_tail m dim
  refine ⟨K, hK, ?_⟩
  intro G _ _ I _ n B _ J _ U b R σ hR hσ S x _ hb o Q _ bW d _ C V hC hV ν _ _
    modulus _ hperiod X _ _ q hq reference wholeReference N hN W τ ξ ρ hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift
    base cells hmass p hp hm P Rrank ε hP hX hdim hτP hstride hε hεP hsize hrank hRank
    η δf L hδf hL hamb hδL A hLip hfreqP hcoeffP Vsp Merr u r
  let _ := coefficientTorus_compact_of_lattice (K := Fin dim) U
  let _ : MeasurableSpace (CoefficientTorus (K := Fin dim) U) := borel _
  let _ : BorelSpace (CoefficientTorus (K := Fin dim) U) := ⟨rfl⟩
  let H := trimmedSpatialRootScale τ N q
  let T := trimmedSpatialSlopeScale W τ N q
  let Vs := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
  let y := wholeReference
    (principalAxisResidueJoin (allocatedGridAxis (I := I) U b S.value) u (residueRefinedPeriod modulus q) r)
  have hgeo (t : X) := allocatedNarrow_reference_jet_geometry B U b S (fun _ => 0) x y N q hN hq
    hW hτ hξ1 hρ hsizeSp hρ8 hρshift t
  have hH (t) : 0 < H t := (hgeo t).1
  have hT (t) : 0 < T t := (trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)).2
  have hscale : 0 < ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t) (T t) S.value i :=
    Finset.prod_pos (fun t _ => Finset.prod_pos (fun i _ =>
      physicalSpatialOutputScale_pos (Fin dim) (hH t) (hT t) (Nat.cast_pos.mpr S.positive) i))
  have h := htail hP hX hdim U (probabilityAddHaar _) ν p hp hm d q hq
    (Real.exp_pos P).le le_rfl hτ hε hτP hεP hstride (fun t => (N t : ℝ)) hsize hrank hRank
    (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y) (allocatedPhysicalCubeDirections B U b S x y)
    base cells Vs (narrowTrimmedSpatialWidths_pos hW hτ hξ N hN) hmass H T hH hT
    (Nat.cast_pos.mpr S.positive) (trimmedSpatial_scale_ratio hW N q)
    (fun t => (hgeo t).2.1) (fun t => (hgeo t).2.2.1) (fun t => (hgeo t).2.2.2)
    (fun _ => (1 : ℂ)) zero_le_one (by intro w hw; simp) (fun _ => (1 : ℂ)) (by intro w; simp)
    B b S o hR hσ x u (reference u r) jetRows hb bW modulus hperiod
    η C V hC hV hδf hL hamb hδL hLip hfreqP hcoeffP
  dsimp only at h
  simp only [one_mul] at h
  have hsum (a : cells) (f : (X → Unit ⊕ Fin dim → ℤ) → ℝ) :
      selectedResidueCellWeight q cells Vs a *
        ((∑ v ∈ spatialWindow (α := Fin dim) H 4, f v) /
          (∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t) (T t) S.value i)) =
      ∑ v : spatialWindow (α := Fin dim) H 4,
        ‖(selectedResidueCellWeight q cells Vs a : ℂ) *
          ((1 : ℂ) / ((∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t) (T t) S.value i : ℝ) : ℂ)) * 1‖ * f v.val := by
    rw [mul_one, norm_mul, norm_div, norm_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (selectedResidueCellWeight_nonneg q cells Vs a), abs_of_pos hscale]
    rw [← Finset.mul_sum, ← Finset.sum_subtype (spatialWindow (α := Fin dim) H 4) (fun _ => Iff.rfl) f]
    ring
  unfold allocatedRefinedReferenceErrorProfile allocatedRecenteredFiberReconstruction
    allocatedWholeResidueReconstruction
  dsimp only
  convert h using 1
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  exact hsum a _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable (m dim : ℕ)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

theorem exists_allocated_recentered_profile_window_bound :
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
    (s : ∀ j, jets j ↪ BoundedIntegerExponent G (j.val + 1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (jetRows j)).submatrix id (s j)).det ≠ 0)
    (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
        (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      ∀ j, Matrix (jets j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (u : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
      (allocatedPrincipalSides B U b S))
    (r : PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
      (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q))
    (_hresidue : ∀ j, integerResidueMatrix
      (allocatedNonkernelJetMatrix B U b S x u jetRows j (reference u r)) modulus = residue u r j)
    (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, jets a.val.1) → ℝ) → ℝ)
    (Cm : ℝ≥0) (_hCm : 1 ≤ (Cm : ℝ))
    (_hmasks : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x jetRows j modulus (residue u r j) z ∧
      allocatedIntegerKernelMask B U b S x jetRows j modulus (residue u r j) z ≤ Cm)
    {Cf Cg Kf Kg : ℝ≥0}
    (_hproxy : LipschitzWith Kf (allocatedContinuousLongJetProxy B U b S x u jetRows s hA))
    (_hf : LipschitzWith Kg f)
    (_hproxyBound : ∀ z, |allocatedContinuousLongJetProxy B U b S x u jetRows s hA z| ≤ Cf)
    (_hfBound : ∀ z, |f z| ≤ Cg)
    {δf L : ℝ} (_hδf : 0 < δf) (_hL : 0 ≤ L)
    (_hamb : (Fintype.card (JetAmbientIndex jets J) : ℝ) ≤ L) (_hδL : δf⁻¹ ≤ Real.exp L),
    let A := Real.toNNReal (coefficientDeckPeriodCap jets Q modulus) * Cm ^ Fintype.card (LayerSamplerAxis I n)
    (allocatedProfileErrorLip B U b S (O := jets) A Cf Cg Kf Kg C V : ℝ) ≤ Real.exp L →
    Real.exp ((2 * L + 2) ^ 4) ≤ Real.exp P →
    Real.exp (2 * L * (2 * L + 2) ^ 4) * allocatedProfileErrorCap B U b S (O := jets) A Cf Cg V ≤ Real.exp P →
    Integrable (allocatedUnmaskedLongProfileDensity B U b S
      (fun z => |allocatedContinuousLongJetProxy B U b S x u jetRows s hA z - f z|))
      (allocatedLongJetReference B U b S jets) →
    ∀ M : ℝ,
    (A : ℝ) * (∫ z, allocatedUnmaskedLongProfileDensity B U b S
      (fun v => |allocatedContinuousLongJetProxy B U b S x u jetRows s hA v - f v|) z
        ∂allocatedLongJetReference B U b S jets) ≤ M →
    let Vsp := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / S.value) ^ dim) ^ Fintype.card X
    (∑ a : cells,
      selectedResidueCellWeight q cells
        (narrowTrimmedSpatialWidths (G := G)
          (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) a *
      ((∑ v ∈ spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4,
        |allocatedRefinedReferenceProfile B U b hR hσ S x jetRows X modulus s hA q reference residue hb o bW d
            u r (physicalCubeEuclideanSample U d p hm
              (allocatedRecenteredFiberReconstruction (G := G) (dim := dim)
                B U b S X modulus q wholeReference x base u r a.val v)) -
          allocatedWholeMaskedCoveredProfile B U b hR hσ S x jetRows hb o bW d
            (principalAxisJoin (allocatedGridAxis (I := I) U b S.value) u (reference u r)) modulus f
            (physicalCubeEuclideanSample U d p hm
              (allocatedRecenteredFiberReconstruction (G := G) (dim := dim)
                B U b S X modulus q wholeReference x base u r a.val v))|) /
        (∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
          (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i))) ≤
      Vsp * (M + 2 * δf + ε) := by
  obtain ⟨K, hK, htail⟩ := exists_allocated_weighted_profile_error m dim
  refine ⟨K, hK, ?_⟩
  intro G _ _ I _ n B _ J _ U b R σ hR hσ S x _ hb o Q _ bW d _ C V hC hV ν _ _
    modulus _ hperiod X _ _ q hq reference wholeReference N hN W τ ξ ρ hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift
    base cells hmass p hp hm P Rrank ε hP hX hdim hτP hstride hε hεP hsize hrank hRank
    s hA residue u r hresidue f Cm hCm hmasks Cf Cg Kf Kg hproxy hf hproxyBound hfBound
    δf L hδf hL hamb hδL A hLip hfreqP hcoeffP hi M hMass Vsp
  let _ := coefficientTorus_compact_of_lattice (K := Fin dim) U
  let _ : MeasurableSpace (CoefficientTorus (K := Fin dim) U) := borel _
  let _ : BorelSpace (CoefficientTorus (K := Fin dim) U) := ⟨rfl⟩
  let H := trimmedSpatialRootScale τ N q
  let T := trimmedSpatialSlopeScale W τ N q
  let Vs := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
  let y := wholeReference
    (principalAxisResidueJoin (allocatedGridAxis (I := I) U b S.value) u (residueRefinedPeriod modulus q) r)
  have hgeo (t : X) := allocatedNarrow_reference_jet_geometry B U b S (fun _ => 0) x y N q hN hq
    hW hτ hξ1 hρ hsizeSp hρ8 hρshift t
  have hH (t) : 0 < H t := (hgeo t).1
  have hT (t) : 0 < T t := (trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)).2
  have hscale : 0 < ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t) (T t) S.value i :=
    Finset.prod_pos (fun t _ => Finset.prod_pos (fun i _ =>
      physicalSpatialOutputScale_pos (Fin dim) (hH t) (hT t) (Nat.cast_pos.mpr S.positive) i))
  have h := htail hP hX hdim U (probabilityAddHaar _) ν p hp hm d q hq
    (Real.exp_pos P).le le_rfl hτ hε hτP hεP hstride (fun t => (N t : ℝ)) hsize hrank hRank
    (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y) (allocatedPhysicalCubeDirections B U b S x y)
    base cells Vs (narrowTrimmedSpatialWidths_pos hW hτ hξ N hN) hmass H T hH hT
    (Nat.cast_pos.mpr S.positive) (trimmedSpatial_scale_ratio hW N q)
    (fun t => (hgeo t).2.1) (fun t => (hgeo t).2.2.1) (fun t => (hgeo t).2.2.2)
    (fun _ => (1 : ℂ)) zero_le_one (by intro w hw; simp) (fun _ => (1 : ℂ)) (by intro w; simp)
    B b S o hR hσ x u (reference u r) jetRows hb bW modulus hperiod
    modulus (residue u r) Cm hCm hmasks
    (allocatedContinuousLongJetProxy B U b S x u jetRows s hA) f
    hproxy hf hproxyBound hfBound C V hC hV hδf hL hamb hδL hLip hfreqP hcoeffP hi M hMass
  dsimp only at h
  simp only [one_mul] at h
  have hsum (a : cells) (f : (X → Unit ⊕ Fin dim → ℤ) → ℝ) :
      selectedResidueCellWeight q cells Vs a *
        ((∑ v ∈ spatialWindow (α := Fin dim) H 4, f v) /
          (∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t) (T t) S.value i)) =
      ∑ v : spatialWindow (α := Fin dim) H 4,
        ‖(selectedResidueCellWeight q cells Vs a : ℂ) *
          ((1 : ℂ) / ((∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t) (T t) S.value i : ℝ) : ℂ)) * 1‖ * f v.val := by
    rw [mul_one, norm_mul, norm_div, norm_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (selectedResidueCellWeight_nonneg q cells Vs a), abs_of_pos hscale]
    rw [← Finset.mul_sum, ← Finset.sum_subtype (spatialWindow (α := Fin dim) H 4) (fun _ => Iff.rfl) f]
    ring
  have hwhole : allocatedWholeMaskedCoveredProfile B U b hR hσ S x jetRows hb o bW d
      (principalAxisJoin (allocatedGridAxis (I := I) U b S.value) u (reference u r)) modulus f =
      allocatedCoveredProfileDensity B U b hR hσ S x u (reference u r) jetRows hb o bW d
        (fun j _ => standardLatticeClosedQuarterBox (J j))
        (allocatedLongProfileDensity B U b S x jetRows modulus (residue u r) f) := by
    simp only [allocatedWholeMaskedCoveredProfile, principalAxisRestrict_join_left,
      principalAxisRestrict_join_right]
    rw [show (fun j => integerResidueMatrix
      (allocatedNonkernelJetMatrix B U b S x u jetRows j (reference u r)) modulus) = residue u r
        from funext hresidue]
  rw [allocatedRefinedReferenceProfile_as_covered B U b hR hσ S x jetRows X modulus s hA q
    reference residue hb o bW d u r, hwhole]
  unfold allocatedRecenteredFiberReconstruction allocatedWholeResidueReconstruction
  convert h using 1
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  exact hsum a _

end Erdos3.VectorPolynomial

end

end OAI

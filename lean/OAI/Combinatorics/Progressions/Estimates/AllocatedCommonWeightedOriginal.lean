import OAI.Combinatorics.Progressions.Estimates.AllocatedFlexibleOriginalMesh

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset (Fin dim))

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

variable (X : Type*) [Fintype X]

local notation "whole" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) sides (allocatedPrincipalSides_pos B U b S)
local notation "frozen" => allocatedFrozenTupleWeights (α := Fin dim) B U b S
local notation "long" => allocatedLongTupleWeights (α := Fin dim) B U b S

variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Module.Basis (Kcov j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

def AllocatedChosenProjectedIdealAt (P E η : ℝ) (δideal : ℝ≥0) : Prop :=
    ∀ (_hP : 0 ≤ P) (_hE : 0 ≤ E)
    (_hmP : ((m + 1 : ℕ) : ℝ) ≤ P) (_hdimP : ((dim + 1 : ℕ) : ℝ) ≤ P)
    (_hGP : (Fintype.card G : ℝ) ≤ P) (_hXP : (Fintype.card X : ℝ) ≤ P)
    (_hMP : (M : ℝ) ≤ Real.exp P) (_hmodulus : modulus ≤ M ^ (m + 1))
    (_hqpos : ∀ t, 0 < q t) (_hσ1 : ∀ j, σ j ≤ 1),
    let indices := PrincipalTupleIndex B (layerSamplerDegree I n)
    let ξ := normalizedTupleNarrowWidth X indices selection M P (E + 1)
    let hξ := normalizedTupleNarrowWidth_pos X indices selection M P (E + 1)
    ξ ≤ 1 ∧ ξ⁻¹ ≤ Real.exp (normalizedTupleWidthLog indices selection P (E + 1)) ∧
    ∀ [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
        [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
        [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
        [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
        (C : Fin m → ℝ) (_hC : ∀ j, 0 ≤ C j)
        (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
        (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) C 1 j)
        (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
        [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
        (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
        [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
        (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides → EuclideanJetLayers U O → ℝ)
        (_hg : ∀ w, Continuous (g w)) (_hg0 : ∀ w z, 0 ≤ g w z)
        (_hlaw : ∀ w, (realDensityMeasure μ (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
          (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d z))).map
          (euclideanCoefficientJetMap U
            (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x w)
            (allocatedPhysicalCubeDirections B U b S x w) rows) =
          realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) (g w))
    {W τ C₀ Cg Z growth l : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ)
    (_hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (_hC₀ : 1 ≤ C₀) (_hLC : (S.value : ℝ) ≤ C₀) (_hWC : W ≤ C₀)
    (_hCg : 0 ≤ Cg) (_hZ : 1 / 2 ≤ Z)
    (_hgrowth : growth ≤ Real.exp P) (_hWscale : W ≤ growth * (S.value : ℝ))
    (_hl : 0 ≤ l) (_hC₀l : C₀ ≤ Real.exp l) (_hWl : W ≤ Real.exp l)
    (_hCgl : Cg ≤ Real.exp l)
    (_hentryl : allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ Real.exp l)
    (_hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp l)
    (_hql : ∀ t, (q t : ℝ) ≤ Real.exp l) (_hτl : τ⁻¹ ≤ Real.exp l),
    let Centry := allocatedPhysicalEntryBudget B U b S (fun _ => 0)
    let δsp := normalizedTupleRadius X selection M P (E + 1) W
    let mesh := δsp / 4
    let ρ := normalizedTupleResolution X indices selection M P (E + 1) C₀ W Cg Centry
    0 < δsp ∧ 0 < mesh ∧ 0 < ρ ∧
    δsp⁻¹ ≤ Real.exp (3 * normalizedTupleLateBudget X indices selection P (E + 1) l + 8) ∧
    mesh⁻¹ ≤ Real.exp (3 * normalizedTupleLateBudget X indices selection P (E + 1) l + 8) ∧
    ρ ≤ Real.exp (3 * normalizedTupleLateBudget X indices selection P (E + 1) l + 8) ∧
    ∀ (N : X → ℕ) (hN : ∀ t, 0 < N t)
    (_hside : ∀ t, Real.exp (normalizedTupleSideLog X indices selection P (E + 1) l) ≤ (N t : ℝ))
    (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := indices) W τ ξ N) z)
    (point : (X → Unit ⊕ Fin dim → ℤ) → EuclideanJetLayers U O)
    (test : (X → Unit ⊕ Fin dim → ℤ) → ℂ) (_htest : ∀ v, ‖test v‖ ≤ 1)
    (_hcap : ∀ y v, g y (point v) ≤ Cg)
    (_hreferenceMass : ∀ y y₀ (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q),
      (∑ v ∈ spatialWindow (trimmedSpatialRootScale τ N q) 4,
        g y (point (physicalResidueReconstruction
          (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y₀)
          (allocatedPhysicalCubeDirections B U b S x y₀) base
          (boundedColumnResidueRepresentative q a) q v))) ≤
        (4 * (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X)) *
          (∏ t, ∏ _i : Unit ⊕ Fin dim, trimmedSpatialRootScale τ N q t)),
    allocatedRefinedReferenceTailBound (τ := τ) (ξ := ξ)
      B U b hR hσ S x rows X hM selection hx modulus q reference hb o bW d
      N hW mesh base cells point test η (Z * Real.exp (-(E + 3))) →
    ‖allocatedRefinedTupleReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x rows X hM selection hx modulus s hA q reference residue hb o bW d
        N hW mesh base cells point test Z -
      allocatedRefinedIdealReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x rows X hM selection hx modulus q reference residue hb o bW d
        N hW mesh base cells point test Z δideal‖ ≤ Real.exp (-(E + 3)) →
    ‖allocatedProjectedTupleSource B U b S x X q g N hN hW hτ hξ base cells hmass point test Z -
      allocatedRefinedIdealReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x rows X hM selection hx modulus q reference residue hb o bW d
        N hW mesh base cells point test Z δideal‖ ≤ Real.exp (-E)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset (Fin dim))

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

variable (X : Type*) [Fintype X]

local notation "whole" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) sides (allocatedPrincipalSides_pos B U b S)
local notation "frozen" => allocatedFrozenTupleWeights (α := Fin dim) B U b S
local notation "long" => allocatedLongTupleWeights (α := Fin dim) B U b S

variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Module.Basis (Kcov j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

theorem allocatedFixedData_chosen_projected_ideal {P E η : ℝ} (δideal : ℝ≥0)
    (hsource : AllocatedFixedDataSourceAt B U b hR hσ S x rows X hM selection hx modulus s hA
      q reference residue hb o bW d η) :
    AllocatedChosenProjectedIdealAt B U b hR hσ S x rows X hM selection hx modulus s hA
      q reference residue hb o bW d P E η δideal := by
  unfold AllocatedChosenProjectedIdealAt
  intro hP hE hmP hdimP hGP hXP hMP hmodulus hqpos hσ1 indices ξ hξ
  have hE1 : 0 ≤ E + 1 := by linarith
  obtain ⟨_hξ, hξ1, hξlog, hchoices⟩ := normalizedTupleSpatialChoices
    (N := indices) (X := X) (m := m) selection hM hP hE1 hmP hdimP hGP hXP hMP
  refine ⟨hξ1, hξlog, ?_⟩
  intro _ _ _ _ C hC hchart hsmall μ _ _ ν _ _ g hg hg0 hlaw
    W τ C₀ Cg Z growth l hW hτ hbudget hC₀ hLC hWC hCg hZ hgrowth hWscale
    hl hC₀l hWl hCgl hentryl hprofile hql hτl Centry δsp mesh ρ
  have hCentry : 0 ≤ Centry := zero_le_one.trans (allocatedPhysicalEntryBudget_one_le B U b S (fun _ => 0))
  have hC₀0 : 0 ≤ C₀ := zero_le_one.trans hC₀
  have hS1 : (1 : ℝ) ≤ S.value := by exact_mod_cast (Nat.succ_le_iff.mpr S.positive)
  obtain ⟨hδ, _hδ1, hmesh, hρ, hmeshSize, hρ8, hshift, hmove, hboundary, hspatial⟩ :=
    hchoices hC₀0 hW hS1 hCg hCentry hgrowth hWscale
  have hqcard : (Fintype.card (Unit ⊕ Fin dim) : ℝ) ≤ P := by
    simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Nat.add_comm 1] using hdimP
  obtain ⟨hδlog, hmeshlog, hρlog⟩ := normalizedTupleLateParameters_bound X indices selection
    hP hE1 hl hM hMP hqcard hGP hXP hC₀0 hW hCentry hC₀l hWl hCgl hentryl hprofile
  refine ⟨hδ, hmesh, hρ, hδlog, hmeshlog, hρlog, ?_⟩
  intro N hN hside base cells hmass point test htest hcap hreferenceMass htail hideal
  have hphysicalSize (t : X) : 8 * (1 + W) * (q t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ) :=
    normalizedTupleSpatialSize X indices selection hP hE1 hl hM hmP hdimP hGP hXP hMP
      hC₀0 hW hCg hCentry hC₀l hWl hCgl hentryl hprofile (Nat.cast_nonneg _) (hql t)
      hτ hτl (hside t)
  have hZpos : 0 < Z := by linarith
  have hmassEstimate := hsource hqpos hσ1 C hC hchart hsmall μ ν g hg hg0 hlaw N hN
    hW hτ hρ hbudget hC₀ hLC hWC hξ hξ1 hphysicalSize hmeshSize hρ8 hδ.le
    (by simpa only [mul_assoc] using hshift) hmove hmesh base cells hmass point test htest hCg hZpos hcap hreferenceMass
  have htail' : allocatedRefinedReferenceTailBound (τ := τ) (ξ := ξ)
      B U b hR hσ S x rows X hM selection hx modulus q reference hb o bW d
      N hW mesh base cells point test η (Z * normalizedSpatialShare (E + 1)) := by
    simpa only [normalizedSpatialShare, show (E + 1) + 2 = E + 3 by ring] using htail
  have hscalar := allocatedRefinedTupleMassEstimate_scalar B U b hR hσ S x rows X hM selection hx
    modulus s hA q reference residue hb o bW d g N hN hW hτ hξ C₀ ρ δsp mesh
    base cells hmass point test Cg Z η hZpos hmassEstimate htail'
  have hcomparison := allocatedRefinedTupleDifference_exp_bound B U b hR hσ S x rows X hM selection hx
    modulus s hA q reference residue hb o bW d g N hN hW hτ hξ C₀ ρ δsp mesh
    base cells hmass point test Cg Z hZ hscalar hboundary (hspatial modulus hmodulus)
  rw [allocatedRefinedTupleDifference_decomposition] at hcomparison
  have hsmall : Real.exp (-(E + 1)) + Real.exp (-(E + 3)) ≤ Real.exp (-E) := by
    have hmono : Real.exp (-(E + 3)) ≤ Real.exp (-(E + 1)) :=
      Real.exp_le_exp.mpr (by linarith)
    calc
      _ ≤ 2 * Real.exp (-(E + 1)) := by linarith
      _ ≤ Real.exp 1 * Real.exp (-(E + 1)) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hcomparison hideal)).trans hsmall

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

universe uX

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "rows" => (fun j : Fin m => (Subtype.val : jets j → Finset (Fin dim)))

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

variable (X : Type uX) [Fintype X] [DecidableEq X]

local notation "whole" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) sides (allocatedPrincipalSides_pos B U b S)
local notation "frozen" => allocatedFrozenTupleWeights (α := Fin dim) B U b S
local notation "long" => allocatedLongTupleWeights (α := Fin dim) B U b S

variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus]
variable (s : ∀ j : Fin m, BoundedBooleanJet (Fin dim) (j.val + 1) ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j : Fin m, ((scalarKernelIntegerJet x (j.val + 1)
  (Subtype.val : BoundedBooleanJet (Fin dim) (j.val + 1) → Finset (Fin dim))).submatrix id (s j)).det ≠ 0)
variable (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  ∀ j : Fin m, Matrix (BoundedBooleanJet (Fin dim) (j.val + 1))
    (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Module.Basis (Kcov j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

theorem allocatedFixedData_chosen_original_ideal {Pbase P E η : ℝ} {Kproj : ℕ} (δideal : ℝ≥0)
    (hsource : AllocatedFixedDataSourceAt B U b hR hσ S x rows X hM selection hx modulus s hA
      q reference residue hb o bW d η) :
    AllocatedChosenOriginalIdealAt B U b hR hσ S x X hM selection hx modulus s hA
      q reference residue hb o bW d Pbase Kproj P E η δideal := by
  have hchosen := allocatedFixedData_chosen_projected_ideal B U b hR hσ S x rows X hM selection hx
    modulus s hA q reference residue hb o bW d (P := P) (E := E + 1) δideal hsource
  unfold AllocatedChosenProjectedIdealAt at hchosen
  simp only [show (E + 1) + 1 = E + 2 by ring, show (E + 1) + 3 = E + 4 by ring] at hchosen
  unfold AllocatedChosenOriginalIdealAt
  intro hP hE hmP hdimP hGP hXP hMP hmodulus hqpos hσ1 indices ξ hξ
  obtain ⟨hξ1, hξlog, hchosen⟩ :=
    hchosen hP (by linarith : 0 ≤ E + 1) hmP hdimP hGP hXP hMP hmodulus hqpos hσ1
  refine ⟨hξ1, hξlog, ?_⟩
  intro _ _ _ _ C hC hchart hsmall μ _ _ ν _ _ g hg hg0 hlaw hprojection
    W τ C₀ Cg Z growth l hW hτ hbudget hC₀ hLC hWC hCg hZ hgrowth hWscale
    hl hC₀l hWl hCgl hentryl hprofile hql hτl Centry δsp mesh ρ
  obtain ⟨hδ, hmesh, hρ, hδlog, hmeshlog, hρlog, hcomparison⟩ :=
    hchosen C hC hchart hsmall μ ν g hg hg0 hlaw hW hτ hbudget hC₀ hLC hWC hCg hZ
      hgrowth hWscale hl hC₀l hWl hCgl hentryl hprofile hql hτl
  refine ⟨hδ, hmesh, hρ, hδlog, hmeshlog, hρlog, ?_⟩
  intro Q hPbaseQ hlQ hEQ hwidthQ hXQ hdimQ N hN hside hsizeProj poly hpoly hmem rank hrank hRank
    base cells hcells hmass test htest point siteTest hcap hreferenceMass htail hideal
  have htest' : ∀ v, ‖siteTest v‖ ≤ 1 := physicalCubeSiteTest_norm_le test htest
  have hprojected := hcomparison N hN hside base cells hmass point siteTest htest' hcap
    hreferenceMass htail hideal
  have hlExp := Real.exp_le_exp.mpr hlQ
  have horiginal := hprojection hPbaseQ (by linarith : 1 ≤ Q) hXQ hdimQ
    poly hpoly hmem base q hqpos (fun t => (hql t).trans hlExp) hW hbudget
    (hWl.trans hlExp) hτ (hτl.trans hlExp) hξ hξ1
    (hξlog.trans (Real.exp_le_exp.mpr hwidthQ)) N hN hsizeProj hrank hRank test htest cells hcells hZ hmass
  have hsum : Real.exp (-Q) + Real.exp (-(E + 1)) ≤ Real.exp (-E) := by
    have hmono : Real.exp (-Q) ≤ Real.exp (-(E + 1)) :=
      Real.exp_le_exp.mpr (neg_le_neg hEQ)
    calc
      _ ≤ 2 * Real.exp (-(E + 1)) := by linarith
      _ ≤ Real.exp 1 * Real.exp (-(E + 1)) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add horiginal hprojected)).trans hsum

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uG uI uB uGeom uCover uSpace

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {dim : ℕ}

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

section FixedScale

variable {J : Fin m → Type uGeom} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

def AllocatedOriginalPrescribedAtScale (D Psp E e pNum : ℝ) (δ : ℝ≥0)
    (A T Kproj Kideal : ℕ) : Prop :=
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
  let error := allocatedReferenceIdealError m D Psp (E + 4)
  let gainLog := allocatedProfileGainLog m D Psp w
  let S := allocatedIdealScale (G := G) B U b hR hσ D pNum e w error
  let lengthLog := allocatedIdealScaleLog m D pNum e w error
  let Pbase := allocatedIdealSourceBudget m D pNum e w error
  let l := allocatedSpatialLateLog (G := G) B Pbase Pbase
  let F := allocatedProfileFourierOutput (allocatedActualProfileInput m D pNum e gainLog lengthLog)
  let Q := allocatedSourceSamplingBudget m dim A Pbase E l F
  let K := max T (max Kproj Kideal)
  (S.value : ℝ) ≤ Real.exp lengthLog ∧
  ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    {Mk : ℕ} (hMk : 0 < Mk) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (_hqDim : dim ≤ m + 1) (_hMkPsp : (Mk : ℝ) ≤ Real.exp Psp),
  ∃ (d : ℕ) (hd : 0 < d),
    let : NeZero d := ⟨hd.ne'⟩
    (d : ℝ) ≤ Real.exp ((Pbase + A) ^ A) ∧
  ∀ (modulus : ℕ) (hmodulus : 0 < modulus),
    let : NeZero modulus := ⟨hmodulus.ne'⟩
    ∀ (_hmodulusSize : modulus ≤ Mk ^ (m + 1))
      (_hspatialPeriod : ∀ root : G → ℤ, integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
        pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
          (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection))
      (_hcoefficientPeriod : ∀ j, integerScalarLattice (jets j) (modulus : ℤ) ≤
        (scalarKernelIntegerJet x (j.val + 1) (jetRows j)).mulVecLin.range),
    ∃ (s : ∀ j, jets j ↪ BoundedIntegerExponent G (j.val + 1))
      (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (jetRows j)).submatrix id (s j)).det ≠ 0),
    (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (jetRows j) (s j) (hA j) (1 / (Mk : ℝ))) ∧
    ∀ (_block : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, jets a.val.1 ↪ B a.val)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin dim)) U)] [BorelSpace (SiteTorus (Finset (Fin dim)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Kcov : Fin m → Type uCover} [∀ j, Fintype (Kcov j)]
    (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCp : ∀ j, (C j : ℝ) ≤ Real.exp pNum) (_hVp : ∀ j, (V j : ℝ) ≤ Real.exp pNum)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv 1 j)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {X : Type uSpace} [Fintype X] [DecidableEq X]
    (_hXPsp : (Fintype.card X : ℝ) ≤ Psp)
    (q : X → ℕ) (_hq : ∀ t, 0 < q t) (_hqPsp : ∀ t, (q t : ℝ) ≤ Real.exp Psp),
    let refined := residueRefinedPeriod modulus q
    ∃ hRefined : 0 < refined,
    let : NeZero refined := ⟨hRefined.ne'⟩
    (∀ t, q t * modulus ∣ refined) ∧
    (refined : ℝ) ≤ Real.exp ((m + 1 : ℕ) * Psp + Fintype.card X * Psp) ∧
    ∃ hsize : ∀ a, (Fintype.card (Fin dim) + 1) * refined ≤
      principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
        (allocatedPrincipalSides B U b S) a,
    ∃ (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
    (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      ∀ j, Matrix (jets j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)),
    (∀ u r, principalResidueLabel refined (reference u r) = r) ∧
    (∀ u r v, (allocatedLongResidueWeights B U b S refined hRefined r hsize).weight v ≠ 0 →
      ∀ j, integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u jetRows j v) modulus = residue u r j) ∧
    let W := allocatedPhysicalRootBudget B U b S (fun _ => 0)
    let hW := allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)
    let indices := PrincipalTupleIndex B (layerSamplerDegree I n)
    let ξ := normalizedTupleNarrowWidth X indices selection Mk Psp (E + 2)
    let hξ := normalizedTupleNarrowWidth_pos X indices selection Mk Psp (E + 2)
    let mesh := normalizedTupleRadius X selection Mk Psp (E + 2) W / 4
    ∀ {τ : ℝ} (hτ : 0 < τ) (_hτP : 1 / τ ≤ Real.exp pNum)
    (N : X → ℕ) (hN : ∀ t, 0 < N t)
    (_hsize : ∀ t, Real.exp ((Q + K) ^ K) ≤ (N t : ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
    {rank : ℝ}
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) rank (U j) (poly j))
    (_hRank : Real.exp ((Q + K) ^ K) ≤ rank)
    (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hcells : cells.Nonempty)
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) (_htest : ∀ site v, ‖test site v‖ ≤ 1)
    (Z : ℝ) (_hZ : 1 / 2 ≤ Z),
    ∃ hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := indices) W τ ξ N) z,
    ‖allocatedOriginalTupleSource B U b hR hσ S x X q hb o N hN hW hτ hξ base cells hmass
        (physicalCubeSiteTest test) Z poly hmem -
      allocatedRefinedIdealReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x jetRows X hMk selection hx modulus q reference residue hb o bW d
        N hW mesh base cells (physicalCubeEuclideanSample U d poly hmem) (physicalCubeSiteTest test) Z δ‖ ≤
      Real.exp (-E)

end FixedScale

def AllocatedOriginalPrescribedAt (D Psp E e t : ℝ) (δ : ℝ≥0) (A T Kproj Kideal : ℕ) : Prop :=
  ∀ (_hmPsp : ((m + 1 : ℕ) : ℝ) ≤ Psp) (_hdimPsp : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (_hGPsp : (Fintype.card G : ℝ) ≤ Psp)
    (_hvarsGrowth : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp Psp)
    {J : Fin m → Type uGeom} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (_hσt : ∀ j, σ j ≤ t)
    {pNum : ℝ} (_hPspNum : Psp ≤ pNum)
    (_hcount : ∀ j : Fin m, (Fintype.card
      (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp pNum)
    (_herrorNum : profileReferenceErrorLog Psp (E + 4) ≤ pNum)
    (_hRefineNum : (m + 1 : ℕ) * Psp + Psp ^ 2 + (dim + 1 : ℕ) ≤ pNum)
    (_hRP : ∀ j, R j ≤ Real.exp pNum) (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp pNum)
    (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp pNum),
  AllocatedOriginalPrescribedAtScale.{uG,uI,uB,uGeom,uCover,uSpace}
    (G := G) (dim := dim) B U b hR hσ D Psp E e pNum δ A T Kproj Kideal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uG uI uB uGeom uCover uSpace

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {dim : ℕ}

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

def AllocatedOriginalSelectedAt (D Psp E e t : ℝ) (δ : ℝ≥0) (A T Kproj Kideal : ℕ) : Prop :=
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
  let error := allocatedReferenceIdealError m D Psp (E + 4)
  let gainLog := allocatedProfileGainLog m D Psp w
  ∀ (_hmPsp : ((m + 1 : ℕ) : ℝ) ≤ Psp) (_hdimPsp : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (_hGPsp : (Fintype.card G : ℝ) ≤ Psp)
    (_hvarsGrowth : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp Psp)
    {J : Fin m → Type uGeom} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (_hσt : ∀ j, σ j ≤ t)
    {pNum : ℝ} (_hPspNum : Psp ≤ pNum)
    (_hcount : ∀ j : Fin m, (Fintype.card
      (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp pNum)
    (_herrorNum : profileReferenceErrorLog Psp (E + 4) ≤ pNum)
    (_hRefineNum : (m + 1 : ℕ) * Psp + Psp ^ 2 + (dim + 1 : ℕ) ≤ pNum)
    (_hRP : ∀ j, R j ≤ Real.exp pNum) (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp pNum)
    (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp pNum),
  let S := allocatedIdealScale (G := G) B U b hR hσ D pNum e w error
  let lengthLog := allocatedIdealScaleLog m D pNum e w error
  let Pbase := allocatedIdealSourceBudget m D pNum e w error
  let l := allocatedSpatialLateLog (G := G) B Pbase Pbase
  let F := allocatedProfileFourierOutput (allocatedActualProfileInput m D pNum e gainLog lengthLog)
  let Q := allocatedSourceSamplingBudget m dim A Pbase E l F
  let K := max T (max Kproj Kideal)
  (S.value : ℝ) ≤ Real.exp lengthLog ∧
  ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    {Mk : ℕ} (hMk : 0 < Mk) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (_hqDim : dim ≤ m + 1) (_hMkPsp : (Mk : ℝ) ≤ Real.exp Psp),
  ∃ (d : ℕ) (hd : 0 < d),
    let : NeZero d := ⟨hd.ne'⟩
    (d : ℝ) ≤ Real.exp ((Pbase + A) ^ A) ∧
  ∃ (modulus : ℕ) (hmodulus : 0 < modulus),
    let : NeZero modulus := ⟨hmodulus.ne'⟩
    modulus ≤ Mk ^ (m + 1) ∧
    (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
    (∀ j, integerScalarLattice (jets j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (jetRows j)).mulVecLin.range) ∧
    ∃ (s : ∀ j, jets j ↪ BoundedIntegerExponent G (j.val + 1))
      (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (jetRows j)).submatrix id (s j)).det ≠ 0),
    (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (jetRows j) (s j) (hA j) (1 / (Mk : ℝ))) ∧
    ∀ (_block : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, jets a.val.1 ↪ B a.val)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin dim)) U)] [BorelSpace (SiteTorus (Finset (Fin dim)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Kcov : Fin m → Type uCover} [∀ j, Fintype (Kcov j)]
    (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCp : ∀ j, (C j : ℝ) ≤ Real.exp pNum) (_hVp : ∀ j, (V j : ℝ) ≤ Real.exp pNum)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv 1 j)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {X : Type uSpace} [Fintype X] [DecidableEq X]
    (_hXPsp : (Fintype.card X : ℝ) ≤ Psp)
    (q : X → ℕ) (_hq : ∀ t, 0 < q t) (_hqPsp : ∀ t, (q t : ℝ) ≤ Real.exp Psp),
    let refined := residueRefinedPeriod modulus q
    ∃ hRefined : 0 < refined,
    let : NeZero refined := ⟨hRefined.ne'⟩
    (∀ t, q t * modulus ∣ refined) ∧
    (refined : ℝ) ≤ Real.exp ((m + 1 : ℕ) * Psp + Fintype.card X * Psp) ∧
    ∃ hsize : ∀ a, (Fintype.card (Fin dim) + 1) * refined ≤
      principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
        (allocatedPrincipalSides B U b S) a,
    ∃ (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
    (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      ∀ j, Matrix (jets j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)),
    (∀ u r, principalResidueLabel refined (reference u r) = r) ∧
    (∀ u r v, (allocatedLongResidueWeights B U b S refined hRefined r hsize).weight v ≠ 0 →
      ∀ j, integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u jetRows j v) modulus = residue u r j) ∧
    let W := allocatedPhysicalRootBudget B U b S (fun _ => 0)
    let hW := allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)
    let indices := PrincipalTupleIndex B (layerSamplerDegree I n)
    let ξ := normalizedTupleNarrowWidth X indices selection Mk Psp (E + 2)
    let hξ := normalizedTupleNarrowWidth_pos X indices selection Mk Psp (E + 2)
    let mesh := normalizedTupleRadius X selection Mk Psp (E + 2) W / 4
    ∀ {τ : ℝ} (hτ : 0 < τ) (_hτP : 1 / τ ≤ Real.exp pNum)
    (N : X → ℕ) (hN : ∀ t, 0 < N t)
    (_hsize : ∀ t, Real.exp ((Q + K) ^ K) ≤ (N t : ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
    {rank : ℝ}
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) rank (U j) (poly j))
    (_hRank : Real.exp ((Q + K) ^ K) ≤ rank)
    (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hcells : cells.Nonempty)
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) (_htest : ∀ site v, ‖test site v‖ ≤ 1)
    (Z : ℝ) (_hZ : 1 / 2 ≤ Z),
    ∃ hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := indices) W τ ξ N) z,
    ‖allocatedOriginalTupleSource B U b hR hσ S x X q hb o N hN hW hτ hξ base cells hmass
        (physicalCubeSiteTest test) Z poly hmem -
      allocatedRefinedIdealReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x jetRows X hMk selection hx modulus q reference residue hb o bW d
        N hW mesh base cells (physicalCubeEuclideanSample U d poly hmem) (physicalCubeSiteTest test) Z δ‖ ≤
      Real.exp (-E)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uG uI uB uGeom uCover uSpace

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {dim : ℕ}

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

theorem allocatedReferencePrescribedIdealAt_original
    {D Psp E e t : ℝ} {δ : ℝ≥0} {Kideal : ℕ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) jets D)
    (hPsp : 0 ≤ Psp) (hE : 0 ≤ E) (he : 0 ≤ e) (ht1 : t ≤ 1) (hKideal : 2 ≤ Kideal)
    (hselected : AllocatedReferencePrescribedIdealAt.{uG, uI, uB, uGeom, uCover, uSpace}
      (G := G) (dim := dim) B D Psp (E + 4) e t δ Kideal) :
    ∃ A T Kproj : ℕ, 2 ≤ A ∧ 2 ≤ T ∧ 2 ≤ Kproj ∧
      AllocatedOriginalPrescribedAt.{uG, uI, uB, uGeom, uCover, uSpace}
        (G := G) (dim := dim) B D Psp E e t δ A T Kproj Kideal := by
  obtain ⟨A, T, Kproj, hAconst, hT, hKproj, hfamily⟩ :=
    exists_allocated_ideal_density_source_family.{uSpace, uG, uI, uB, uGeom} m dim
  refine ⟨A, T, Kproj, hAconst, hT, hKproj, ?_⟩
  unfold AllocatedOriginalPrescribedAt
  intro hmPsp hdimPsp hGPsp hvarsGrowth J _ U b R σ hR hσ hσt
    pNum hPspNum hcount herrorNum hRefineNum hRP hRi hσi
  unfold AllocatedOriginalPrescribedAtScale
  intro w error gainLog S lengthLog Pbase l F Q K
  have hpNum : 0 ≤ pNum := hPsp.trans hPspNum
  have hw : 0 ≤ w := mul_nonneg (Nat.cast_nonneg _) hPsp
  have herror : 0 ≤ error := allocatedReferenceIdealError_nonneg m hdim.nonneg hPsp (by linarith)
  have hgain : 0 ≤ gainLog := allocatedProfileGainLog_nonneg m hdim.nonneg hPsp hw
  have hlength : 0 ≤ lengthLog := by
    have h := allocatedIdealScaleInput_bounds m hdim.nonneg hpNum he hw herror
    exact h.2.1.trans h.2.2.2.2.2
  have hinput := (allocatedActualProfileInput_bounds m hdim.nonneg hpNum he hgain hlength).1
  have hF : 0 ≤ F := by
    have hlog := allocatedProfileErrorLog_nonneg hinput
    dsimp only [F, allocatedProfileFourierOutput, allocatedProfileFourierInput]
    positivity
  obtain ⟨_hPbase1, _hDPbase, hpBase, _hLBase, _hWBase⟩ :=
    allocatedIdealSourceBudget_bounds m hdim.nonneg hpNum he hw herror
  have hPspBase : Psp ≤ Pbase := hPspNum.trans hpBase
  obtain ⟨hS, hselected⟩ := hselected hmPsp hdimPsp hGPsp U b hR hσ hσt
    hPspNum hcount herrorNum hRefineNum hRP hRi hσi
  obtain ⟨_hSfamily, hfamily⟩ := hfamily B U b hR hσ hdim hpNum he hw herror hRi hσi
  refine ⟨hS, ?_⟩
  intro x Mk hMk selection hx hqDim hMkPsp
  obtain ⟨d, hd, hdb, hfamily⟩ := hfamily x hx.2
  let : NeZero d := ⟨hd.ne'⟩
  refine ⟨d, hd, hdb, ?_⟩
  intro modulus hmodulus
  let : NeZero modulus := ⟨hmodulus.ne'⟩
  intro _ hmodulusSize hspatialPeriod hcoefficientPeriod
  obtain ⟨s, hA, hinverse, hselected⟩ :=
    hselected x hMk selection hx hqDim hMkPsp modulus hmodulus
      hmodulusSize hspatialPeriod hcoefficientPeriod
  refine ⟨s, hA, hinverse, ?_⟩
  intro block _ _ _ _ _ _ hb o Kcov _ bW C V hC hV hCp hVp Cinv hCinv hchart hsmall μ _ _ ν _ _
    X _ _ hXPsp q hq hqPsp refined
  have hσ1 (j) : σ j ≤ 1 := (hσt j).trans ht1
  have hjet := allocatedPhysicalChartRadius_bound (G := G) B (Fin dim) Cinv hCinv
    (le_refl 1) (fun j => (hR j).le) hsmall (le_refl 1) (le_refl 1)
  have hsmallDensity := allocatedJetRadius_implies_chartRadius (B := B) (hR := hR)
    (le_refl 1) Cinv hCinv hjet
  obtain ⟨hnum, g, hgc, hgb, _hgi, _hgm, hglaw, _hproject, horiginal, hdata⟩ :=
    hfamily hb o C V hC hV hCp hVp hσ1 Cinv hCinv hchart hsmallDensity μ ν
  obtain ⟨hRefined, hdiv, hRefinedBound, hsize, reference, residue, href, hresidue, _hpointwise,
    hsource, hideal⟩ := hselected block hb o bW d C V hC hV ν hXPsp q hq hqPsp
  let : NeZero (residueRefinedPeriod modulus q) := ⟨hRefined.ne'⟩
  refine ⟨hRefined, hdiv, hRefinedBound, hsize, reference, residue, href, hresidue, ?_⟩
  intro W hW indices ξ hξ mesh τ hτ hτP N hN hsizeN poly hpoly hmem rank hrank hRank
    base cells hcells test htest Z hZ
  let C₀ : ℝ := 1 + (S.value : ℝ) + W
  let cap : ℝ := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
    Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
  let Centry := allocatedPhysicalEntryBudget B U b S (fun _ => 0)
  let ρ := normalizedTupleResolution X indices selection Mk Psp (E + 2) C₀ W cap Centry
  have hcap : 0 ≤ cap := pow_nonneg (NNReal.coe_nonneg _) _
  obtain ⟨_hW, hl, hBaseL, hC₀, hLC, hWC, hC₀l, hcapl, hentryl, hWl, hprofilel⟩ :=
    AllocatedSourceNumerics.late_bounds B U b S C V hnum hR hσ
  have hWscale : W ≤ (Fintype.card (LayerSamplerVariables G I n B) : ℝ) * S.value := by
    simp only [W, allocatedPhysicalRootBudget, Int.cast_zero, abs_zero, Finset.sum_const_zero, zero_add, le_refl]
  have hPspL : Psp ≤ l := hPspBase.trans hBaseL
  have hql (a : X) : (q a : ℝ) ≤ Real.exp l := (hqPsp a).trans (Real.exp_le_exp.mpr hPspL)
  have hτl : τ⁻¹ ≤ Real.exp l := by
    simpa only [one_div] using hτP.trans (Real.exp_le_exp.mpr (hpBase.trans hBaseL))
  have hE2 : 0 ≤ E + 2 := by linarith
  have hS1 : (1 : ℝ) ≤ S.value := by exact_mod_cast Nat.succ_le_iff.mpr S.positive
  have hentry : 0 ≤ Centry := zero_le_one.trans (allocatedPhysicalEntryBudget_one_le B U b S (fun _ => 0))
  obtain ⟨_hξ, hξ1, _hξlog, hchoices⟩ := normalizedTupleSpatialChoices
    (N := indices) (X := X) (m := m) selection hMk hPsp hE2 hmPsp hdimPsp hGPsp hXPsp hMkPsp
  obtain ⟨_hδ, _hδ1, hmesh, hρ, _hmeshSize, hρ8, hshift, _hmove, _hboundary, _hspatial⟩ :=
    hchoices (zero_le_one.trans hC₀) hW hS1 hcap hentry hvarsGrowth hWscale
  have hqdimBase : (Fintype.card (Unit ⊕ Fin dim) : ℝ) ≤ Pbase := by
    simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Nat.add_comm 1] using
      hdimPsp.trans hPspBase
  have hXBase : (Fintype.card X : ℝ) ≤ Pbase := hXPsp.trans hPspBase
  obtain ⟨_hQ1, hBaseQ, hE1Q, hlQ, _hFQ, hJetQ, hProdQ, _hWidthQ, _hSideQ⟩ :=
    allocatedSourceSamplingBudget_bounds m dim A hnum.nonneg hE hl hF
  obtain ⟨hwidthQ, hsideQ, hdimQ⟩ := allocatedSourceSamplingBudget_spatial m A X indices selection
    hPsp hE hl hF hPspBase hqdimBase hnum.variable_count hXBase
  have hXQ := hXBase.trans hBaseQ
  have hOptionBase : (Fintype.card (Option (Fin dim)) : ℝ) ≤ Pbase := by
    simpa only [Fintype.card_option, Fintype.card_fin, Fintype.card_sum, Fintype.card_unit, Nat.add_comm 1]
      using hqdimBase
  have hsmallDim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ Q := by
    calc
      _ = (Fintype.card (Option (Fin dim)) : ℝ) * Fintype.card X := by
        simp only [Fintype.card_prod, Nat.cast_mul]
      _ ≤ Pbase * Pbase := mul_le_mul hOptionBase hXBase (Nat.cast_nonneg _) hnum.nonneg
      _ ≤ (Pbase + 1) * Pbase := mul_le_mul_of_nonneg_right (by linarith) hnum.nonneg
      _ ≤ Q := hProdQ
  obtain ⟨hQcut, hMassCut, hProjCut, hIdealCut⟩ := allocatedSourceSamplingBudget_cutoffs m dim A
    hnum.nonneg hE hl hF T Kproj Kideal (Nat.le_trans (by decide) hT)
      (Nat.le_trans (by decide) hKproj) (Nat.le_trans (by decide) hKideal)
  have hside (a : X) : Real.exp (normalizedTupleSideLog X indices selection Psp (E + 2) l) ≤ (N a : ℝ) :=
    (Real.exp_le_exp.mpr (hsideQ.trans hQcut)).trans (hsizeN a)
  have hphysical (a : X) : 8 * (1 + W) * (q a : ℝ) * ρ ≤ (ξ * τ) * (N a : ℝ) :=
    normalizedTupleSpatialSize X indices selection hPsp hE2 hl hMk hmPsp hdimPsp hGPsp hXPsp hMkPsp
      (zero_le_one.trans hC₀) hW hcap hentry hC₀l hWl hcapl hentryl hprofilel (Nat.cast_nonneg _) (hql a)
      hτ hτl (hside a)
  have hshift' : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ := by
    simpa only [mul_assoc] using hshift
  obtain ⟨hmass, _hphysicalCap⟩ := exists_selectedResidue_physical_cap
    (fun _ : LayerSamplerVariables G I n B => 0) q hq cells hcells
    (narrowTrimmedSpatialWidths (G := G) (J := indices) W τ ξ N)
    (narrowTrimmedSpatialWidths_pos hW hτ hξ N hN)
    (fun z => hρ8.trans (narrowTrimmedSpatial_residue_width_lower hW hτ hξ1 hρ.le N q hN hq hphysical z))
  refine ⟨hmass, ?_⟩
  have hmassReference := fun y y₀ a => (hdata y).2 hJetQ hXQ hsmallDim poly hpoly hmem N q hq
    hW hτ hξ1 hρ (hτP.trans (Real.exp_le_exp.mpr (hpBase.trans hBaseQ)))
    (fun a => (hqPsp a).trans (Real.exp_le_exp.mpr (hPspBase.trans hBaseQ)))
    (fun a => (Real.exp_le_exp.mpr hMassCut).trans (hsizeN a)) hrank
    ((Real.exp_le_exp.mpr hMassCut).trans hRank) hphysical hρ8 hshift' y₀ base a
  have htest' := physicalCubeSiteTest_norm_le test htest
  have htailIdeal := hideal N hN hW hτ hξ hξ1 hρ hphysical hρ8 hshift' le_rfl base cells hmass
    poly hpoly hmem hCp hVp hτP mesh hmesh hvarsGrowth hWscale
    (fun a => (Real.exp_le_exp.mpr hIdealCut).trans (hsizeN a)) hrank
    ((Real.exp_le_exp.mpr hIdealCut).trans hRank) (physicalCubeSiteTest test) htest' Z hZ
  have hcomparison := allocatedFixedData_chosen_original_ideal B U b hR hσ S x X hMk selection hx
    modulus s hA q reference residue hb o bW d (Pbase := Pbase) (Kproj := Kproj) (P := Psp) (E := E) δ hsource
  obtain ⟨_hξ1', _hξlog', hcomparison⟩ :=
    hcomparison hPsp hE hmPsp hdimPsp hGPsp hXPsp hMkPsp hmodulusSize hq hσ1
  obtain ⟨_hδ', _hmesh', _hρ', _hδlog, _hmeshlog, _hρlog, hcomparison⟩ :=
    hcomparison Cinv hCinv hchart hsmall μ ν g hgc (fun y z => (hgb y z).1) hglaw horiginal
      hW hτ le_rfl hC₀ hLC hWC hcap hZ hvarsGrowth hWscale hl hC₀l hWl hcapl hentryl hprofilel hql hτl
  exact hcomparison hBaseQ hlQ hE1Q hwidthQ hXQ hdimQ N hN hside
    (fun a => (Real.exp_le_exp.mpr hProjCut).trans (hsizeN a)) poly hpoly hmem hrank
    ((Real.exp_le_exp.mpr hProjCut).trans hRank) base cells hcells hmass test htest
    (fun y v => (hgb y (physicalCubeEuclideanSample U d poly hmem v)).2)
    hmassReference htailIdeal.1 htailIdeal.2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uG uI uB uGeom uCover uSpace

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {dim : ℕ}

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) (Fin.val j + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : jets j → Finset (Fin dim)))

def AllocatedCommonOriginalAt (p Psp E e t : ℝ) (δ : ℝ≥0) (A T Kproj Kideal : ℕ) : Prop :=
  ∀ {c : ℝ} (_hc : 0 ≤ c) {J : Fin m → Type uGeom} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (_hσt : ∀ j, σ j ≤ t) (_hR1 : ∀ j, R j ≤ 1)
    (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp c) (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp c),
    AllocatedOriginalPrescribedAtScale.{uG,uI,uB,uGeom,uCover,uSpace} (G := G) (dim := dim) B U b hR hσ
      (allocatedComparisonDimension m p) Psp E e (allocatedCommonScaleNumeric m p c Psp (E + 4)) δ A T Kproj Kideal

theorem allocatedOriginalPrescribedAt_commonScale
    {p Psp E e t : ℝ} {δ : ℝ≥0} {A T Kproj Kideal : ℕ}
    (hp : 0 ≤ p) (hPsp : 0 ≤ Psp) (hE : 0 ≤ E)
    (hdim : dim ≤ m + 1) (hmPsp : ((m + 2 : ℕ) : ℝ) ≤ Psp) (hpPsp : p ≤ Psp)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (horiginal : AllocatedOriginalPrescribedAt.{uG,uI,uB,uGeom,uCover,uSpace}
      (G := G) (dim := dim) B (allocatedComparisonDimension m p) Psp E e t δ A T Kproj Kideal) :
    AllocatedCommonOriginalAt.{uG,uI,uB,uGeom,uCover,uSpace} (G := G) (dim := dim)
      B p Psp E e t δ A T Kproj Kideal := by
  intro c hc J _ U b R σ hR hσ hσt hR1 hRi hσi
  have hE4 : 0 ≤ E + 4 := by linarith
  obtain ⟨hq, _, hcq, hPq, hcountq, herrorq, hrefineq⟩ :=
    allocatedCommonScaleNumeric_bounds m hp hc hPsp hE4
  have hdim' : ((dim + 1 : ℕ) : ℝ) ≤ (m + 2 : ℕ) := by
    exact_mod_cast (show dim + 1 ≤ m + 2 by omega)
  have hm' : ((m + 1 : ℕ) : ℝ) ≤ (m + 2 : ℕ) := by exact_mod_cast (show m + 1 ≤ m + 2 by omega)
  have hG : (Fintype.card G : ℝ) ≤ Psp :=
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans (hvars.trans hpPsp)
  have hvarsGrowth : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp Psp :=
    (hvars.trans hpPsp).trans (by linarith [Real.add_one_le_exp Psp])
  have hcount := allocatedSiteScale_coefficient_count B hp hvars
  exact horiginal (hm'.trans hmPsp) (hdim'.trans hmPsp) hG hvarsGrowth U b hR hσ hσt
    hPq (fun j => (hcount j).trans (Real.exp_le_exp.mpr hcountq)) herrorq
    (by linarith) (fun j => (hR1 j).trans (Real.one_le_exp_iff.mpr hq))
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hcq))
    (fun j => (hσi j).trans (Real.exp_le_exp.mpr hcq))

theorem exists_allocated_common_original
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {p Psp E : ℝ} (hp : 0 ≤ p) (hPsp : 0 ≤ Psp) (hE : 0 ≤ E)
    (hdim : dim ≤ m + 1) (hmPsp : ((m + 2 : ℕ) : ℝ) ≤ Psp) (hpPsp : p ≤ Psp)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p) :
    ∃ K : ℕ, 2 ≤ K ∧
      let D := allocatedComparisonDimension m p
      let target := profileReferenceErrorLog Psp (E + 4)
      let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
      let gainLog := allocatedProfileGainLog m D Psp w
      let ε := physicalIdealErrorShare target gainLog
      let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
        (α := Fin dim) (layerSamplerDegree I n) A T target gainLog
      ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
        (δ : ℝ) = booleanRegularizationRadius (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim) (layerSamplerDegree I n)
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T (ε / 2) ∧ (δ : ℝ)⁻¹ ≤ Real.exp e ∧
        let t := booleanMassPerturbationScale (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
          ((G × Option (Fin dim)) ⊕ (Σ a, SamplerCoefficientSlot G B (layerSamplerDegree I n) a))
          (layerSamplerDegree I n)
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T m 1 (ε / 2)
        0 < t ∧ t ≤ 1 ∧
          ∃ A₀ T₀ Kproj : ℕ, 2 ≤ A₀ ∧ 2 ≤ T₀ ∧ 2 ≤ Kproj ∧
            AllocatedCommonOriginalAt.{uG,uI,uB,uGeom,uCover,uSpace} (G := G) (dim := dim)
              B p Psp E e t δ A₀ T₀ Kproj K := by
  have hdimensions := allocatedComparisonDimensions_of_primitive B jetRows
    (by simpa only [Fintype.card_fin] using hdim) (fun _ => Subtype.val_injective) hp hvars hI hn
  have hE4 : 0 ≤ E + 4 := by linarith
  have htarget : 0 ≤ profileReferenceErrorLog Psp (E + 4) := by
    have hs := coefficientErrorSpatialLog_nonneg hPsp
    unfold profileReferenceErrorLog
    linarith
  have hw : 0 ≤ (m * 2 ^ (m + 1) : ℕ) * Psp := mul_nonneg (Nat.cast_nonneg _) hPsp
  have hgain := allocatedProfileGainLog_nonneg m hdimensions.nonneg hPsp hw
  have he := physicalIdealSmoothingLog_nonneg (B := B)
    (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
    (layerSamplerDegree I n) A T htarget hgain
  obtain ⟨K, hK, δ, hδ, hδ1, hδeq, hδe, ht, ht1, hcompare⟩ :=
    exists_allocated_reference_prescribed_ideal.{uG,uI,uB,uGeom,uCover,uSpace} B
      ψ hψ hrange hzero hone A T hLip hTransition hdimensions hPsp hE4
  obtain ⟨A₀, T₀, Kproj, hA₀, hT₀, hKproj, horiginal⟩ :=
    allocatedReferencePrescribedIdealAt_original B hdimensions hPsp hE he ht1 hK hcompare
  exact ⟨K, hK, δ, hδ, hδ1, hδeq, hδe, ht, ht1, A₀, T₀, Kproj, hA₀, hT₀, hKproj,
    allocatedOriginalPrescribedAt_commonScale B hp hPsp hE hdim hmPsp hpPsp hvars horiginal⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uG uI uB uGeom uCover uSpace

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {dim : ℕ}

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

section FixedScale

variable {J : Fin m → Type uGeom} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

def AllocatedOriginalResidueWeightedAtScale (D Psp E e pNum : ℝ) (δ : ℝ≥0)
    (A T Kproj Kideal : ℕ) : Prop :=
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
  let error := allocatedReferenceIdealError m D Psp (E + 4)
  let gainLog := allocatedProfileGainLog m D Psp w
  let S := allocatedIdealScale (G := G) B U b hR hσ D pNum e w error
  let lengthLog := allocatedIdealScaleLog m D pNum e w error
  let Pbase := allocatedIdealSourceBudget m D pNum e w error
  let l := allocatedSpatialLateLog (G := G) B Pbase Pbase
  let F := allocatedProfileFourierOutput (allocatedActualProfileInput m D pNum e gainLog lengthLog)
  let Q := allocatedSourceSamplingBudget m dim A Pbase E l F
  let K := max T (max Kproj Kideal)
  (S.value : ℝ) ≤ Real.exp lengthLog ∧
  ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    {Mk : ℕ} (hMk : 0 < Mk) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (_hqDim : dim ≤ m + 1) (_hMkPsp : (Mk : ℝ) ≤ Real.exp Psp),
  ∃ (d : ℕ) (hd : 0 < d),
    let : NeZero d := ⟨hd.ne'⟩
    (d : ℝ) ≤ Real.exp ((Pbase + A) ^ A) ∧
  ∀ (modulus : ℕ) (hmodulus : 0 < modulus),
    let : NeZero modulus := ⟨hmodulus.ne'⟩
    ∀ (_hmodulusSize : modulus ≤ Mk ^ (m + 1))
      (_hspatialPeriod : ∀ root : G → ℤ, integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
        pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
          (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection))
      (_hcoefficientPeriod : ∀ j, integerScalarLattice (jets j) (modulus : ℤ) ≤
        (scalarKernelIntegerJet x (j.val + 1) (jetRows j)).mulVecLin.range),
    ∃ (s : ∀ j, jets j ↪ BoundedIntegerExponent G (j.val + 1))
      (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (jetRows j)).submatrix id (s j)).det ≠ 0),
    (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (jetRows j) (s j) (hA j) (1 / (Mk : ℝ))) ∧
    ∀ (_block : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, jets a.val.1 ↪ B a.val)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin dim)) U)] [BorelSpace (SiteTorus (Finset (Fin dim)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Kcov : Fin m → Type uCover} [∀ j, Fintype (Kcov j)]
    (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCp : ∀ j, (C j : ℝ) ≤ Real.exp pNum) (_hVp : ∀ j, (V j : ℝ) ≤ Real.exp pNum)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv 1 j)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {X : Type uSpace} [Fintype X] [DecidableEq X]
    (_hXPsp : (Fintype.card X : ℝ) ≤ Psp)
    (q : X → ℕ) (_hq : ∀ t, 0 < q t) (_hqPsp : ∀ t, (q t : ℝ) ≤ Real.exp Psp),
    let refined := residueRefinedPeriod modulus q
    ∃ hRefined : 0 < refined,
    let : NeZero refined := ⟨hRefined.ne'⟩
    (∀ t, q t * modulus ∣ refined) ∧
    (refined : ℝ) ≤ Real.exp ((m + 1 : ℕ) * Psp + Fintype.card X * Psp) ∧
    ∃ hsize : ∀ a, (Fintype.card (Fin dim) + 1) * refined ≤
      principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
        (allocatedPrincipalSides B U b S) a,
    ∃ (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
    (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      ∀ j, Matrix (jets j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)),
    (∀ u r, principalResidueLabel refined (reference u r) = r) ∧
    (∀ u r v, (allocatedLongResidueWeights B U b S refined hRefined r hsize).weight v ≠ 0 →
      ∀ j, integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u jetRows j v) modulus = residue u r j) ∧
    let W := allocatedPhysicalRootBudget B U b S (fun _ => 0)
    let hW := allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)
    let indices := PrincipalTupleIndex B (layerSamplerDegree I n)
    let ξ := normalizedTupleNarrowWidth X indices selection Mk Psp (E + 2)
    let hξ := normalizedTupleNarrowWidth_pos X indices selection Mk Psp (E + 2)
    let mesh := normalizedTupleRadius X selection Mk Psp (E + 2) W / 4
    ∀ {τ : ℝ} (hτ : 0 < τ) (_hτP : 1 / τ ≤ Real.exp pNum)
    (N : X → ℕ) (hN : ∀ t, 0 < N t)
    (_hsize : ∀ t, Real.exp ((Q + K) ^ K) ≤ (N t : ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
    {rank : ℝ}
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) rank (U j) (poly j))
    (_hRank : Real.exp ((Q + K) ^ K) ≤ rank)
    (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hcells : cells.Nonempty)
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) (_htest : ∀ site v, ‖test site v‖ ≤ 1)
    (Z : ℝ) (_hZ : 1 / 2 ≤ Z),
    ∃ hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := indices) W τ ξ N) z,
    ‖allocatedOriginalTupleSource B U b hR hσ S x X q hb o N hN hW hτ hξ base cells hmass
        (physicalCubeSiteTest test) Z poly hmem -
      allocatedWholeIdealReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x jetRows X hMk selection hx modulus q reference hb o bW d
        N hW mesh base cells (physicalCubeEuclideanSample U d poly hmem) (physicalCubeSiteTest test) Z δ‖ ≤
      Real.exp (-E)

theorem allocatedOriginalPrescribedAtScale_residue_weighted
    {D Psp E e pNum : ℝ} {δ : ℝ≥0} {A T Kproj Kideal : ℕ}
    (horiginal : AllocatedOriginalPrescribedAtScale.{uG,uI,uB,uGeom,uCover,uSpace}
      (G := G) (dim := dim) B U b hR hσ D Psp E e pNum δ A T Kproj Kideal) :
    AllocatedOriginalResidueWeightedAtScale.{uG,uI,uB,uGeom,uCover,uSpace}
      (G := G) (dim := dim) B U b hR hσ D Psp E e pNum δ A T Kproj Kideal := by
  unfold AllocatedOriginalResidueWeightedAtScale
  intro w error gainLog S lengthLog Pbase l F Q K
  obtain ⟨hS, horiginal⟩ := horiginal
  refine ⟨hS, ?_⟩
  intro x Mk hMk selection hx hqDim hMkPsp
  obtain ⟨d, hd, hdb, horiginal⟩ := horiginal x hMk selection hx hqDim hMkPsp
  let : NeZero d := ⟨hd.ne'⟩
  refine ⟨d, hd, hdb, ?_⟩
  intro modulus hmodulus
  let : NeZero modulus := ⟨hmodulus.ne'⟩
  intro _ hmodulusSize hspatialPeriod hcoefficientPeriod
  obtain ⟨s, hA, hinverse, horiginal⟩ := horiginal modulus hmodulus
    hmodulusSize hspatialPeriod hcoefficientPeriod
  refine ⟨s, hA, hinverse, ?_⟩
  intro block _ _ _ _ _ _ hb o Kcov _ bW C V hC hV hCp hVp Cinv hCinv hchart hsmall μ _ _ ν _ _
    X _ _ hXPsp q hq hqPsp refined
  obtain ⟨hRefined, hdiv, hRefinedBound, hsize, reference, residue, href, hresidue, horiginal⟩ :=
    horiginal block hb o bW C V hC hV hCp hVp Cinv hCinv hchart hsmall μ ν hXPsp q hq hqPsp
  let : NeZero (residueRefinedPeriod modulus q) := ⟨hRefined.ne'⟩
  refine ⟨hRefined, hdiv, hRefinedBound, hsize, reference, residue, href, hresidue, ?_⟩
  intro W hW indices ξ hξ mesh τ hτ hτP N hN hsizeN poly hpoly hmem rank hrank hRank
    base cells hcells test htest Z hZ
  obtain ⟨hmass, he⟩ := horiginal hτ hτP N hN hsizeN poly hpoly hmem hrank hRank
    base cells hcells test htest Z hZ
  refine ⟨hmass, ?_⟩
  have hid := allocatedRefinedIdealReference_residue_weighted (τ := τ) (ξ := ξ)
    B U b hR hσ S x jetRows X hMk selection hx modulus q reference residue hb o bW d
    N hW mesh base cells (physicalCubeEuclideanSample U d poly hmem) (physicalCubeSiteTest test) Z
    δ hcoefficientPeriod hRefined hsize href hresidue
  rw [hid] at he
  exact he

end FixedScale

def AllocatedCommonResidueWeightedOriginalAt (p Psp E e t : ℝ) (δ : ℝ≥0) (A T Kproj Kideal : ℕ) : Prop :=
  ∀ {c : ℝ} (_hc : 0 ≤ c) {J : Fin m → Type uGeom} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (_hσt : ∀ j, σ j ≤ t) (_hR1 : ∀ j, R j ≤ 1)
    (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp c) (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp c),
    AllocatedOriginalResidueWeightedAtScale.{uG,uI,uB,uGeom,uCover,uSpace} (G := G) (dim := dim) B U b hR hσ
      (allocatedComparisonDimension m p) Psp E e (allocatedCommonScaleNumeric m p c Psp (E + 4)) δ A T Kproj Kideal

theorem allocatedCommonOriginalAt_residue_weighted
    {p Psp E e t : ℝ} {δ : ℝ≥0} {A T Kproj Kideal : ℕ}
    (horiginal : AllocatedCommonOriginalAt.{uG,uI,uB,uGeom,uCover,uSpace}
      (G := G) (dim := dim) B p Psp E e t δ A T Kproj Kideal) :
    AllocatedCommonResidueWeightedOriginalAt.{uG,uI,uB,uGeom,uCover,uSpace}
      (G := G) (dim := dim) B p Psp E e t δ A T Kproj Kideal := by
  intro c hc J _ U b R σ hR hσ hσt hR1 hRi hσi
  exact allocatedOriginalPrescribedAtScale_residue_weighted B U b hR hσ
    (horiginal hc U b hR hσ hσt hR1 hRi hσi)

theorem exists_allocated_common_residue_weighted_original
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {p Psp E : ℝ} (hp : 0 ≤ p) (hPsp : 0 ≤ Psp) (hE : 0 ≤ E)
    (hdim : dim ≤ m + 1) (hmPsp : ((m + 2 : ℕ) : ℝ) ≤ Psp) (hpPsp : p ≤ Psp)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p) :
    ∃ K : ℕ, 2 ≤ K ∧
      let D := allocatedComparisonDimension m p
      let target := profileReferenceErrorLog Psp (E + 4)
      let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
      let gainLog := allocatedProfileGainLog m D Psp w
      let ε := physicalIdealErrorShare target gainLog
      let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
        (α := Fin dim) (layerSamplerDegree I n) A T target gainLog
      ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
        (δ : ℝ) = booleanRegularizationRadius (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim) (layerSamplerDegree I n)
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T (ε / 2) ∧ (δ : ℝ)⁻¹ ≤ Real.exp e ∧
        let t := booleanMassPerturbationScale (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
          ((G × Option (Fin dim)) ⊕ (Σ a, SamplerCoefficientSlot G B (layerSamplerDegree I n) a))
          (layerSamplerDegree I n)
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T m 1 (ε / 2)
        0 < t ∧ t ≤ 1 ∧
          ∃ A₀ T₀ Kproj : ℕ, 2 ≤ A₀ ∧ 2 ≤ T₀ ∧ 2 ≤ Kproj ∧
            AllocatedCommonResidueWeightedOriginalAt.{uG,uI,uB,uGeom,uCover,uSpace} (G := G) (dim := dim)
              B p Psp E e t δ A₀ T₀ Kproj K := by
  obtain ⟨K, hK, δ, hδ, hδ1, hδeq, hδe, ht, ht1, A₀, T₀, Kproj, hA₀, hT₀, hKproj, horiginal⟩ :=
    exists_allocated_common_original.{uG,uI,uB,uGeom,uCover,uSpace}
      (G := G) (dim := dim) B ψ hψ hrange hzero hone A T hLip hTransition
      hp hPsp hE hdim hmPsp hpPsp hvars hI hn
  exact ⟨K, hK, δ, hδ, hδ1, hδeq, hδe, ht, ht1, A₀, T₀, Kproj, hA₀, hT₀, hKproj,
    allocatedCommonOriginalAt_residue_weighted B horiginal⟩

end Erdos3.VectorPolynomial

end

end OAI

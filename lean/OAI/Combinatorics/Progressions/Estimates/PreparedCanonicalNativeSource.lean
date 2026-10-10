import OAI.Combinatorics.Progressions.Dynamics.AllocatedCoarseNativeBudget
import OAI.Combinatorics.Progressions.Probability.AllocatedEarlyCoverCoefficientMass
import OAI.Combinatorics.Progressions.Sampling.ForecastPreparedScaleBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def selectedResidueCellLaw {K X : Type*} [Fintype K] [Fintype X]
    (q : X → ℕ) (cells : Finset (ColumnResiduePattern K X q)) (V : K × X → ℝ)
    (hV : ∀ z, 0 < V z) (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells V z) :
    FiniteProbabilityWeights cells where
  weight := selectedResidueCellWeight q cells V
  nonneg := selectedResidueCellWeight_nonneg q cells V
  total := selectedResidueCellWeight_sum q cells V hV hmass

namespace VectorPolynomial

open Module Submodule

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (period : ℕ) [NeZero period]

local notation "positive" => AllocatedPositiveResidue (dim := dim) B U b S period
local notation "tuples" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
local notation "residueLaw" => FiniteProbabilityWeights.fiberLaw (tuples) (principalResidueLabel period)

theorem exists_allocated_genuine_source_cell {K X : Type*} [Fintype K] [Fintype X]
    (q : X → ℕ) (cells : Finset (ColumnResiduePattern K X q)) (V : K × X → ℝ)
    (hV : ∀ z, 0 < V z) (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells V z)
    (value : positive → cells → ℂ) (Z : ℂ) {η : ℝ}
    (hpositive : η ≤ ((residueLaw).complexMean (fun r =>
      if hr : 0 < (tuples).mass (Finset.univ.filter (fun y => principalResidueLabel period y = r)) then
        ∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) * value ⟨r, hr⟩ a
      else 0) / Z).re) :
    ∃ (r : positive) (a : cells),
      0 < selectedResidueCellWeight q cells V a ∧ η ≤ (value r a / Z).re := by
  let law := allocatedPositiveResidueLaw (dim := dim) B U b S period
  let cellLaw := selectedResidueCellLaw q cells V hV hmass
  have hmean : η ≤ (law.complexMean (fun r => cellLaw.complexMean (value r)) / Z).re := by
    rw [allocatedPositiveResidueLaw_complexMean]
    exact hpositive
  rw [← FiniteProbabilityWeights.complexMean_div] at hmean
  obtain ⟨r, _, hr⟩ := law.exists_positive_weight_ge_complexMean_re
    (fun r => cellLaw.complexMean (value r) / Z)
  have hcell := hmean.trans hr
  rw [← FiniteProbabilityWeights.complexMean_div] at hcell
  obtain ⟨a, ha, hvalue⟩ := cellLaw.exists_positive_weight_ge_complexMean_re
    (fun a => value r a / Z)
  exact ⟨r, a, ha, hcell.trans hvalue⟩

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped Classical NNReal

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq

theorem exists_prepared_canonical_sources :
    ∃ A T : ℝ≥0, 1 ≤ A ∧ 1 ≤ T ∧ ∀ m dim : ℕ,
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin dim) (j.val + 1)
      ∃ Ksite Knorm Kgen Kideal A₀ T₀ Kproj : ℕ,
        2 ≤ Ksite ∧ 2 ≤ Knorm ∧ 2 ≤ Kgen ∧
        2 ≤ Kideal ∧ 2 ≤ A₀ ∧ 2 ≤ T₀ ∧ 2 ≤ Kproj ∧
        PhysicalAmbientRowsKernelSampling.{0,0,0} m dim Kgen
          (fun j => (rowSets j : Type)) (fun _ => Subtype.val) ∧
        ∀ {X J : Type} (L : RankPreparationFamily X J m) {M : ℕ},
          (∀ j, Fintype.card (L j).Coord ≤ M) →
          let p : ℝ := preparedSamplerDimension m dim M
          ∀ {P E : ℝ} (hP : 0 ≤ P), 0 ≤ E → dim ≤ m + 1 →
            ((m + 2 : ℕ) : ℝ) ≤ P → allocatedComparisonDimension m p ≤ P →
            AllocatedInitializedCanonicalSourceAt.{0,0,0,0,0,0}
              (G := Fin (dim * (dim + 2))) (dim := dim)
              (PreparedSamplerBlock L dim) p P E (Nat.cast_nonneg _) hP
              A T Ksite Knorm Kgen Kideal A₀ T₀ Kproj := by
  obtain ⟨A, T, hA, hT, hsource⟩ := exists_uniform_initialized_canonical_sources.{0,0,0,0,0,0}
  refine ⟨A, T, hA, hT, ?_⟩
  intro m dim rowSets
  obtain ⟨Ksite, Knorm, Kgen, Kideal, A₀, T₀, Kproj,
    hKsite, hKnorm, hKgen, hKideal, hA₀, hT₀, hKproj, hgen, hs⟩ := hsource m dim
  refine ⟨Ksite, Knorm, Kgen, Kideal, A₀, T₀, Kproj,
    hKsite, hKnorm, hKgen, hKideal, hA₀, hT₀, hKproj, hgen, ?_⟩
  intro X J L M hM p P E hP hE hdim hmP hDP
  obtain ⟨hvars, hI, hn⟩ := preparedSampler_dimensions L dim hM
  apply hs (PreparedSamplerBlock L dim) (Nat.cast_nonneg _) hP hE hdim hmP hDP
  · exact_mod_cast hvars
  · intro j; exact_mod_cast hI j
  · intro j; exact_mod_cast hn j
  · intro j i
    simpa only [PreparedSamplerBlock, Fintype.card_fin] using preparedSamplerBlockCount_spectrum m dim j

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

noncomputable def allocatedProductCoarseNNMesh (m : ℕ) {dim : ℕ}
    {G : Type*} [Fintype G] (X : Type*) [Fintype X]
    (selection : Fin dim ↪ G) (M modulus : ℕ) (p pAccuracy w v E : ℝ) : ℝ≥0 :=
  ⟨allocatedProductCoarseMesh m X selection M modulus p pAccuracy w v E,
    (allocatedProductCoarseMesh_pos m X selection M modulus p pAccuracy w v E).le⟩

private theorem cubeCount_rescale_bound_change_decidable {X : Type} [Fintype X]
    (d₁ d₂ : DecidableEq X) (N : X → ℕ) (dim : ℕ) {A Z C : ℝ}
    (h : (@integerBoxCubeCount X _ d₁ N dim : ℝ) * A / Z ≤ C) :
    (@integerBoxCubeCount X _ d₂ N dim : ℝ) * A / Z ≤ C := by
  have hd : d₁ = d₂ := Subsingleton.elim _ _
  cases hd
  exact h

private theorem sum_compare_enumerations {T : Type} (a b : Fintype T)
    (f g : T → ℝ) (h : ∀ x, f x = g x) :
    @Finset.sum T ℝ _ (@Finset.univ T a) f = @Finset.sum T ℝ _ (@Finset.univ T b) g := by
  have hab : a = b := Subsingleton.elim _ _
  cases hab
  exact Finset.sum_congr rfl (fun x _ => h x)

variable {m s nX : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (modulus : ℕ) [NeZero modulus] (q : (Fin nX) → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U b S))
variable (coverWitness : (r : AllocatedPositiveResidue (dim := (s + 1)) B U b S (residueRefinedPeriod modulus q)) →
  AllocatedFullGridResidueWitness (dim := (s + 1)) B U b S (residueRefinedPeriod modulus q) r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (hR : ∀ j, 0 < R j)
variable (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin (s + 1) ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : (Fin nX) → ℕ) {τ : ℝ}
local notation "W" => allocatedPhysicalRootBudget B U b S (fun _ => 0)
local notation "hW" => allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)
variable (period : ℕ) [NeZero period]

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => {s : Finset (Fin (s + 1)) // s ∈ rowSets j})
local notation "tuples" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U b S)
local notation "refined" => residueRefinedPeriod modulus q
local notation "positive" => AllocatedPositiveResidue (dim := (s + 1)) B U b S refined
local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "law" => FiniteProbabilityWeights.fiberLaw
  (principalTupleWeights (α := Fin (s + 1)) B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)) (principalResidueLabel refined)

variable (F : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1))
  (allocatedPrincipalSides B U b S) → AllocatedFiniteIdealData (Fin (s + 1)) I n)

variable [gridPeriodNeZero : ∀ (r : AllocatedPositiveResidue (dim := (s + 1)) B U b S (residueRefinedPeriod modulus q))
  (a : {a // allocatedGridAxis (I := I) U b S.value a}) (ki : ((coverWitness r).expansion a).Term),
  NeZero (((coverWitness r).expansion a).period ki)]

variable (base : (Fin nX) → ℤ)

variable (pI p0 pAccuracy w v E0 D O pc gc Pτ Z : ℝ)
local notation "meshR" => allocatedProductCoarseMesh m (Fin nX) selection M modulus p0 pAccuracy w v E0
local notation "cost" => allocatedCoarseNativeLog m (s + 1) pI p0 pAccuracy w v E0 D O pc gc Pτ

variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) q))
variable (p : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem allocated_coarse_cube_native_partner
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (rho : AllocatedPositiveResidue (dim := s + 1) B U b S (residueRefinedPeriod modulus q))
    (cell : cells) [∀ z, NeZero (N z)]
    (hresources : AllocatedCoarseFamilyResources (Kcov := Kcov) (τ := τ)
      B U b S (Fin nX) modulus q wholeReference coverWitness d x hM selection hx N period F base
      pI p0 pAccuracy w v E0 D O pc gc Pτ Z)
    {budget : ℝ} (hbudget : 0 ≤ budget) (hdimension : (nX : ℝ) ≤ budget)
    (hcost : cost ≤ budget) (hZ : 0 < Z)
    (f : (Fin nX → ℤ) → ℂ) (hf : ∀ u ∈ integerBox N, ‖f u‖ ≤ 1)
    (hpositive : Real.exp (-budget) ≤
      (((integerBoxCubeCount N (s + 1) : ℂ) *
        (𝔼 cube : SupportedCube (s + 1) (integerBox N : Set (Fin nX → ℤ)),
          allocatedAmbientNormalizedSpatialApproximation (τ := τ) B U b S (Fin nX) modulus q wholeReference coverWitness hb o bW d x hM selection hx N hW (allocatedProductCoarseNNMesh m (Fin nX) selection M modulus p0 pAccuracy w v E0) base cells p hm rho cell period (F (coverWitness rho).representative).coefficient (F (coverWitness rho).representative).factor (fun site y => conjugationPower site.card (f (fun z => ⌊y z⌋)))
            ((physicalCubeParametersEquiv (Fin nX) (s + 1)).symm cube.val))) / (Z : ℂ)).re) :
    ∃ (spatial : Fin nX → SpatialSiteLabel (Fin (s + 1)) modulus 4 (allocatedProductCoarseNNMesh m (Fin nX) selection M modulus p0 pAccuracy w v E0))
      (kg : ∀ i, ((coverWitness rho).expansion i).Term)
      (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period))
      (k : (F (coverWitness rho).representative).Term) (gridLabel : ∀ i, ZMod (((coverWitness rho).expansion i).period (kg i)))
      (V : NativeSampleCorrelation (fun _ : Fin nX => 1) s
        ((budget + 2) ^ Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))
        (integerBox N) id
        (fun u => f u * allocatedRecenteredNormalizedSiteFactor (τ := τ) B U b S (Fin nX) modulus q
          wholeReference coverWitness hb o bW d x N (allocatedProductCoarseNNMesh m (Fin nX) selection M modulus p0 pAccuracy w v E0) base p hm rho cell.val period
          spatial kg label ((F (coverWitness rho).representative).factor k ∅) ∅ gridLabel u)),
      V.test.normBound ≤ 1 := by
  rcases hresources with ⟨hmass, _, hunit⟩
  apply allocated_genuine_cube_native_partner B U b S modulus q wholeReference coverWitness
    hb o bW d x hM selection hx N hW (allocatedProductCoarseNNMesh m (Fin nX) selection M modulus p0 pAccuracy w v E0) base cells p hm rho cell period (F (coverWitness rho).representative).coefficient (F (coverWitness rho).representative).factor
    (fun spatial kg k site gridLabel z => (hunit rho cell.val spatial kg k site gridLabel).1 z)
    hbudget hdimension hZ _ f hf hpositive
  have hbound := (hmass rho).trans (Real.exp_le_exp.mpr hcost)
  have hbound' := cubeCount_rescale_bound_change_decidable
    (fun a b : Fin nX => Classical.propDecidable (a = b)) (instDecidableEqFin nX) N (s + 1) hbound
  refine le_trans (le_of_eq ?_) hbound'
  apply congrArg (fun t : ℝ => (integerBoxCubeCount N (s + 1) : ℝ) * t / Z)
  dsimp only [allocatedRefinedConstructedSpatialCoefficientAt, allocatedProductCoarseNNMesh]
  refine sum_compare_enumerations _ _ _ _ ?_
  intro t
  refine sum_compare_enumerations _ _ _ _ ?_
  intro label
  refine sum_compare_enumerations _ _ _ _ ?_
  intro k
  refine sum_compare_enumerations _ _ _ _ ?_
  intro gridLabel
  rfl

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem allocated_coarse_mixture_native_partner [∀ z, NeZero (N z)]
    (hresources : AllocatedCoarseFamilyResources (Kcov := Kcov) (τ := τ)
      B U b S (Fin nX) modulus q wholeReference coverWitness d x hM selection hx N period F base
      pI p0 pAccuracy w v E0 D O pc gc Pτ Z)
    {budget : ℝ} (hbudget : 0 ≤ budget) (hdimension : (nX : ℝ) ≤ budget)
    (hcost : cost ≤ budget) (hZ : 0 < Z)
    (V₀ : Option (LayerSamplerVariables G I n B) × Fin nX → ℝ)
    (hV₀ : ∀ z, 0 < V₀ z) (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells V₀ z)
    (f : (Fin nX → ℤ) → ℂ) (hf : ∀ u ∈ integerBox N, ‖f u‖ ≤ 1)
    (hpositive : Real.exp (-budget) ≤
      ((law).complexMean (fun r =>
        if hr : 0 < (principalTupleWeights (α := Fin (s + 1)) B (layerSamplerDegree I n)
            (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
            (Finset.univ.filter (fun y => principalResidueLabel refined y = r)) then
          ∑ a : cells, (selectedResidueCellWeight q cells V₀ a : ℂ) *
            ((integerBoxCubeCount N (s + 1) : ℂ) *
              𝔼 cube : SupportedCube (s + 1) (integerBox N : Set (Fin nX → ℤ)),
                allocatedAmbientNormalizedSpatialApproximation (τ := τ) B U b S (Fin nX) modulus q
                  wholeReference coverWitness hb o bW d x hM selection hx N hW (allocatedProductCoarseNNMesh m (Fin nX) selection M modulus p0 pAccuracy w v E0) base cells p hm
                  ⟨r, hr⟩ a period (F (coverWitness ⟨r, hr⟩).representative).coefficient
                  (F (coverWitness ⟨r, hr⟩).representative).factor
                  (fun site y => conjugationPower site.card (f (fun z => ⌊y z⌋)))
                  ((physicalCubeParametersEquiv (Fin nX) (s + 1)).symm cube.val))
        else 0) / (Z : ℂ)).re) :
    ∃ (r : positive) (a : cells)
      (spatial : Fin nX → SpatialSiteLabel (Fin (s + 1)) modulus 4 (allocatedProductCoarseNNMesh m (Fin nX) selection M modulus p0 pAccuracy w v E0))
      (kg : ∀ i, ((coverWitness r).expansion i).Term)
      (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period))
      (k : (F (coverWitness r).representative).Term)
      (gridLabel : ∀ i, ZMod (((coverWitness r).expansion i).period (kg i)))
      (V : NativeSampleCorrelation (fun _ : Fin nX => 1) s
        ((budget + 2) ^ Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))
        (integerBox N) id
        (fun u => f u * allocatedRecenteredNormalizedSiteFactor (τ := τ) B U b S (Fin nX) modulus q
          wholeReference coverWitness hb o bW d x N (allocatedProductCoarseNNMesh m (Fin nX) selection M modulus p0 pAccuracy w v E0) base p hm r a.val period
          spatial kg label ((F (coverWitness r).representative).factor k ∅) ∅ gridLabel u)),
      V.test.normBound ≤ 1 := by
  let value := fun (r : positive) (a : cells) =>
    (integerBoxCubeCount N (s + 1) : ℂ) *
      𝔼 cube : SupportedCube (s + 1) (integerBox N : Set (Fin nX → ℤ)),
        allocatedAmbientNormalizedSpatialApproximation (τ := τ) B U b S (Fin nX) modulus q
          wholeReference coverWitness hb o bW d x hM selection hx N hW (allocatedProductCoarseNNMesh m (Fin nX) selection M modulus p0 pAccuracy w v E0) base cells p hm
          r a period (F (coverWitness r).representative).coefficient
          (F (coverWitness r).representative).factor
          (fun site y => conjugationPower site.card (f (fun z => ⌊y z⌋)))
          ((physicalCubeParametersEquiv (Fin nX) (s + 1)).symm cube.val)
  obtain ⟨r, a, _, ha⟩ := exists_allocated_genuine_source_cell B U b S refined q cells V₀ hV₀
    hmass value (Z : ℂ) hpositive
  obtain ⟨spatial, kg, label, k, gridLabel, V, hV⟩ :=
    allocated_coarse_cube_native_partner B U b S modulus q wholeReference coverWitness hb o bW d
      x hM selection hx N period F base pI p0 pAccuracy w v E0 D O pc gc Pτ Z cells p hm r a
      hresources hbudget hdimension hcost hZ f hf ha
  exact ⟨r, a, spatial, kg, label, k, gridLabel, V, hV⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

variable {m s nX : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (modulus : ℕ) [NeZero modulus] (q : (Fin nX) → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U b S))
variable (coverWitness : (r : AllocatedPositiveResidue (dim := (s + 1)) B U b S (residueRefinedPeriod modulus q)) →
  AllocatedFullGridResidueWitness (dim := (s + 1)) B U b S (residueRefinedPeriod modulus q) r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (hR : ∀ j, 0 < R j)
variable (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin (s + 1) ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : (Fin nX) → ℕ) {τ : ℝ}
local notation "W" => allocatedPhysicalRootBudget B U b S (fun _ => 0)
local notation "hW" => allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (period : ℕ) [NeZero period]

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => {s : Finset (Fin (s + 1)) // s ∈ rowSets j})
local notation "tuples" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U b S)
local notation "refined" => residueRefinedPeriod modulus q
local notation "positive" => AllocatedPositiveResidue (dim := (s + 1)) B U b S refined
local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "law" => FiniteProbabilityWeights.fiberLaw
  (principalTupleWeights (α := Fin (s + 1)) B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)) (principalResidueLabel refined)

variable (F : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1))
  (allocatedPrincipalSides B U b S) → AllocatedFiniteIdealData (Fin (s + 1)) I n)

variable [gridPeriodNeZero : ∀ (r : AllocatedPositiveResidue (dim := (s + 1)) B U b S (residueRefinedPeriod modulus q))
  (a : {a // allocatedGridAxis (I := I) U b S.value a}) (ki : ((coverWitness r).expansion a).Term),
  NeZero (((coverWitness r).expansion a).period ki)]

variable (base : (Fin nX) → ℤ)

variable (pI p0 pAccuracy w v E0 D O pc gc Pτ Z : ℝ)
local notation "meshR" => allocatedProductCoarseMesh m (Fin nX) selection M modulus p0 pAccuracy w v E0
local notation "cost" => allocatedCoarseNativeLog m (s + 1) pI p0 pAccuracy w v E0 D O pc gc Pτ

variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) q))
variable (p : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem allocated_coarse_mixture_native_model [∀ z, NeZero (N z)]
    (hresources : AllocatedCoarseFamilyResources (Kcov := Kcov) (τ := τ)
      B U b S (Fin nX) modulus q wholeReference coverWitness d x hM selection hx N period F base
      pI p0 pAccuracy w v E0 D O pc gc Pτ Z)
    {budget : ℝ} (hbudget : 0 ≤ budget) (hdimension : (nX : ℝ) ≤ budget)
    (hcost : cost ≤ budget) (hZ : 0 < Z)
    (V₀ : Option (LayerSamplerVariables G I n B) × Fin nX → ℝ)
    (hV₀ : ∀ z, 0 < V₀ z) (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells V₀ z)
    (f : (Fin nX → ℤ) → ℂ) (hf : ∀ u ∈ integerBox N, ‖f u‖ ≤ 1)
    (hpositive : Real.exp (-budget) ≤
      ((law).complexMean (fun r =>
        if hr : 0 < (principalTupleWeights (α := Fin (s + 1)) B (layerSamplerDegree I n)
            (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
            (Finset.univ.filter (fun y => principalResidueLabel refined y = r)) then
          ∑ a : cells, (selectedResidueCellWeight q cells V₀ a : ℂ) *
            ((integerBoxCubeCount N (s + 1) : ℂ) *
              𝔼 cube : SupportedCube (s + 1) (integerBox N : Set (Fin nX → ℤ)),
                allocatedAmbientNormalizedSpatialApproximation (τ := τ) B U b S (Fin nX) modulus q
                  wholeReference coverWitness hb o bW d x hM selection hx N hW (allocatedProductCoarseNNMesh m (Fin nX) selection M modulus p0 pAccuracy w v E0) base cells p hm
                  ⟨r, hr⟩ a period (F (coverWitness ⟨r, hr⟩).representative).coefficient
                  (F (coverWitness ⟨r, hr⟩).representative).factor
                  (fun site y => conjugationPower site.card (f (fun z => ⌊y z⌋)))
                  ((physicalCubeParametersEquiv (Fin nX) (s + 1)).symm cube.val))
        else 0) / (Z : ℂ)).re) :
    ∃ (r : positive) (a : cells)
      (spatial : Fin nX → SpatialSiteLabel (Fin (s + 1)) modulus 4 (allocatedProductCoarseNNMesh m (Fin nX) selection M modulus p0 pAccuracy w v E0))
      (kg : ∀ i, ((coverWitness r).expansion i).Term)
      (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period))
      (k : (F (coverWitness r).representative).Term)
      (gridLabel : ∀ i, ZMod (((coverWitness r).expansion i).period (kg i)))
      (G : integerBox N → ℂ),
      Nonempty (NativeSampleModel (fun _ : Fin nX => 1) s
        ((budget + 2) ^ Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))
        (fun u : integerBox N => u.val) G) ∧
      (∀ u, ‖allocatedRecenteredNormalizedSiteFactor (τ := τ) B U b S (Fin nX) modulus q
        wholeReference coverWitness hb o bW d x N
        (allocatedProductCoarseNNMesh m (Fin nX) selection M modulus p0 pAccuracy w v E0)
        base p hm r a.val period spatial kg label
        ((F (coverWitness r).representative).factor k ∅) ∅ gridLabel u‖ ≤ 1) ∧
      Real.exp (-((budget + 2) ^ Classical.choose
        (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))) ≤
        ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N)).correlation
          (fun u => f u.val)
          (fun u => star (allocatedRecenteredNormalizedSiteFactor (τ := τ) B U b S (Fin nX) modulus q
            wholeReference coverWitness hb o bW d x N
            (allocatedProductCoarseNNMesh m (Fin nX) selection M modulus p0 pAccuracy w v E0)
            base p hm r a.val period spatial kg label
            ((F (coverWitness r).representative).factor k ∅) ∅ gridLabel u.val) * G u)‖ := by
  obtain ⟨r, a, spatial, kg, label, k, gridLabel, V, hV⟩ :=
    allocated_coarse_mixture_native_partner B U b S modulus q wholeReference coverWitness hb o bW d
      x hM selection hx N period F base pI p0 pAccuracy w v E0 D O pc gc Pτ Z cells p hm
      hresources hbudget hdimension hcost hZ V₀ hV₀ hmass f hf hpositive
  obtain ⟨G, hG, hcorrelation⟩ := nativeCorrelation_restrict_model (integerBox N) (integerBox_nonempty N)
    (fun _ : Fin nX => 1) s _ id f
    (allocatedRecenteredNormalizedSiteFactor (τ := τ) B U b S (Fin nX) modulus q wholeReference
      coverWitness hb o bW d x N
      (allocatedProductCoarseNNMesh m (Fin nX) selection M modulus p0 pAccuracy w v E0)
      base p hm r a.val period spatial kg label
      ((F (coverWitness r).representative).factor k ∅) ∅ gridLabel) V hV
  refine ⟨r, a, spatial, kg, label, k, gridLabel, G, hG, ?_, hcorrelation⟩
  intro u
  apply allocatedRecenteredNormalizedSiteFactor_norm_le
  exact (hresources.2.2 r a.val spatial kg k ∅ gridLabel).1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

variable {m s nX : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (modulus : ℕ) [NeZero modulus] (q : (Fin nX) → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U b S))
variable (coverWitness : (r : AllocatedPositiveResidue (dim := (s + 1)) B U b S (residueRefinedPeriod modulus q)) →
  AllocatedFullGridResidueWitness (dim := (s + 1)) B U b S (residueRefinedPeriod modulus q) r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (hR : ∀ j, 0 < R j)
variable (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin (s + 1) ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : (Fin nX) → ℕ) {τ : ℝ}
local notation "W" => allocatedPhysicalRootBudget B U b S (fun _ => 0)
local notation "hW" => allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (period : ℕ) [NeZero period]

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => {s : Finset (Fin (s + 1)) // s ∈ rowSets j})
local notation "tuples" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U b S)
local notation "refined" => residueRefinedPeriod modulus q
local notation "positive" => AllocatedPositiveResidue (dim := (s + 1)) B U b S refined
local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "law" => FiniteProbabilityWeights.fiberLaw
  (principalTupleWeights (α := Fin (s + 1)) B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)) (principalResidueLabel refined)

variable (F : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1))
  (allocatedPrincipalSides B U b S) → AllocatedFiniteIdealData (Fin (s + 1)) I n)

variable [gridPeriodNeZero : ∀ (r : AllocatedPositiveResidue (dim := (s + 1)) B U b S (residueRefinedPeriod modulus q))
  (a : {a // allocatedGridAxis (I := I) U b S.value a}) (ki : ((coverWitness r).expansion a).Term),
  NeZero (((coverWitness r).expansion a).period ki)]

variable (base : (Fin nX) → ℤ)

variable (pI p0 pAccuracy w v E0 D O pc gc Pτ Z : ℝ)
local notation "meshR" => allocatedProductCoarseMesh m (Fin nX) selection M modulus p0 pAccuracy w v E0
local notation "cost" => allocatedCoarseNativeLog m (s + 1) pI p0 pAccuracy w v E0 D O pc gc Pτ

variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) q))
variable (p : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

noncomputable def allocatedCoarseCubeSource
    (V₀ : Option (LayerSamplerVariables G I n B) × Fin nX → ℝ) (f : (Fin nX → ℤ) → ℂ) : ℂ :=
  ((law).complexMean (fun r =>
        if hr : 0 < (principalTupleWeights (α := Fin (s + 1)) B (layerSamplerDegree I n)
            (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
            (Finset.univ.filter (fun y => principalResidueLabel refined y = r)) then
          ∑ a : cells, (selectedResidueCellWeight q cells V₀ a : ℂ) *
            ((integerBoxCubeCount N (s + 1) : ℂ) *
              𝔼 cube : SupportedCube (s + 1) (integerBox N : Set (Fin nX → ℤ)),
                allocatedAmbientNormalizedSpatialApproximation (τ := τ) B U b S (Fin nX) modulus q
                  wholeReference coverWitness hb o bW d x hM selection hx N hW (allocatedProductCoarseNNMesh m (Fin nX) selection M modulus p0 pAccuracy w v E0) base cells p hm
                  ⟨r, hr⟩ a period (F (coverWitness ⟨r, hr⟩).representative).coefficient
                  (F (coverWitness ⟨r, hr⟩).representative).factor
                  (fun site y => conjugationPower site.card (f (fun z => ⌊y z⌋)))
                  ((physicalCubeParametersEquiv (Fin nX) (s + 1)).symm cube.val))
        else 0) / (Z : ℂ))

def allocatedCoarseSiteTwists : Set (integerBox N → ℂ) :=
  {ψ | ∃ (r : positive) (a : cells)
      (spatial : Fin nX → SpatialSiteLabel (Fin (s + 1)) modulus 4
        (allocatedProductCoarseNNMesh m (Fin nX) selection M modulus p0 pAccuracy w v E0))
      (kg : ∀ i, ((coverWitness r).expansion i).Term)
      (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period))
      (k : (F (coverWitness r).representative).Term)
      (gridLabel : ∀ i, ZMod (((coverWitness r).expansion i).period (kg i))),
      ψ = fun u => allocatedRecenteredNormalizedSiteFactor (τ := τ) B U b S (Fin nX) modulus q
        wholeReference coverWitness hb o bW d x N
        (allocatedProductCoarseNNMesh m (Fin nX) selection M modulus p0 pAccuracy w v E0)
        base p hm r a.val period spatial kg label
        ((F (coverWitness r).representative).factor k ∅) ∅ gridLabel u.val}

theorem allocated_coarse_native_family [∀ z, NeZero (N z)]
    (hresources : AllocatedCoarseFamilyResources (Kcov := Kcov) (τ := τ)
      B U b S (Fin nX) modulus q wholeReference coverWitness d x hM selection hx N period F base
      pI p0 pAccuracy w v E0 D O pc gc Pτ Z)
    {budget : ℝ} (hbudget : 0 ≤ budget) (hdimension : (nX : ℝ) ≤ budget)
    (hcost : cost ≤ budget) (hZ : 0 < Z)
    (V₀ : Option (LayerSamplerVariables G I n B) × Fin nX → ℝ)
    (hV₀ : ∀ z, 0 < V₀ z) (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells V₀ z) :
    let twists := allocatedCoarseSiteTwists (M := M) (τ := τ) B U b S modulus q wholeReference coverWitness
      hb o bW d x selection N period F base p0 pAccuracy w v E0 cells p hm
    (∀ ψ ∈ twists, ∀ u, ‖ψ u‖ ≤ 1) ∧
    ∀ (f : (Fin nX → ℤ) → ℂ), (∀ u ∈ integerBox N, ‖f u‖ ≤ 1) →
      Real.exp (-budget) ≤ (allocatedCoarseCubeSource (τ := τ) B U b S modulus q wholeReference coverWitness
        hb o bW d x hM selection hx N period F base p0 pAccuracy w v E0 Z cells p hm V₀ f).re →
      ∃ ψ ∈ twists, ∃ g : integerBox N → ℂ,
        Nonempty (NativeSampleModel (fun _ : Fin nX => 1) s
          ((budget + 2) ^ Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))
          (fun u : integerBox N => u.val) g) ∧
        Real.exp (-((budget + 2) ^ Classical.choose
          (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N)).correlation
            (fun u => f u.val) (fun u => star (ψ u) * g u)‖ := by
  intro twists
  constructor
  · intro ψ hψ u
    obtain ⟨r, a, spatial, kg, label, k, gridLabel, rfl⟩ := hψ
    apply allocatedRecenteredNormalizedSiteFactor_norm_le
    exact (hresources.2.2 r a.val spatial kg k ∅ gridLabel).1
  · intro f hf hpositive
    obtain ⟨r, a, spatial, kg, label, k, gridLabel, g, hg, _, hcorrelation⟩ :=
      allocated_coarse_mixture_native_model B U b S modulus q wholeReference coverWitness
        hb o bW d x hM selection hx N period F base pI p0 pAccuracy w v E0 D O pc gc Pτ Z
        cells p hm hresources hbudget hdimension hcost hZ V₀ hV₀ hmass f hf hpositive
    refine ⟨_, ⟨r, a, spatial, kg, label, k, gridLabel, rfl⟩, g, hg, hcorrelation⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

variable {m s nX : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {Kcov : Fin m → Type} [∀ j, Fintype (Kcov j)]
variable (q N : Fin nX → ℕ) (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin (s + 1) ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (τ : ℝ) (base : Fin nX → ℤ)
variable (pI p0 pAccuracy w v E0 D O pc gc Pτ Z : ℝ)

local notation "tuples" => PrincipalIntegerTuples B (layerSamplerDegree I n)
  (Fin (s + 1)) (allocatedPrincipalSides B U b S)

structure AllocatedCoarseSourceData where
  modulus : ℕ
  [modulusNonzero : NeZero modulus]
  [refinedNonzero : NeZero (residueRefinedPeriod modulus q)]
  denominator : ℕ
  [denominatorNonzero : NeZero denominator]
  period : ℕ
  [periodNonzero : NeZero period]
  reference : (PrincipalTupleIndex B (layerSamplerDegree I n) →
    Option (Fin (s + 1)) → ZMod (residueRefinedPeriod modulus q)) → tuples
  cover : (r : AllocatedPositiveResidue (dim := s + 1) B U b S (residueRefinedPeriod modulus q)) →
    AllocatedFullGridResidueWitness (dim := s + 1) B U b S (residueRefinedPeriod modulus q) r.val
  [gridPeriodNonzero : ∀ (r : AllocatedPositiveResidue (dim := s + 1) B U b S
      (residueRefinedPeriod modulus q)) (a : {a // allocatedGridAxis (I := I) U b S.value a})
      (ki : ((cover r).expansion a).Term), NeZero (((cover r).expansion a).period ki)]
  ideal : tuples → AllocatedFiniteIdealData (Fin (s + 1)) I n
  resources : AllocatedCoarseFamilyResources (Kcov := Kcov) (τ := τ)
    B U b S (Fin nX) modulus q reference cover denominator x hM selection hx N period ideal base
    pI p0 pAccuracy w v E0 D O pc gc Pτ Z

attribute [local instance] AllocatedCoarseSourceData.modulusNonzero
  AllocatedCoarseSourceData.refinedNonzero AllocatedCoarseSourceData.denominatorNonzero
  AllocatedCoarseSourceData.periodNonzero AllocatedCoarseSourceData.gridPeriodNonzero

variable (A : AllocatedCoarseSourceData (Kcov := Kcov) B U b S q N x hM selection hx τ base
  pI p0 pAccuracy w v E0 D O pc gc Pτ Z)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Kcov j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) q))
variable (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable {B U b S q N x hM selection hx τ base pI p0 pAccuracy w v E0 D O pc gc Pτ Z}

noncomputable def AllocatedCoarseSourceData.source
    (V₀ : Option (LayerSamplerVariables G I n B) × Fin nX → ℝ)
    (f : (Fin nX → ℤ) → ℂ) : ℂ :=
  allocatedCoarseCubeSource (τ := τ) B U b S A.modulus q A.reference A.cover
    hb o bW A.denominator x hM selection hx N A.period A.ideal base
    p0 pAccuracy w v E0 Z cells poly hmem V₀ f

def AllocatedCoarseSourceData.twists : Set (integerBox N → ℂ) :=
  allocatedCoarseSiteTwists (M := M) (τ := τ) B U b S A.modulus q A.reference A.cover
    hb o bW A.denominator x selection N A.period A.ideal base p0 pAccuracy w v E0 cells poly hmem

theorem AllocatedCoarseSourceData.twists_norm (ψ)
    (hψ : ψ ∈ A.twists hb o bW cells poly hmem) (u) : ‖ψ u‖ ≤ 1 := by
  obtain ⟨r, a, spatial, kg, label, k, gridLabel, rfl⟩ := hψ
  apply allocatedRecenteredNormalizedSiteFactor_norm_le
  exact (A.resources.2.2 r a.val spatial kg k ∅ gridLabel).1

theorem AllocatedCoarseSourceData.detect [∀ z, NeZero (N z)]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {budget : ℝ} (hbudget : 0 ≤ budget) (hdimension : (nX : ℝ) ≤ budget)
    (hcost : allocatedCoarseNativeLog m (s + 1) pI p0 pAccuracy w v E0 D O pc gc Pτ ≤ budget)
    (hZ : 0 < Z)
    (V₀ : Option (LayerSamplerVariables G I n B) × Fin nX → ℝ)
    (hV₀ : ∀ z, 0 < V₀ z) (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells V₀ z)
    (f : (Fin nX → ℤ) → ℂ) (hf : ∀ u ∈ integerBox N, ‖f u‖ ≤ 1)
    (hpositive : Real.exp (-budget) ≤ (A.source hb o bW cells poly hmem V₀ f).re) :
    ∃ ψ ∈ A.twists hb o bW cells poly hmem, ∃ g : integerBox N → ℂ,
      Nonempty (NativeSampleModel (fun _ : Fin nX => 1) s
        ((budget + 2) ^ Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))
        (fun u : integerBox N => u.val) g) ∧
      Real.exp (-((budget + 2) ^ Classical.choose
        (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))) ≤
        ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N)).correlation
          (fun u => f u.val) (fun u => star (ψ u) * g u)‖ := by
  have h := allocated_coarse_native_family B U b S A.modulus q A.reference A.cover
    hb o bW A.denominator x hM selection hx N A.period A.ideal base
    pI p0 pAccuracy w v E0 D O pc gc Pτ Z cells poly hmem
    A.resources hbudget hdimension hcost hZ V₀ hV₀ hmass
  exact h.2 f hf hpositive

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq fullGridCoverAxisDecidableEq

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin (s + 1)) (Fin.val j + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : jets j → Finset (Fin (s + 1))))
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
local notation "fullRows" => (fun j => (Subtype.val : rowSets j → Finset (Fin (s + 1))))

def AllocatedCanonicalNativeData (p g Psp E e pNum Pbase Qraw pAccuracy pSampling O : ℝ) (hP : 0 ≤ Psp)
    (δ : ℝ≥0) (A Kraw Ksite Kgen : ℕ)
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := (s + 1)) B U b S (q.val : ℕ)) →
      AllocatedFullGridResidueWitness (dim := (s + 1)) B U b S (q.val : ℕ) r.val)
    (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin) (η : ℝ) (hη : 0 < η) : Prop :=
  let Dgeom := allocatedComparisonDimension m p
  let cgeom := g
  let pc := p
  let gc := g
  let Pτ := Psp
  ∃ hgridPeriod : ∀ (q : AllocatedRefinedPeriodIndex m Psp)
      (r : AllocatedPositiveResidue (dim := (s + 1)) B U b S (q.val : ℕ))
      (a : {a // allocatedGridAxis (I := I) U b S.value a})
      (k : ((witnesses q r).expansion a).Term),
      0 < ((witnesses q r).expansion a).period k,
  let w := allocatedSiteKernelMaskLog m Psp
  let v := allocatedIdealProfileLog m pAccuracy e
  let Pfinal := sourceCoverParameter (s + 1) Kraw Psp pNum Qraw
    (allocatedSiteErrorFourierOutput m pSampling w v)
    (allocatedSeparatedGeometryLog m Psp pAccuracy pSampling w v (E + 2))
  let Mk := scalarKernelCutoff (Fin (s + 1)) G M Dwin η
  let hMk := (scalarKernelCutoff_bounds (Fin (s + 1)) G hM hDwin hη).1
  ∀ (selection : Fin (s + 1) ↪ G) (_hqDim : (s + 1) ≤ m + 1)
    (_hcard : (s + 1) * ((s + 1) + 2) ≤ Fintype.card G) [Nonempty (Fin (s + 1))]
    (hMkPsp : (Mk : ℝ) ≤ Real.exp Psp) (_hlarge : Mk ≤ S.value)
    (_hKgen : 2 ≤ Kgen)
    (_hSampling : PhysicalAmbientRowsKernelSampling.{0,0,0} m (s + 1) Kgen
      (fun j => (rowSets j : Type)) fullRows),
  let Kernel := G → IntegerScalarCubeBox (Fin (s + 1)) S.value
  let Good := GoodScalarKernelTuple (L := S.value) selection (1 / (Mk : ℝ)) Mk
  let GoodKernel := {x : Kernel // Good x}
  ∃ (d : GoodKernel → ℕ) (hd : ∀ x, 0 < d x),
    let : ∀ x, NeZero (d x) := fun x => ⟨(hd x).ne'⟩
    (∀ x, (d x : ℝ) ≤ Real.exp ((Pbase + A) ^ A)) ∧
  ∃ (modulus : GoodKernel → ℕ) (hmodulus : ∀ x, 0 < modulus x),
    let : ∀ x, NeZero (modulus x) := fun x => ⟨(hmodulus x).ne'⟩
    ∃ hmodulusSize : ∀ x, modulus x ≤ Mk ^ (m + 1),
    (∀ (x : GoodKernel) (root : G → ℤ), integerScalarLattice (Unit ⊕ Fin (s + 1)) (modulus x : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x.val) selection)
        (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x.val) selection)) ∧
    (∀ (x : GoodKernel) j, integerScalarLattice (jets j) (modulus x : ℤ) ≤
      (scalarKernelIntegerJet x.val (j.val + 1) (jetRows j)).mulVecLin.range) ∧
    ∀ (_block : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, jets a.val.1 ↪ B a.val)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin (s + 1))) U)] [BorelSpace (SiteTorus (Finset (Fin (s + 1))) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Kcov : Fin m → Type} [∀ j, Fintype (Kcov j)]
    (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCp : ∀ j, (C j : ℝ) ≤ Real.exp pNum) (_hVp : ∀ j, (V j : ℝ) ≤ Real.exp pNum)
    (_hCpAccuracy : ∀ j, (C j : ℝ) ≤ Real.exp pAccuracy)
    (_hVpAccuracy : ∀ j, (V j : ℝ) ≤ Real.exp pAccuracy)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hCgeom : ∀ j, Cinv j ≤ Real.exp g)
    (_hCovEarly : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp g)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    [CompactSpace (CoefficientTorus (K := Fin (s + 1)) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U)] [BorelSpace (CoefficientTorus (K := Fin (s + 1)) U)]
    (μsmall : Measure (CoefficientTorus (K := Fin (s + 1)) U)) [μsmall.IsAddLeftInvariant] [IsProbabilityMeasure μsmall]
    (nX : ℕ)
    (hXPsp : (Fintype.card (Fin nX) : ℝ) ≤ Psp)
    (q : (Fin nX) → ℕ) (hq : ∀ t, 0 < q t) (hqPsp : ∀ t, (q t : ℝ) ≤ Real.exp Psp),
    let refined := fun x => residueRefinedPeriod (modulus x) q
    let index := fun x => allocatedRefinedPeriodIndex m hP hMkPsp
      (hmodulusSize x)
      hXPsp (hmodulus x) q hq hqPsp
    let : ∀ x, NeZero (refined x) := fun x => ⟨(residueRefinedPeriod_pos (hmodulus x) q hq).ne'⟩
    let W := allocatedPhysicalRootBudget B U b S (fun _ => 0)
    let hW := allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)
    let indices := PrincipalTupleIndex B (layerSamplerDegree I n)
    let ξ := normalizedTupleNarrowWidth (Fin nX) indices selection Mk Psp ((E + 2) + 2)
    let hξ := normalizedTupleNarrowWidth_pos (Fin nX) indices selection Mk Psp ((E + 2) + 2)
    let _mesh := fun x : GoodKernel =>
      allocatedProductCoarseMesh m (Fin nX) selection Mk (modulus x) Psp pAccuracy w v (E + 2)
    let τ := Real.exp (-Psp)
    let hτ := Real.exp_pos (-Psp)
    let Psamp : ℝ := ((s + 1) + 2 : ℕ) * Psp
    let sourceThreshold := (Pfinal + Ksite) ^ Ksite
    let genuineThreshold := (allocatedCutoffSamplingLog m (s + 1) Pbase
      (normalizedSiteCutoffBound : ℝ) 0 Psamp + Kgen) ^ Kgen
    let threshold := allocatedCanonicalCubeThreshold Psp sourceThreshold genuineThreshold
    ∀ (N : (Fin nX) → ℕ) (hN : ∀ t, 0 < N t)
    (_hsize : ∀ t, Real.exp threshold ≤ (N t : ℝ))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
    (_hpoly : ∀ j, DegreeLE (1 : (Fin nX) → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
    {rank : ℝ}
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) rank (U j) (poly j))
    (_hRank : Real.exp threshold ≤ rank)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) q))
    (_hcells : cells.Nonempty)
    (bases : Finset ((Fin nX) → ℤ)) (_hbases : bases.Nonempty)
    (_hbaseBox : ∀ base ∈ bases, base ∈ trimmedIntegerBox N (spatialTrimMargin τ N)),
    let V₀ := narrowTrimmedSpatialWidths (G := G) (J := indices) W τ ξ N
    let Z := selectedJointDensityMass bases q cells V₀
      (allocatedJointBaseDensity B U b hb o hR hσ S (Fin nX) poly hmem)
    let _law := principalTupleWeights (α := Fin (s + 1)) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let wholeReference := fun x => allocatedSupportedWholeReference (dim := (s + 1)) B U b S (refined x)
    let idealLog := allocatedGenuineComparisonErrorLog m Psp Dgeom cgeom
      (coarseSpatialPartitionLog (allocatedProductCoarseInput m (s + 1) Psp pAccuracy w v (E + 2))) O E
    ∃ hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells V₀ z,
    ∃ hnormalizer : |Z - 1| ≤ Real.exp (-Qraw) ∧
      Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2,
    ∃ t : GoodKernel → ((Fin nX) → ℤ) → Fin Mk,
      (∀ x base, kernelPeriodCandidate (m + 1) (t x base) ≤ Mk ^ (m + 1)) ∧
    ∃ F : GoodKernel → ((Fin nX) → ℤ) →
        PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U b S) →
        AllocatedFiniteIdealData (Fin (s + 1)) I n,
      (∀ x base y₀, (F x base y₀).Bounds B U b S rowSets x.val y₀ (refined x) (d x)
        (kernelPeriodCandidate (m + 1) (t x base)) hb o bW hR δ (Real.exp (-idealLog))
        (allocatedFiniteIdealInputLog m Dgeom e idealLog) (layerKernelIndexBound m Mk)) ∧
      ∃ hresources : (∀ x base,
        let _ : ∀ (r : AllocatedPositiveResidue (dim := (s + 1)) B U b S (refined x))
            (a : {a // allocatedGridAxis (I := I) U b S.value a})
            (k : ((witnesses (index x) r).expansion a).Term),
            NeZero (((witnesses (index x) r).expansion a).period k) :=
          fun r a k => ⟨(hgridPeriod (index x) r a k).ne'⟩
        AllocatedCoarseFamilyResources (Kcov := Kcov) (τ := τ)
          B U b S (Fin nX) (modulus x) q (wholeReference x) (witnesses (index x))
          (d x) x.val hMk selection x.property N (kernelPeriodCandidate (m + 1) (t x base))
          (F x base) base (allocatedFiniteIdealInputLog m Dgeom e idealLog)
          Psp pAccuracy w v (E + 2) Dgeom O pc gc Pτ Z) ,
    let family : ∀ x : GoodKernel, ∀ base : Fin nX → ℤ,
        AllocatedCoarseSourceData (Kcov := Kcov) B U b S q N x.val hMk selection x.property τ base
          (allocatedFiniteIdealInputLog m Dgeom e idealLog)
          Psp pAccuracy w v (E + 2) Dgeom O pc gc Pτ Z :=
      fun x base => {
        modulus := modulus x
        modulusNonzero := ⟨(hmodulus x).ne'⟩
        refinedNonzero := ⟨(residueRefinedPeriod_pos (hmodulus x) q hq).ne'⟩
        denominator := d x
        denominatorNonzero := ⟨(hd x).ne'⟩
        period := kernelPeriodCandidate (m + 1) (t x base)
        periodNonzero := inferInstance
        reference := wholeReference x
        cover := witnesses (index x)
        gridPeriodNonzero := fun r a k => ⟨(hgridPeriod (index x) r a k).ne'⟩
        ideal := F x base
        resources := hresources x base }
    ∀ (f : (Fin nX → ℤ) → ℂ), (∀ u, ‖f u‖ ≤ 1) →
      ‖(allocatedOriginalPathLaw B U b hb o hR hσ S (Fin nX) poly hmem
          N hN hW hτ hξ q cells hmass bases _hbases hnormalizer.2.2.1).complexMean (fun z =>
            𝔼 cube : SupportedCube (s + 1)
                (integerBox (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)) :
                  Set (LayerSamplerVariables G I n B → ℤ)),
              physicalCubeSiteTest (integerSelfSiteTest (s + 1) f)
                (physicalCubeRootDifferences cube.val.2 cube.val.1 z.1.val z.2.val)) -
        (FiniteProbabilityWeights.pi (fun _ : G =>
          integerScalarCubeWeights (Fin (s + 1)) S.value S.positive)).goodPartBaseMean bases Good
          (fun x hx base => (family ⟨x, hx⟩ base).source hb o bW cells poly hmem V₀ f)‖ ≤
        2 * Real.exp (-E) + η

theorem allocatedCanonicalGenuineData_native
    {p g Psp E e pNum Pbase Qraw pAccuracy pSampling O : ℝ} (hP : 0 ≤ Psp)
    (δ : ℝ≥0) (A Kraw Ksite Kgen : ℕ)
    (witnesses : (q : AllocatedRefinedPeriodIndex m Psp) →
      (r : AllocatedPositiveResidue (dim := s + 1) B U b S (q.val : ℕ)) →
      AllocatedFullGridResidueWitness (dim := s + 1) B U b S (q.val : ℕ) r.val)
    (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin) (η : ℝ) (hη : 0 < η)
    (hData : AllocatedCanonicalGenuineData.{0,0,0,0,0,0} (dim := s + 1)
      B U b hR hσ S p g Psp E e pNum Pbase Qraw pAccuracy pSampling O hP δ
      A Kraw Ksite Kgen witnesses M Dwin hM hDwin η hη) :
    AllocatedCanonicalNativeData B U b hR hσ S p g Psp E e pNum Pbase Qraw pAccuracy pSampling O hP δ
      A Kraw Ksite Kgen witnesses M Dwin hM hDwin η hη := by
  unfold AllocatedCanonicalNativeData
  intro Dgeom cgeom pc gc Pτ
  obtain ⟨hgridPeriod, hData⟩ := hData
  refine ⟨hgridPeriod, ?_⟩
  intro w v Pfinal Mk hMk selection hqDim hcard _ hMkPsp hlarge hKgen hSampling
    Kernel Good GoodKernel
  obtain ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatial, hcoefficient, hData⟩ :=
    hData selection hqDim hcard hMkPsp hlarge hKgen hSampling
  let _ : ∀ x, NeZero (d x) := fun x => ⟨(hd x).ne'⟩
  let _ : ∀ x, NeZero (modulus x) := fun x => ⟨(hmodulus x).ne'⟩
  refine ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatial, hcoefficient, ?_⟩
  intro block _ _ _ _ _ _ hb o Kcov _ bW C V hC hV hCp hVp hCpAccuracy hVpAccuracy
    Cinv hCinv hchart hCgeom hCovEarly μ _ _ ν _ _ _ _ _ μsmall _ _ nX hXPsp q hq hqPsp
    refined index _ W hW indices ξ hξ mesh τ hτ Psamp sourceThreshold genuineThreshold threshold
    N hN hsize poly hpoly hmem rank hrank hRank cells hcells bases hbases hbaseBox
    V₀ Z law wholeReference idealLog
  have hResult := hData block hb o bW C V hC hV hCp hVp hCpAccuracy hVpAccuracy
    Cinv hCinv hchart hCgeom hCovEarly μ ν μsmall hXPsp q hq hqPsp
    N hN hsize poly hpoly hmem hrank hRank cells hcells bases hbases hbaseBox
  obtain ⟨hmass, hnormalizer, t, ht, F, hF, hresources, hcompare⟩ := hResult
  refine ⟨hmass, hnormalizer, t, ht, F, hF, hresources, ?_⟩
  intro family f hf
  exact (hcompare (integerSelfSiteTest (s + 1) f) (integerSelfSiteTest_norm_le (s + 1) f hf)).2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
local notation "rowTypes" => (fun j => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin (s + 1))))

def AllocatedUniversalCanonicalNativeSourceAt (p P E e t : ℝ) (hp : 0 ≤ p) (hP : 0 ≤ P)
    (δ : ℝ≥0) (A T Kproj Kideal Ksite Knorm Kgen : ℕ) : Prop :=
  ∀ {g : ℝ} (hg : 0 ≤ g),
    let hR := fun _ : Fin m => And.left (And.right (allocatedCommonProductRadius_bounds m hp hg))
    let cEarly := g + allocatedCommonProductRadiusLog m p g
    ∀ {cLate : ℝ} (_hcLate : 0 ≤ cLate), cEarly ≤ cLate →
    ∀ {J : Fin m → Type} [∀ j, Fintype (J j)]
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
      {σ : Fin m → ℝ} (hσ : ∀ j, 0 < σ j),
      (∀ j, σ j ≤ t) → (∀ j, (σ j)⁻¹ ≤ Real.exp cLate) →
      (∀ j, (Fintype.card (J j) : ℝ) ≤ 2 * p) →
    let Eraw := (E + 2) + 4
    let accuracy := allocatedOriginalCoverAccuracy P (E + 2)
    let D := allocatedComparisonDimension m p
    let pNum := allocatedCommonScaleNumeric m p cLate P Eraw
    let S := allocatedCommonScale (G := G) B U b hR hσ p cLate P e Eraw
    let pAccuracy := allocatedCommonRefinedSourceLog m p cEarly P e 0 accuracy
    let pSampling := allocatedCommonRefinedSourceLog m p cLate P e Eraw accuracy
    let w := allocatedSiteKernelMaskLog m P
    let v := allocatedIdealProfileLog m pAccuracy e
    let O := allocatedFullGridPrimitiveResourceLog m pAccuracy w v accuracy
    let tolerance := allocatedSitePrimitiveTolerance m pAccuracy w v accuracy
    let error := allocatedReferenceIdealError m D P Eraw
    let lengthLog := allocatedIdealScaleLog m D pNum e w error
    let gainLog := allocatedProfileGainLog m D P w
    let Pbase := allocatedIdealSourceBudget m D pNum e w error
    let lateLog := allocatedSpatialLateLog (G := G) B Pbase Pbase
    let rawFourier := allocatedProfileFourierOutput (allocatedActualProfileInput m D pNum e gainLog lengthLog)
    ∃ witnesses : (q : AllocatedRefinedPeriodIndex m P) →
        (r : AllocatedPositiveResidue (dim := (s + 1)) B U b S (q.val : ℕ)) →
        AllocatedFullGridResidueWitness (dim := (s + 1)) B U b S (q.val : ℕ) r.val,
      (∀ q r a, ((witnesses q r).expansion a).Bounds
        (Real.exp O) (Real.exp O) (Real.exp O) ⟨Real.exp O, Real.exp_nonneg _⟩
        (Real.exp (allocatedInactiveSupportLog (allocatedComparisonDimension m pAccuracy)))) ∧
      (∀ q r, AllocatedFullGridResidueSampling.{0,0,0,0,0,0}
        B U b hR hσ S (q.val : ℕ) (witnesses q r) tolerance) ∧
      ∀ (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin) (η : ℝ) (hη : 0 < η),
        AllocatedCanonicalNativeData
          B U b hR hσ S p g P E e pNum Pbase
          (allocatedSourceSamplingBudget m (s + 1) A Pbase (E + 2) lateLog rawFourier)
          pAccuracy pSampling O hP δ A (max T (max Kproj Kideal)) (max Ksite Knorm) Kgen
          witnesses M Dwin hM hDwin η hη

theorem AllocatedUniversalCanonicalSourceAt.to_native
    {p P E e t : ℝ} {hp : 0 ≤ p} {hP : 0 ≤ P} {δ : ℝ≥0}
    {A T Kproj Kideal Ksite Knorm Kgen : ℕ}
    (h : AllocatedUniversalCanonicalSourceAt.{0,0,0,0,0,0} (G := G) (dim := s + 1)
      B p P E e t hp hP δ A T Kproj Kideal Ksite Knorm Kgen) :
    AllocatedUniversalCanonicalNativeSourceAt (G := G) (s := s) B p P E e t hp hP δ A T Kproj Kideal Ksite Knorm Kgen := by
  intro g hg hR cEarly cLate hcLate hEarlyLate J _ U b σ hσ hσt hσi hJ
    Eraw accuracy D pNum S pAccuracy pSampling w v O tolerance error lengthLog gainLog Pbase lateLog rawFourier
  obtain ⟨witnesses, hBounds, hWitnesses, hData⟩ := h hg hcLate hEarlyLate U b hσ hσt hσi hJ
  refine ⟨witnesses, hBounds, hWitnesses, ?_⟩
  intro M Dwin hM hDwin η hη
  exact allocatedCanonicalGenuineData_native B U b hR hσ S hP δ A
    (max T (max Kproj Kideal)) (max Ksite Knorm) Kgen witnesses M Dwin hM hDwin η hη
    (hData M Dwin hM hDwin η hη)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]

noncomputable def allocatedCanonicalSmoothingLog (dim : ℕ) (p P E : ℝ) (A T : ℝ≥0) : ℝ :=
  physicalIdealSmoothingLog (B := B)
    (O := fun a : LayerSamplerAxis I n => BoundedBooleanJet (Fin dim) (a.1.val + 1))
    (α := Fin dim) (layerSamplerDegree I n) A T (profileReferenceErrorLog P ((E + 2) + 4))
    (allocatedProfileGainLog m (allocatedComparisonDimension m p) P ((m * 2 ^ (m + 1) : ℕ) * P))

noncomputable def allocatedCanonicalTailLog (dim : ℕ) (p P E : ℝ) (A T : ℝ≥0) : ℝ :=
  physicalIdealTailLog (B := B)
    (O := fun a : LayerSamplerAxis I n => BoundedBooleanJet (Fin dim) (a.1.val + 1))
    (α := Fin dim) G (G × Option (Fin dim)) (layerSamplerDegree I n) A T m
    (profileReferenceErrorLog P ((E + 2) + 4))
    (allocatedProfileGainLog m (allocatedComparisonDimension m p) P ((m * 2 ^ (m + 1) : ℕ) * P))

theorem AllocatedFlexibleCanonicalSourceAt.at_log_bounds
    {s : ℕ} {p P E e l : ℝ} {hp : 0 ≤ p} {hP : 0 ≤ P} {A T : ℝ≥0}
    {Ksite Knorm Kgen Kideal A₀ T₀ Kproj : ℕ}
    (h : AllocatedFlexibleCanonicalSourceAt.{0,0,0,0,0,0} (G := G) (dim := s + 1)
      B p P E hp hP A T Ksite Knorm Kgen Kideal A₀ T₀ Kproj)
    (he : allocatedCanonicalSmoothingLog B (s + 1) p P E A T ≤ e)
    (hl : allocatedCanonicalTailLog (G := G) B (s + 1) p P E A T ≤ l) :
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧ (δ : ℝ)⁻¹ ≤ Real.exp e ∧
      AllocatedUniversalCanonicalNativeSourceAt (G := G) (s := s)
        B p P E e (Real.exp (-l)) hp hP δ A₀ T₀ Kproj Kideal Ksite Knorm Kgen := by
  obtain ⟨_, _, δ, hδ, hδ1, _, hδe, ht, _, hti, hsource⟩ := h
  have ht' := hti.trans (Real.exp_le_exp.mpr hl)
  have hsmall := (inv_le_comm₀ ht (Real.exp_pos l)).mp ht'
  rw [← Real.exp_neg] at hsmall
  exact ⟨δ, hδ, hδ1, hδe.trans (Real.exp_le_exp.mpr he),
    AllocatedUniversalCanonicalSourceAt.to_native (G := G) (s := s) (hp := hp) (hP := hP) B
      (hsource e (Real.exp (-l)) he hsmall)⟩

theorem allocatedCanonicalSources_synchronize
    {p P E : ℝ} {hp : 0 ≤ p} {hP : 0 ≤ P} {A T : ℝ≥0}
    {Ksite Knorm Kgen Kideal A₀ T₀ Kproj : Fin (m + 1) → ℕ}
    (h : ∀ s : Fin (m + 1),
      AllocatedFlexibleCanonicalSourceAt.{0,0,0,0,0,0} (G := G) (dim := s.val + 1)
        B p P E hp hP A T (Ksite s) (Knorm s) (Kgen s) (Kideal s) (A₀ s) (T₀ s) (Kproj s)) :
    let e := ∑ s : Fin (m + 1), allocatedCanonicalSmoothingLog B (s.val + 1) p P E A T
    let l := ∑ s : Fin (m + 1), allocatedCanonicalTailLog (G := G) B (s.val + 1) p P E A T
    0 ≤ e ∧ 0 ≤ l ∧ 0 < Real.exp (-l) ∧ Real.exp (-l) ≤ 1 ∧
      ∃ δ : Fin (m + 1) → ℝ≥0, ∀ s : Fin (m + 1),
        0 < δ s ∧ δ s ≤ 1 ∧ (δ s : ℝ)⁻¹ ≤ Real.exp e ∧
        AllocatedUniversalCanonicalNativeSourceAt (G := G) (s := s.val)
          B p P E e (Real.exp (-l)) hp hP (δ s)
          (A₀ s) (T₀ s) (Kproj s) (Kideal s) (Ksite s) (Knorm s) (Kgen s) := by
  intro e l
  have hlogs (s : Fin (m + 1)) :
      0 ≤ allocatedCanonicalSmoothingLog B (s.val + 1) p P E A T ∧
      0 ≤ allocatedCanonicalTailLog (G := G) B (s.val + 1) p P E A T :=
    ⟨(h s).1, (h s).2.1⟩
  have he : 0 ≤ e := Finset.sum_nonneg (fun s _ => (hlogs s).1)
  have hl : 0 ≤ l := Finset.sum_nonneg (fun s _ => (hlogs s).2)
  refine ⟨he, hl, Real.exp_pos _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hl), ?_⟩
  have hs (s : Fin (m + 1)) := (h s).at_log_bounds B
    (Finset.single_le_sum (fun i _ => (hlogs i).1) (Finset.mem_univ s))
    (Finset.single_le_sum (fun i _ => (hlogs i).2) (Finset.mem_univ s))
  choose δ hδ hδ1 hδe hsource using hs
  exact ⟨δ, fun s => ⟨hδ s, hδ1 s, hδe s, hsource s⟩⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin (s + 1)) (Fin.val j + 1))
local notation "hLayer" => layerSamplerDegree I n
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
local notation "rowTypes" => (fun j => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin (s + 1))))

def AllocatedInitializedCanonicalNativeSourceAt (p P E : ℝ) (hp : 0 ≤ p) (hP : 0 ≤ P)
    (A T : ℝ≥0) (Ksite Knorm Kgen Kideal A₀ T₀ Kproj : ℕ) : Prop :=
  let D := allocatedComparisonDimension m p
  let target := profileReferenceErrorLog P ((E + 2) + 4)
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * P
  let gainLog := allocatedProfileGainLog m D P w
  let ε := physicalIdealErrorShare target gainLog
  let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
    (α := Fin (s + 1)) hLayer A T target gainLog
  let eTail := physicalIdealTailLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
    (α := Fin (s + 1)) G (G × Option (Fin (s + 1))) hLayer A T m target gainLog
  0 ≤ e ∧ 0 ≤ eTail ∧
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      (δ : ℝ) = booleanRegularizationRadius (B := B)
        (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin (s + 1)) hLayer
        (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
        A T (ε / 2) ∧ (δ : ℝ)⁻¹ ≤ Real.exp e ∧
      let t := booleanMassPerturbationScale (B := B)
        (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin (s + 1))
        ((G × Option (Fin (s + 1))) ⊕ (Σ a, SamplerCoefficientSlot G B hLayer a)) hLayer
        (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
        A T m 1 (ε / 2)
      0 < t ∧ t ≤ 1 ∧ t⁻¹ ≤ Real.exp eTail ∧
          AllocatedUniversalCanonicalNativeSourceAt
            (G := G) (s := s) B p P E e t hp hP δ A₀ T₀ Kproj Kideal Ksite Knorm Kgen

theorem AllocatedInitializedCanonicalSourceAt.to_native
    {p P E : ℝ} {hp : 0 ≤ p} {hP : 0 ≤ P} {A T : ℝ≥0}
    {Ksite Knorm Kgen Kideal A₀ T₀ Kproj : ℕ}
    (h : AllocatedInitializedCanonicalSourceAt.{0,0,0,0,0,0}
      (G := G) (dim := s + 1) B p P E hp hP A T Ksite Knorm Kgen Kideal A₀ T₀ Kproj) :
    AllocatedInitializedCanonicalNativeSourceAt
      (G := G) (s := s) B p P E hp hP A T Ksite Knorm Kgen Kideal A₀ T₀ Kproj := by
  unfold AllocatedInitializedCanonicalNativeSourceAt
  intro D target w gainLog ε e eTail
  obtain ⟨he, heTail, δ, hδ, hδ1, hδeq, hδe, ht, ht1, hti, hsource⟩ := h
  exact ⟨he, heTail, δ, hδ, hδ1, hδeq, hδe, ht, ht1, hti, hsource.to_native B⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq

theorem exists_prepared_common_canonical_sources :
    ∃ A T : ℝ≥0, 1 ≤ A ∧ 1 ≤ T ∧ ∀ m : ℕ,
      ∃ Ksite Knorm Kgen Kideal A₀ T₀ Kproj : Fin (m + 1) → ℕ,
        (∀ s, 2 ≤ Ksite s ∧ 2 ≤ Knorm s ∧ 2 ≤ Kgen s ∧
          2 ≤ Kideal s ∧ 2 ≤ A₀ s ∧ 2 ≤ T₀ s ∧ 2 ≤ Kproj s) ∧
        (∀ s : Fin (m + 1),
          PhysicalAmbientRowsKernelSampling.{0,0,0} m (s.val + 1) (Kgen s)
            (fun j => (boundedBooleanJetRows (Fin (s.val + 1)) (j.val + 1) : Type))
            (fun _ => Subtype.val)) ∧
        ∀ {X J : Type} (L : RankPreparationFamily X J m) {M : ℕ},
          (∀ j, Fintype.card (L j).Coord ≤ M) →
          let p : ℝ := preparedCommonSamplerDimension m M
          ∀ {P E : ℝ} (hP : 0 ≤ P), 0 ≤ E →
            ((m + 2 : ℕ) : ℝ) ≤ P → allocatedComparisonDimension m p ≤ P →
          let e := ∑ s : Fin (m + 1),
            allocatedCanonicalSmoothingLog (PreparedCommonSamplerBlock L) (s.val + 1) p P E A T
          let l := ∑ s : Fin (m + 1),
            allocatedCanonicalTailLog (G := PreparedCommonKernel m)
              (PreparedCommonSamplerBlock L) (s.val + 1) p P E A T
          0 ≤ e ∧ 0 ≤ l ∧ 0 < Real.exp (-l) ∧ Real.exp (-l) ≤ 1 ∧
            ∃ δ : Fin (m + 1) → ℝ≥0, ∀ s : Fin (m + 1),
              0 < δ s ∧ δ s ≤ 1 ∧ (δ s : ℝ)⁻¹ ≤ Real.exp e ∧
              AllocatedUniversalCanonicalNativeSourceAt (G := PreparedCommonKernel m) (s := s.val)
                (PreparedCommonSamplerBlock L) p P E e (Real.exp (-l)) (Nat.cast_nonneg _) hP (δ s)
                (A₀ s) (T₀ s) (Kproj s) (Kideal s) (Ksite s) (Knorm s) (Kgen s) := by
  obtain ⟨A, T, hA, hT, hsource⟩ :=
    exists_uniform_flexible_canonical_sources.{0,0,0,0,0,0}
  refine ⟨A, T, hA, hT, ?_⟩
  intro m
  have hs (s : Fin (m + 1)) := hsource m (s.val + 1)
  choose Ksite Knorm Kgen Kideal A₀ T₀ Kproj
    hKsite hKnorm hKgen hKideal hA₀ hT₀ hKproj hgen hSources using hs
  refine ⟨Ksite, Knorm, Kgen, Kideal, A₀, T₀, Kproj,
    (fun s => ⟨hKsite s, hKnorm s, hKgen s, hKideal s, hA₀ s, hT₀ s, hKproj s⟩), hgen, ?_⟩
  intro X J L M hM p P E hP hE hmP hDP
  apply allocatedCanonicalSources_synchronize (PreparedCommonSamplerBlock L)
  intro s
  obtain ⟨hvars, hI, hn⟩ := preparedCommonSampler_dimensions L hM
  apply hSources s (PreparedCommonSamplerBlock L) (Nat.cast_nonneg _) hP hE
    (Nat.succ_le_of_lt s.isLt) hmP hDP
  · exact_mod_cast hvars
  · intro j; exact_mod_cast hI j
  · intro j; exact_mod_cast hn j
  · intro j i
    simpa only [PreparedCommonSamplerBlock, Fintype.card_fin] using
      preparedCommonBlockCount_spectrum m j s

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped Classical NNReal

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq

theorem exists_prepared_canonical_native_sources :
    ∃ A T : ℝ≥0, 1 ≤ A ∧ 1 ≤ T ∧ ∀ m s : ℕ,
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)
      ∃ Ksite Knorm Kgen Kideal A₀ T₀ Kproj : ℕ,
        2 ≤ Ksite ∧ 2 ≤ Knorm ∧ 2 ≤ Kgen ∧
        2 ≤ Kideal ∧ 2 ≤ A₀ ∧ 2 ≤ T₀ ∧ 2 ≤ Kproj ∧
        PhysicalAmbientRowsKernelSampling.{0,0,0} m (s + 1) Kgen
          (fun j => (rowSets j : Type)) (fun _ => Subtype.val) ∧
        ∀ {X J : Type} (L : RankPreparationFamily X J m) {M : ℕ},
          (∀ j, Fintype.card (L j).Coord ≤ M) →
          let p : ℝ := preparedSamplerDimension m (s + 1) M
          ∀ {P E : ℝ} (hP : 0 ≤ P), 0 ≤ E → s + 1 ≤ m + 1 →
            ((m + 2 : ℕ) : ℝ) ≤ P → allocatedComparisonDimension m p ≤ P →
            AllocatedInitializedCanonicalNativeSourceAt
              (G := Fin ((s + 1) * ((s + 1) + 2))) (s := s)
              (PreparedSamplerBlock L (s + 1)) p P E (Nat.cast_nonneg _) hP
              A T Ksite Knorm Kgen Kideal A₀ T₀ Kproj := by
  obtain ⟨A, T, hA, hT, hsource⟩ := exists_prepared_canonical_sources
  refine ⟨A, T, hA, hT, ?_⟩
  intro m s rowSets
  obtain ⟨Ksite, Knorm, Kgen, Kideal, A₀, T₀, Kproj,
    hKsite, hKnorm, hKgen, hKideal, hA₀, hT₀, hKproj, hgen, hs⟩ := hsource m (s + 1)
  refine ⟨Ksite, Knorm, Kgen, Kideal, A₀, T₀, Kproj,
    hKsite, hKnorm, hKgen, hKideal, hA₀, hT₀, hKproj, hgen, ?_⟩
  intro X J L M hM p P E hP hE hdim hmP hDP
  exact (hs L hM hP hE hdim hmP hDP).to_native (PreparedSamplerBlock L (s + 1))

end Erdos3.VectorPolynomial

end

end OAI

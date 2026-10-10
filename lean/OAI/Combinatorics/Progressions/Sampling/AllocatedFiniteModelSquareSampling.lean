import OAI.Combinatorics.Progressions.Estimates.AllocatedModelCoefficientCover
import OAI.Combinatorics.Progressions.Estimates.CoefficientSignedExpansion
import OAI.Combinatorics.Progressions.Estimates.CoefficientUniformSmallError
import OAI.Combinatorics.Progressions.Probability.ReferenceJetPositiveMass

namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

abbrev physicalModelRows (m q : ℕ) (j : Fin m) :=
  {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (j.val + 1)}

abbrev physicalModelRowSets (m q : ℕ) :=
  fun j : Fin m => (Subtype.val : physicalModelRows m q j → Finset (Fin q))

def PhysicalModelSquareSampling (m A : ℕ) : Prop :=
    ∀ {X : Type*} [Fintype X] [DecidableEq X] {q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P target : ℝ}, 0 ≤ P → 0 ≤ target → (Fintype.card X : ℝ) ≤ P →
    (Fintype.card (Option (Fin q) × X) : ℝ) ≤ P →
    (Fintype.card (CoefficientAmbientIndex (Fin q) J) : ℝ) ≤ P →
    ∀ (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := Fin q) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin q) U)] [BorelSpace (CoefficientTorus (K := Fin q) U)]
    (μ : Measure (CoefficientTorus (K := Fin q) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
    (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j)) →
    ∀ (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (d : ℕ), 0 < d → (d : ℝ) ≤ Real.exp P →
    ∀ (stride : X → ℕ), (∀ x, 0 < stride x) → (∀ x, (stride x : ℝ) ≤ Real.exp P) →
    ∀ {R ρ : ℝ}, 0 < ρ → 1 / ρ ≤ Real.exp P →
    ∀ (H : X → ℝ), (∀ x, Real.exp ((P + target + A) ^ A) ≤ H x) →
    (∀ j, HasLayerSamplingRank (j.val + 1) H R (U j) (p j)) →
    Real.exp ((P + target + A) ^ A) ≤ R →
    ∀ (G : Finset (ColumnResiduePattern (Option (Fin q)) X stride)), G.Nonempty →
    ∀ (V : Option (Fin q) × X → ℝ) (_hV : ∀ z, 0 < V z), (∀ z, ρ * H z.2 ≤ V z) →
    (0 < ∑' z, selectedResidueSmoothWeight stride G V z) →
    ∀ {F T : Type*} [Fintype F] [Fintype T]
    (period : T → ℕ), (∀ t, 0 < period t) → (∀ t, (period t : ℝ) ≤ Real.exp P) →
    ∀ (c : F → ℂ) (a : T → ℂ)
    (f : F → (CoefficientAmbientIndex (Fin q) J → UnitAddCircle) → ℂ)
    (g : T → (CoefficientAmbientIndex (Fin q) J → UnitAddCircle) → ℂ)
    (Lf : F → ℝ≥0) (Lg : T → ℝ≥0),
    (∀ t, LipschitzWith (Lf t) (f t)) → (∀ t z, ‖f t z‖ ≤ 1) →
    (∀ t, (Lf t : ℝ) ≤ Real.exp P) →
    (∀ t, LipschitzWith (Lg t) (g t)) → (∀ t z, ‖g t z‖ ≤ 1) →
    (∀ t, (Lg t : ℝ) ≤ Real.exp P) →
    (∑ t, ‖c t‖) + (∑ t, ‖a t‖) ≤ Real.exp P →
    ∀ (density model : EuclideanJetLayers U (physicalModelRows m q) → ℂ),
    Measurable density → Measurable model →
    Integrable (fun y => ‖density y - model y‖ ^ 2)
      (Measure.pi (fun j => Measure.pi (fun _ : physicalModelRows m q j => ν j))) →
    (∫ y, ‖density y - model y‖ ^ 2
      ∂Measure.pi (fun j => Measure.pi (fun _ : physicalModelRows m q j => ν j))) ≤ Real.exp (-(target + 20)) →
    (∀ z : CoefficientTorus (K := Fin q) U,
      ‖density (euclideanCoefficientJetMap U (fun _ => 0) (1 : Matrix (Fin q) (Fin q) ℤ) (physicalModelRowSets m q) z) -
        ∑ t, c t * f t (coefficientAmbientTorus U z)‖ ≤ Real.exp (-(target + 20))) →
    (∀ (p' : ∀ j, VectorPolynomial (Fin q) ℝ (J j → ℝ)),
      (∀ j, DegreeLE (1 : Fin q → ℕ) (j.val + 1) (p' j)) →
      ∀ (hm' : ∀ j e, coefficients (p' j) e ∈ U j) (v : Fin q → (Unit ⊕ Fin q) → ℤ),
      model (physicalCubeRowSample U d (physicalModelRowSets m q) p' hm' v) =
        ∑ t, a t * g t (coefficientAmbientTorus U (affineCoefficientCoverSample U p' hm' (period t)
          (fun k x => (standardPhysicalCubeFrame v (k,x) : ℝ))))) →
    (∀ v : X → (Unit ⊕ Fin q) → ℤ,
      model (physicalCubeRowSample U d (physicalModelRowSets m q) p hm v) =
        ∑ t, a t * g t (coefficientAmbientTorus U (affineCoefficientCoverSample U p hm (period t)
          (fun k x => (standardPhysicalCubeFrame v (k,x) : ℝ))))) →
    selectedResidueDensityMass stride G V (fun z =>
      ‖density (physicalCubeRowSample U d (physicalModelRowSets m q) p hm (standardPhysicalCubeOutput z)) -
        model (physicalCubeRowSample U d (physicalModelRowSets m q) p hm (standardPhysicalCubeOutput z))‖ ^ 2) ≤
      Real.exp (-target)

theorem exists_physical_model_square_sampling (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ PhysicalModelSquareSampling m A := by
  obtain ⟨A, hA, hsample⟩ := exists_coefficient_uniform_small_error m
  refine ⟨A, hA, ?_⟩
  intro X _ _ q J _ P target hP ht hn hdim hamb U _ _ _ μ _ _ ν _ _ p hp hm
    d hd hdP stride hs hsP R ρ hρ hρP H hH hrank hR G hG V hV hwidth hZ
    F T _ _ period hperiod hperiodP c a f g Lf Lg hf hfb hfP hg hgb hgP hmass
    density model hden hmod hint hL2 happ hmodel hphysical
  let periods : F ⊕ T → ℕ := Sum.elim (fun _ => d) period
  have hperiods : ∀ t, 0 < periods t := Sum.rec (fun _ => hd) hperiod
  obtain ⟨D, hD, hdD, hdiv⟩ := exists_finite_pair_common_cover_with_base d hd periods hperiods
  have hterm (t : T) : period t ∣ D :=
    (dvd_mul_right (period t) (period t)).trans (hdiv (.inr t) (.inr t))
  have hratio : 0 < D / d := Nat.div_pos (Nat.le_of_dvd hD hdD) hd
  let jet := euclideanCoefficientJetMap U (fun _ => 0) (1 : Matrix (Fin q) (Fin q) ℤ) (physicalModelRowSets m q)
  let reference := fun z => density (jet (quotientIntegerCover (coefficientIntegerLattice U) (D / d) z)) -
    model (jet (quotientIntegerCover (coefficientIntegerLattice U) (D / d) z))
  have hmp := physicalRowsCoefficient_measurePreserving U μ ν (D / d) hratio
  have hmp' : MeasurePreserving (fun z => jet (quotientIntegerCover (coefficientIntegerLattice U) (D / d) z))
      μ (Measure.pi (fun j => Measure.pi (fun _ : physicalModelRows m q j => ν j))) := by
    convert hmp using 1
  have hi : Integrable (fun z => ‖reference z‖ ^ 2) μ := by
    have hh := hmp'.integrable_comp_of_integrable hint
    convert hh using 1
    congr! (transparency := .reducible)
  have he : (∫ z, ‖reference z‖ ^ 2 ∂μ) ≤ Real.exp (-(target + 20)) := by
    change (∫ z, ‖density (jet (quotientIntegerCover (coefficientIntegerLattice U) (D / d) z)) -
      model (jet (quotientIntegerCover (coefficientIntegerLattice U) (D / d) z))‖ ^ 2 ∂μ) ≤ _
    rw [physicalRowsCoefficient_square_integral U μ ν (D / d) hratio density model hden hmod]
    convert hL2 using 1
    congr! (transparency := .reducible)
  apply hsample hP ht hn hdim hamb U μ p hp hm periods hperiods
    (Sum.rec (fun _ => hdP) hperiodP) D hD hdiv stride hs hsP hρ hρP H hH hrank hR
    G hG V hV hwidth hZ (signedExpansionCoefficients c a) (Sum.elim f g) (Sum.elim Lf Lg)
    (Sum.rec hf hg) (Sum.rec hfb hgb) (Sum.rec hfP hgP)
    (by simpa only [signedExpansion_mass] using hmass) _ reference hi he
  · intro z
    have hh := coefficient_physical_difference_approximation U (physicalModelRowSets m q) d p hp hm
      period c a f g density model happ hphysical (standardPhysicalCubeOutput z)
    have hframe : standardPhysicalCubeFrame (standardPhysicalCubeOutput z) = z := by
      funext ⟨k, x⟩
      cases k <;> rfl
    simpa only [hframe] using hh
  · exact coefficient_polynomial_difference_approximation U (physicalModelRowSets m q) d D hD hdD
      period hterm c a f g density model happ hmodel

noncomputable def physicalModelSamplingExponent.{uX, uJ, uF, uT} (m : ℕ) : ℕ :=
  (exists_physical_model_square_sampling.{uX, uJ, uF, uT} m).choose

theorem physicalModelSamplingExponent_spec.{uX, uJ, uF, uT} (m : ℕ) :
    2 ≤ physicalModelSamplingExponent.{uX, uJ, uF, uT} m ∧
      PhysicalModelSquareSampling.{uX, uJ, uF, uT} m (physicalModelSamplingExponent.{uX, uJ, uF, uT} m) :=
  (exists_physical_model_square_sampling.{uX, uJ, uF, uT} m).choose_spec

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial
universe uG uI uB uJ uE uT uF

open Module Submodule _root_.Set _root_.OAI.Set MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type uE} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "mask" => allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

theorem allocated_finite_model_square_sampling
    (hdiv : period ∣ d) (hR : ∀ j, 0 < R j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin dim)) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    {T : Type uT} [Fintype T] (a : T → ℂ)
    (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : ∀ k s, LipschitzWith L (f k s)) (hf1 : ∀ k s z, ‖f k s z‖ ≤ 1)
    {Nt V Cc Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (Q : ℝ≥0) (hQ : ∀ a, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2) : ℝ) + 1) ≤ Q)

    {A : ℕ} (hSampling : PhysicalModelSquareSampling.{0, uJ, uF, max uE uT uI} m A)
    {X : Type} [Fintype X] [DecidableEq X]
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j ex, coefficients (p j) ex ∈ U j)
    {P target : ℝ} (hP : 0 ≤ P) (htarget : 0 ≤ target)
    (hn : (Fintype.card X : ℝ) ≤ P)
    (hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    (hamb : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ P)
    (hdP : (d : ℝ) ≤ Real.exp P)
    (stride : X → ℕ) (hs : ∀ t, 0 < stride t) (hsP : ∀ t, (stride t : ℝ) ≤ Real.exp P)
    {Rrank ρ : ℝ} (hρ : 0 < ρ) (hρP : 1 / ρ ≤ Real.exp P)
    (H : X → ℝ) (hH : ∀ t, Real.exp ((P + target + A) ^ A) ≤ H t)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rrank (U j) (p j))
    (hRank : Real.exp ((P + target + A) ^ A) ≤ Rrank)
    (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride)) (hcells : cells.Nonempty)
    (widths : Option (Fin dim) × X → ℝ) (hwidths : ∀ z, 0 < widths z)
    (hwidth : ∀ z, ρ * H z.2 ≤ widths z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
    {F : Type uF} [Fintype F] (c : F → ℂ)
    (factor : F → (CoefficientAmbientIndex (Fin dim) J → UnitAddCircle) → ℂ)
    (Lf : F → ℝ≥0) (hfactor : ∀ t, LipschitzWith (Lf t) (factor t))
    (hfactorb : ∀ t z, ‖factor t z‖ ≤ 1) (hLf : ∀ t, (Lf t : ℝ) ≤ Real.exp P)
    (density : EuclideanJetLayers U rowTypes → ℂ) (hden : Measurable density) :
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Llong := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord +
      max (L * Lcoord * period) (4 * period)
    let Lgrid := fun k => max (((Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} * Lg) * Q) *
      Lcoord * commonSitePeriod e k) (4 * commonSitePeriod e k)
    let model := fun y => allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y *
      allocatedFullGridChartModel B U b S rowSets d hb o bW e y
    (∀ k, (period * commonSitePeriod e k : ℕ) ≤ Real.exp P) →
    (∀ k, ((Fintype.card (Finset (Fin dim)) * ((Llong + Lgrid k) * (period * commonSitePeriod e k) *
      ((∑ j : Fin m, ((rowSets j).card : ℝ≥0)) *
        ∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0))) : ℝ≥0) : ℝ) ≤ Real.exp P) →
    (∑ t, ‖c t‖) + (∑ label : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))), ∑ i, ∑ k,
      ‖(((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
          coverSiteCoefficient e k)‖) ≤ Real.exp P →
    Measurable model →
    Integrable (fun y => ‖density y - model y‖ ^ 2)
      (Measure.pi (fun j => Measure.pi (fun _ : rowTypes j => ν j))) →
    (∫ y, ‖density y - model y‖ ^ 2
      ∂Measure.pi (fun j => Measure.pi (fun _ : rowTypes j => ν j))) ≤ Real.exp (-(target + 20)) →
    (∀ z : CoefficientTorus (K := Fin dim) U,
      ‖density (euclideanCoefficientJetMap U (fun _ => 0) (1 : Matrix (Fin dim) (Fin dim) ℤ) rows z) -
        ∑ t, c t * factor t (coefficientAmbientTorus U z)‖ ≤ Real.exp (-(target + 20))) →
    selectedResidueDensityMass stride cells widths (fun z =>
      ‖density (physicalCubeRowSample U d rows p hm (standardPhysicalCubeOutput z)) -
        model (physicalCubeRowSample U d rows p hm (standardPhysicalCubeOutput z))‖ ^ 2) ≤ Real.exp (-target) := by
  intro Lcoord Llong Lgrid model hperiodP htermLip hmass hmod hint hL2 happ
  obtain ⟨g, hg, hgb, hid⟩ := exists_allocated_finite_model_polynomial_uniform_expansion
    B U b S x y₀ q d period r hr hb o bW e hdiv hR C hC hchart hbudget
    Cforward hforward K hK a f hf hf1 he Q hQ
  have hgrid (k) : 0 < commonSitePeriod e k := by
    exact commonSitePeriod_pos e he k
  let terms := (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) × T × (∀ a, (e a).Term)
  let coeff := fun t : terms =>
    (((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
      allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a t.1 t.2.1) *
        coverSiteCoefficient e t.2.2)
  let factors := fun t : terms => coefficientAmbientModelTerm period (commonSitePeriod e t.2.2) (g t.1 t.2.1 t.2.2)
  let Lt := fun t : terms => Fintype.card (Finset (Fin dim)) * ((Llong + Lgrid t.2.2) *
    (period * commonSitePeriod e t.2.2) * ((∑ j : Fin m, ((rowSets j).card : ℝ≥0)) *
      ∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0)))
  have ht (t : terms) : (∀ z, ‖factors t z‖ ≤ 1) ∧ LipschitzWith (Lt t) (factors t) := by
    let : NeZero (commonSitePeriod e t.2.2) := ⟨(hgrid t.2.2).ne'⟩
    exact coefficientAmbientModelTerm_bounds period (commonSitePeriod e t.2.2) (g t.1 t.2.1 t.2.2)
      (hg t.1 t.2.1 t.2.2) (hgb t.1 t.2.1 t.2.2)
  have hidentity {Y : Type} (p' : ∀ j, VectorPolynomial Y ℝ (J j → ℝ))
      (hp' : ∀ j, DegreeLE (1 : Y → ℕ) (j.val + 1) (p' j))
      (hm' : ∀ j ex, coefficients (p' j) ex ∈ U j) (v : Y → (Unit ⊕ Fin dim) → ℤ) :
      model (physicalCubeRowSample U d rows p' hm' v) =
        ∑ t : terms, coeff t * factors t (coefficientAmbientTorus U
          (affineCoefficientCoverSample U p' hm' (period * commonSitePeriod e t.2.2)
            (fun k x => (standardPhysicalCubeFrame v (k,x) : ℝ)))) := by
    have hh := AllocatedModelPhysicalExpansionIdentity.coefficient_sample
      B U b S x y₀ q d period r hr hb o bW e a f p' hp' hm' g (hid p' hp' hm') hgrid v
    simpa only [terms, coeff, factors, model, Fintype.sum_prod_type] using hh
  exact hSampling (X := X) (q := dim) (J := J) (F := F) (T := terms) hP htarget hn hdim hamb U μ ν p hp hm d (NeZero.pos d) hdP
    stride hs hsP hρ hρP H hH hrank hRank cells hcells widths hwidths hwidth hZ
    (fun t : terms => period * commonSitePeriod e t.2.2)
    (fun t => Nat.mul_pos (NeZero.pos period) (hgrid t.2.2)) (fun t => hperiodP t.2.2)
    c coeff factor factors Lf Lt hfactor hfactorb hLf
    (fun t => (ht t).2) (fun t => (ht t).1) (fun t => htermLip t.2.2)
    (by simpa only [terms, coeff, Fintype.sum_prod_type] using hmass)
    density model hden hmod
    (by convert hint using 1)
    (by convert hL2 using 1; congr! (transparency := .reducible)) happ
    (fun p' hp' hm' => hidentity p' hp' hm') (hidentity p hp hm)

theorem allocated_finite_model_reference_sample
    (hdiv : period ∣ d) (hR : ∀ j, 0 < R j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin dim)) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    {T : Type uT} [Fintype T] (a : T → ℂ)
    (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : ∀ k s, LipschitzWith L (f k s)) (hf1 : ∀ k s z, ‖f k s z‖ ≤ 1)
    {Nt V Cc Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (Q : ℝ≥0) (hQ : ∀ a, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2) : ℝ) + 1) ≤ Q)

    {A : ℕ} (hSampling : PhysicalModelSquareSampling.{0, uJ, uF, max uE uT uI} m A)
    {X : Type} [Fintype X] [DecidableEq X]
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j ex, coefficients (p j) ex ∈ U j)
    {P target : ℝ} (hP : 0 ≤ P) (htarget : 0 ≤ target)
    (hn : (Fintype.card X : ℝ) ≤ P)
    (hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    (hamb : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ P)
    (hdP : (d : ℝ) ≤ Real.exp P)
    (stride : X → ℕ) (hs : ∀ t, 0 < stride t) (hsP : ∀ t, (stride t : ℝ) ≤ Real.exp P)
    {Rrank ρ : ℝ} (hρ : 0 < ρ) (hρP : 1 / ρ ≤ Real.exp P)
    (H : X → ℝ) (hH : ∀ t, Real.exp ((P + target + A) ^ A) ≤ H t)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rrank (U j) (p j))
    (hRank : Real.exp ((P + target + A) ^ A) ≤ Rrank)
    (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride)) (hcells : cells.Nonempty)
    (Hwindow : X → ℝ) (hHwindow : ∀ t, 1 ≤ Hwindow t)
    (hwidth : ∀ z : Option (Fin dim) × X, ρ * H z.2 ≤ referenceJetEnvelopeWidths stride Hwindow z)
    (base : X → ℤ)
    {F : Type uF} [Fintype F] (c : F → ℂ)
    (factor : F → (CoefficientAmbientIndex (Fin dim) J → UnitAddCircle) → ℂ)
    (Lf : F → ℝ≥0) (hfactor : ∀ t, LipschitzWith (Lf t) (factor t))
    (hfactorb : ∀ t z, ‖factor t z‖ ≤ 1) (hLf : ∀ t, (Lf t : ℝ) ≤ Real.exp P)
    (density : EuclideanJetLayers U rowTypes → ℂ) (hden : Measurable density) :
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Llong := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord +
      max (L * Lcoord * period) (4 * period)
    let Lgrid := fun k => max (((Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} * Lg) * Q) *
      Lcoord * commonSitePeriod e k) (4 * commonSitePeriod e k)
    let model := fun y => allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y *
      allocatedFullGridChartModel B U b S rowSets d hb o bW e y
    (∀ k, (period * commonSitePeriod e k : ℕ) ≤ Real.exp P) →
    (∀ k, ((Fintype.card (Finset (Fin dim)) * ((Llong + Lgrid k) * (period * commonSitePeriod e k) *
      ((∑ j : Fin m, ((rowSets j).card : ℝ≥0)) *
        ∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0))) : ℝ≥0) : ℝ) ≤ Real.exp P) →
    (∑ t, ‖c t‖) + (∑ label : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))), ∑ i, ∑ k,
      ‖(((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
          coverSiteCoefficient e k)‖) ≤ Real.exp P →
    Measurable model →
    Integrable (fun y => ‖density y - model y‖ ^ 2)
      (Measure.pi (fun j => Measure.pi (fun _ : rowTypes j => ν j))) →
    (∫ y, ‖density y - model y‖ ^ 2
      ∂Measure.pi (fun j => Measure.pi (fun _ : rowTypes j => ν j))) ≤ Real.exp (-(target + 20)) →
    (∀ z : CoefficientTorus (K := Fin dim) U,
      ‖density (euclideanCoefficientJetMap U (fun _ => 0) (1 : Matrix (Fin dim) (Fin dim) ℤ) rows z) -
        ∑ t, c t * factor t (coefficientAmbientTorus U z)‖ ≤ Real.exp (-(target + 20))) →
    (0 < ∑' z, selectedResidueSmoothWeight stride cells (referenceJetEnvelopeWidths stride Hwindow) z) ∧
    selectedResidueDensityMass stride cells (referenceJetEnvelopeWidths stride Hwindow) (fun z =>
      ‖density (physicalCubeRowSample U d rows p hm (translatePhysicalCube base (standardPhysicalCubeOutput z))) -
        model (physicalCubeRowSample U d rows p hm (translatePhysicalCube base (standardPhysicalCubeOutput z)))‖ ^ 2) ≤ Real.exp (-target) := by
  intro Lcoord Llong Lgrid model hperiodP htermLip hmass hmod hint hL2 happ
  have hZ := referenceJetEnvelope_mass_pos stride hs Hwindow hHwindow cells hcells
  refine ⟨hZ, ?_⟩
  let p₀ := fun j => translate (fun x => (base x : ℝ)) (p j)
  have hp₀ (j) : DegreeLE (1 : X → ℕ) (j.val + 1) (p₀ j) :=
    degreeLE_translate (1 : X → ℕ) (fun _ => by norm_num) _ (p j) (hp j)
  have hm₀ (j ex) : coefficients (p₀ j) ex ∈ U j :=
    coefficients_translate_mem (U j) (fun x => (base x : ℝ)) (p j) (hm j) ex
  have hrank₀ (j) : HasLayerSamplingRank (j.val + 1) H Rrank (U j) (p₀ j) :=
    (hasLayerSamplingRank_translate_iff _ _ H Rrank (U j) (p j) (hp j)).mpr (hrank j)
  have hh := allocated_finite_model_square_sampling B U b S x y₀ q d period r hr hb o bW e
    hdiv hR C hC hchart hbudget Cforward hforward K hK a f hf hf1 he Q hQ
    hSampling μ ν p₀ hp₀ hm₀ hP htarget hn hdim hamb hdP stride hs hsP hρ hρP H hH hrank₀ hRank
    cells hcells (referenceJetEnvelopeWidths stride Hwindow)
    (referenceJetEnvelopeWidths_pos stride hs Hwindow (fun t => lt_of_lt_of_le zero_lt_one (hHwindow t)))
    hwidth hZ c factor Lf hfactor hfactorb hLf density hden
    hperiodP htermLip hmass hmod hint hL2 happ
  dsimp only [p₀] at hh
  simp_rw [physicalCubeRowSample_translate U d rows p hm base] at hh
  exact hh

end Erdos3.VectorPolynomial

end

end OAI

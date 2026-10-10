import OAI.Combinatorics.Progressions.Linear.AllocatedAveragedCoarseKernelComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory Polynomial
open scoped BigOperators Classical NNReal

universe uX

def allocatedAveragedKernelStatement (m dim : ℕ) : Prop :=
    ∃ A a : ℕ, 2 ≤ A ∧ 2 ≤ a ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    [Nonempty (Fin dim)]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ v, Fintype (B v)] [∀ v, DecidableEq (B v)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {p Etarget T : ℝ} (_hp : 0 ≤ p) (_hE : 0 ≤ Etarget) (_hT : 0 ≤ T)
    (_hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (_hn : ∀ j, (n j : ℝ) ≤ p)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (_hRup : ∀ j, R j ≤ Real.exp p) (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p)
    (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp p) (_hmsp : ((m + 2 : ℕ) : ℝ) ≤ p),
    let E := Etarget + 1
    let Q := allocatedKernelPrimitiveBudget p E T
    let S := allocatedKernelScale (G := G) B U b hR hσ p E T
    let P := allocatedChosenScaleBudget m Q (E + 1) (T + 1)
    let Pc := allocatedComparisonDimension m Q
    let L₀ := allocatedNormalizedInitialScale m Q Pc (E + 1) (T + 1)
    (S.value : ℝ) ≤ Real.exp ((p + Etarget + T + a)^a) ∧
    ∀ (M D : ℕ) (hM : 0 < M) (hD : 0 < D)
      (_hMT : (M : ℝ) ≤ Real.exp T) (_hDp : (D : ℝ) ≤ Real.exp p)
      (selection : Fin dim ↪ G) (_hdim : dim ≤ m + 1)
      (_hG : dim * (dim + 2) ≤ Fintype.card G),
    let η := Real.exp (-(E + 1))
    let cutoff := scalarKernelCutoff (Fin dim) G M D η
    let hcutoff := (scalarKernelCutoff_bounds (Fin dim) G hM hD (Real.exp_pos (-(E + 1)))).1
    let Good := GoodScalarKernelTuple (L := S.value) selection (1 / (cutoff : ℝ)) cutoff
    let GoodKernel := {x : G → IntegerScalarCubeBox (Fin dim) S.value // Good x}
    ∃ hlarge : cutoff ≤ S.value,
    (cutoff : ℝ) ≤ Real.exp Q ∧
    ∃ (degree : GoodKernel → ℕ) (hdegree : ∀ x, 0 < degree x),
    (∀ x, (degree x : ℝ) ≤ Real.exp ((p + Etarget + T + a)^a)) ∧
    ∀ (K : G → ℕ) (hKL : ∀ g, K g ≤ S.value) (hDK : ∀ g, S.value ≤ D * K g)
      (shift : G → ℤ) (moduli : G → Option (Fin dim) → ℕ)
      (residues : ∀ g i, ZMod (moduli g i))
      (hmoduli : ∀ g i, 0 < moduli g i) (hmoduliM : ∀ g i, moduli g i ≤ M),
    let kernelLaw := FiniteProbabilityWeights.pi (fun g =>
      affineScalarCubeWindowWeights (Fin dim) S.value (K g) M D (shift g) S.positive
        (hKL g) (hDK g) (moduli g) (residues g) (hmoduli g) (hmoduliM g)
        (scalarKernelCutoff_window_size (Fin dim) G hM hD (Real.exp_pos _) hlarge (hDK g)))
    ∀ [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin dim)) U)] [BorelSpace (SiteTorus (Finset (Fin dim)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv 1 j)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (_hCp : ∀ j, (C j : ℝ) ≤ Real.exp p) (_hVp : ∀ j, (V j : ℝ) ≤ Real.exp p)
    {X : Type uX} [Fintype X] [DecidableEq X] (_hXp : (Fintype.card X : ℝ) ≤ p),
    let O := fun j : Fin m => BoundedBooleanJet (Fin dim) (j.val + 1)
    let rows := fun j => (Subtype.val : O j → Finset (Fin dim))
    let ξ₀ := normalizedTupleNarrowWidth X (PrincipalTupleIndex B (layerSamplerDegree I n))
      selection cutoff Q (E + 1)
    let hξ := normalizedTupleNarrowWidth_pos X (PrincipalTupleIndex B (layerSamplerDegree I n))
      selection cutoff Q (E + 1)
    let W : ℝ := Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ)
    let hW : 0 ≤ W := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    let Pmass := allocatedUnifiedSamplingBudget m dim A P Q (E + 1)
    ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
      (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
      (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U) (c : ∀ j, U j)
      (_hc : coefficientConstantCenter U center =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U) (constantCoefficientArray U (fun s => c s.1))))
      (N stride : X → ℕ) (_hs : ∀ t, 0 < stride t) {Rrank τ : ℝ} (hτ : 0 < τ),
    let δ := normalizedTupleRadius X selection cutoff Q (E + 1) W
    let mesh := δ / 4
    ∀ (_hτp : 1 / τ ≤ Real.exp p) (_hstrideT : ∀ t, (stride t : ℝ) ≤ Real.exp T)
      (_hsize : ∀ t, Real.exp ((p + Etarget + T + a)^a) ≤ (N t : ℝ))
      (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) Rrank (U j) (poly j))
      (_hRank : Real.exp ((p + Etarget + T + a)^a) ≤ Rrank)
      (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
      (_hcells : cells.Nonempty) (bases : Finset (X → ℤ)) (_hbases : bases.Nonempty)
      {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
      (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))),
    let centeredPoly := fun j => subtractConstant (c j).val (poly j)
    let centeredMem := fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j)
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ₀ N
    let baseDensity := jointSelectedPhysicalDensity B U b hb o R σ hR hσ L₀ poly hmem center
    let Z := selectedJointDensityMass bases stride cells widths baseDensity
    ∃ (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
      (hN : ∀ t, 0 < N t) (hZ : 0 < Z),
    let hwidths := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
    let whole := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let law := whole.prod (selectedJointFiniteLaw bases _hbases stride cells widths hwidths
      hmass baseDensity (jointSelectedPhysicalDensity_nonneg B U b hb o R σ hR hσ L₀ poly hmem center) hZ)
    (|Z - 1| ≤ Real.exp (-Pmass) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ Z⁻¹ ≤ 2) ∧
    ∃ reference : GoodKernel → (X → ℤ) → ((X → (Unit ⊕ Fin dim) → ℤ) → ℂ) → ℂ,
    (∀ x : GoodKernel, let : NeZero (degree x) := ⟨(hdegree x).ne'⟩
      ∀ base, allocatedRefinedReferenceFunctional (τ := τ) (ξ := ξ₀) B U b hR hσ S x.val rows X
        hcutoff selection x.property stride hb o bW (degree x) N hW mesh base cells
        (physicalCubeEuclideanSample U (degree x) centeredPoly centeredMem) Z Pc (T + 1) (reference x base)) ∧
    ∀ (test : Finset (Fin dim) → (X → ℝ) → ℂ) (_htest : ∀ s v, ‖test s v‖ ≤ 1),
    ‖kernelLaw.complexMean (fun x => law.complexMean (fun z =>
        physicalCubeSiteTest test (physicalCubeRootDifferences
          (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x z.1)
          (allocatedPhysicalCubeDirections B U b S x z.1) z.2.1.val z.2.2.val))) -
      kernelLaw.goodPartBaseMean bases Good
        (fun x hx base => reference ⟨x, hx⟩ base (physicalCubeSiteTest test))‖ ≤ Real.exp (-Etarget)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem allocatedAveragedKernelComparison (m dim : ℕ) :
    allocatedAveragedKernelStatement m dim := by
  obtain ⟨A, C, hA, _, hcomparison⟩ := allocatedTestUniformJointComparison m dim
  obtain ⟨a₀, ha₀, hthreshold⟩ := exists_allocatedKernelThreshold_bound C
  let a := a₀ + 2
  unfold allocatedAveragedKernelStatement
  refine ⟨A, a, hA, by dsimp [a]; omega, ?_⟩
  intro G _ _ _ I _ _ n B _ _ J _ U b R σ hR hσ p Etarget T hp hEtarget hT
    hvars hI hn hJ hRup hRi hσi hmsp E Q S P Pc L₀
  have hE : 0 ≤ E := by dsimp [E]; linarith
  obtain ⟨hQ, hpQ, _, _, _⟩ := allocatedKernelPrimitiveBudget_bounds hp hE hT
  have hexp := Real.exp_le_exp.mpr hpQ
  have hwork : (p + E + T + a₀)^a₀ ≤ (p + Etarget + T + a)^a := by
    have hbase : p + E + T + a₀ ≤ p + Etarget + T + a := by
      dsimp [E, a]
      push_cast
      linarith
    have hone : 1 ≤ p + Etarget + T + a := by
      dsimp [a]
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) a₀]
    exact (pow_le_pow_left₀ (by positivity) hbase a₀).trans
      (pow_le_pow_right₀ hone (by dsimp [a]; omega))
  have hcut : (Q + E + (T + 1) + C)^C ≤ (p + Etarget + T + a)^a := by
    have hstep : Q + E + (T + 1) + C ≤ Q + (E + 1) + (T + 1) + C := by linarith
    exact (pow_le_pow_left₀ (by positivity) hstep C).trans
      ((hthreshold hp hE hT).trans hwork)
  obtain ⟨S', hS', hSbound, hkernel⟩ := hcomparison B U b hR hσ hQ hE
    (show 0 ≤ T + 1 by positivity) (hvars.trans hpQ)
    (fun j => (hI j).trans hpQ) (fun j => (hn j).trans hpQ) (fun j => (hJ j).trans hpQ)
    (fun j => (hRup j).trans hexp) (fun j => (hRi j).trans hexp)
    (fun j => (hσi j).trans hexp) (hmsp.trans hpQ)
  have hS : S' = S := hS'
  subst S'
  refine ⟨hSbound.trans (Real.exp_le_exp.mpr hcut), ?_⟩
  intro M D hM hD hMT hDp selection hdim hG η cutoff hcutoff Good GoodKernel
  have hdimP : (dim : ℝ) ≤ p :=
    (Nat.cast_le.mpr (by omega : dim ≤ m + 2)).trans hmsp
  have hGp : (Fintype.card G : ℝ) ≤ p :=
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans hvars
  obtain ⟨hcutoffQ, hlarge⟩ := allocatedKernelScale_cutoff B U b hR hσ
    hp hE hT hdimP hGp hM hD hMT hDp
  refine ⟨hlarge, hcutoffQ, ?_⟩
  have hforKernel (x : GoodKernel) := hkernel x.val hcutoff hcutoffQ selection x.property hdim
  choose degree hdegree hdegreeBound hconstruct using hforKernel
  refine ⟨degree, hdegree, fun x => (hdegreeBound x).trans (Real.exp_le_exp.mpr hcut), ?_⟩
  intro K hKL hDK shift moduli residues hmoduli hmoduliM kernelLaw
  have hbad : kernelLaw.eventProbability (fun x => ¬Good x) ≤ η :=
    allocatedKernelScale_affine_bad_probability B U b hR hσ hp hE hT hdimP hGp hG
      selection hM hD hMT hDp K hKL hDK shift moduli residues hmoduli hmoduliM
  have hηlt : η < 1 := by
    change Real.exp (-(E + 1)) < 1
    calc
      _ < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have hexists : ∃ x : G → IntegerScalarCubeBox (Fin dim) S.value, Good x := by
    by_contra! hnone
    have hone : kernelLaw.eventProbability (fun x => ¬Good x) = 1 := by
      simp only [FiniteProbabilityWeights.eventProbability, hnone, not_false_eq_true,
        ite_true, FiniteProbabilityWeights.mean_const]
    linarith
  obtain ⟨x₀, hx₀⟩ := hexists
  let x0 : GoodKernel := ⟨x₀, hx₀⟩
  intro _ _ _ _ _ hb o Cchart Vcap hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _ hCp hVp
  let : ∀ x : GoodKernel, NeZero (degree x) := fun x => ⟨(hdegree x).ne'⟩
  have hg (x : GoodKernel) := hconstruct x hb o Cchart Vcap hC hV hσ1 Cinv hCinv hchart hsmall μ ν
  choose g hgc hgb hgi hgm hglaw hgproj hdata using hg
  intro X _ _ hXp O rows ξ₀ hξ W hW Pmass poly hpoly hmem center c hc N stride hs Rrank τ hτ
    δ mesh hτp hstrideT hsize hrank hRank cells hcells bases hbases Kcov _ bW
    centeredPoly centeredMem widths baseDensity Z
  have hresults (x : GoodKernel) := hdata x
    (fun j => (hCp j).trans hexp) (fun j => (hVp j).trans hexp) (hXp.trans hpQ)
    poly hpoly hmem center c hc N stride hs hτ (hτp.trans hexp)
    (fun t => (hstrideT t).trans (Real.exp_le_exp.mpr (by linarith : T ≤ T + 1)))
    (fun t => (Real.exp_le_exp.mpr hcut).trans (hsize t)) hrank
    ((Real.exp_le_exp.mpr hcut).trans hRank) cells hcells bases hbases bW
  choose hmass hN hZ hnormal reference hrep herror using hresults
  let law := (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).prod
    (selectedJointFiniteLaw bases hbases stride cells widths
      (narrowTrimmedSpatialWidths_pos hW hτ hξ N (hN x0)) (hmass x0) baseDensity
      (jointSelectedPhysicalDensity_nonneg B U b hb o R σ hR hσ L₀ poly hmem center) (hZ x0))
  refine ⟨hmass x0, hN x0, hZ x0, hnormal x0, reference, hrep, ?_⟩
  intro test htest
  have hunit (x : G → IntegerScalarCubeBox (Fin dim) S.value) :
      ‖law.complexMean (fun z => physicalCubeSiteTest test (physicalCubeRootDifferences
        (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x z.1)
        (allocatedPhysicalCubeDirections B U b S x z.1) z.2.1.val z.2.2.val))‖ ≤ 1 := by
    apply (law.norm_complexMean_le_mean_norm _).trans
    exact (law.mean_mono (fun z => physicalCubeSiteTest_norm_le test htest _)).trans_eq (law.mean_const 1)
  have havg := kernelLaw.complexMean_goodPart_comparison Good
    (fun x => law.complexMean (fun z => physicalCubeSiteTest test (physicalCubeRootDifferences
      (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x z.1)
      (allocatedPhysicalCubeDirections B U b S x z.1) z.2.1.val z.2.2.val)))
    (fun x hx => 𝔼 base ∈ bases, reference ⟨x, hx⟩ base (physicalCubeSiteTest test))
    (Real.exp_pos (-E)).le hunit (fun x hx => (herror ⟨x, hx⟩ test htest).2)
  have hηsmall : η ≤ Real.exp (-E) := Real.exp_le_exp.mpr (by linarith : -(E + 1) ≤ -E)
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hsum : Real.exp (-E) + η ≤ Real.exp (-Etarget) := by
    calc
      _ ≤ 2 * Real.exp (-E) := by linarith
      _ ≤ Real.exp 1 * Real.exp (-E) := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = Real.exp (-Etarget) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [E]
        ring
  exact havg.trans ((add_le_add le_rfl hbad).trans hsum)

end Erdos3.VectorPolynomial

end

end OAI

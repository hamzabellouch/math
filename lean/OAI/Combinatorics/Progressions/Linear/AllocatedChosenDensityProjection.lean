import OAI.Combinatorics.Progressions.Estimates.AllocatedProjectedChosenComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

universe uX

theorem exists_allocated_chosen_density_projection (m q : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ v, Fintype (B v)] [∀ v, DecidableEq (B v)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {p E T : ℝ} (_hp : 0 ≤ p) (_hE : 0 ≤ E) (_hT : 0 ≤ T)
    (_hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (_hn : ∀ j, (n j : ℝ) ≤ p)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p) (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp p)
    (_hmsp : ((m + 2 : ℕ) : ℝ) ≤ p)
    (S : LayerSamplerScale (G := G) B U b R σ)
    (_hS : S = allocatedPrimitiveNormalizedScale B U b hR hσ p E T)
    (x : G → IntegerScalarCubeBox (Fin q) S.value)
    {M : ℕ} (_hM : 0 < M) (_hMp : (M : ℝ) ≤ Real.exp p)
    (selection : Fin q ↪ G) (_hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
    (_hq : q ≤ m + 1)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin q) Cinv 1 j)
    (_hCp : ∀ j, (C j : ℝ) ≤ Real.exp p) (_hVp : ∀ j, (V j : ℝ) ≤ Real.exp p)
    {X : Type uX} [Fintype X] [DecidableEq X] (_hXp : (Fintype.card X : ℝ) ≤ p)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
    (N stride : X → ℕ) (_hs : ∀ t, 0 < stride t)
    {rank τ : ℝ} (_hτ : 0 < τ) (_hτp : 1 / τ ≤ Real.exp p)
    (_hstrideT : ∀ t, (stride t : ℝ) ≤ Real.exp T)
    (_hsize : ∀ t, Real.exp ((p + E + T + a) ^ a) ≤ (N t : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) rank (U j) (poly j))
    (_hRank : Real.exp ((p + E + T + a) ^ a) ≤ rank)
    (base : X → ℤ)
    (test : Finset (Fin q) → (X → ℝ) → ℂ) (_htest : ∀ s v, ‖test s v‖ ≤ 1)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (_hcells : cells.Nonempty) (D : ℕ)
    (f : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U b S) →
      EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ),
    let density := allocatedCoefficientDensity B U b hb o hR hσ S
    ∀ (_hproject : ∀ y, physicalDensityProjection.{_, _, uX, 0} U
      (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U b S x y) D density (f y))
    {Z : ℝ} (_hZ : 1 / 2 ≤ Z),
    let W : ℝ := Fintype.card (LayerSamplerVariables G I n B) * S.value
    let ξ := normalizedTupleNarrowWidth X (PrincipalTupleIndex B (layerSamplerDegree I n)) selection M p E
    let widths := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    ∀ (hwidths : ∀ z, 0 < widths z) (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z),
    let law := principalTupleWeights (α := Fin q) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let source := fun y => ∑' z,
      ((selectedResidueSmoothPMF stride cells widths hwidths hmass z).toReal : ℂ) *
        (physicalCubeSiteTest test (physicalCubeRootDifferences
          (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) base z) *
          (density (affineSampleCoefficientTorus U
            (fun j => translate (fun t => (base t : ℝ)) (poly j))
            (fun j => coefficients_translate_mem (U j) (fun t => (base t : ℝ)) (poly j) (hmem j))
            (fun k t => (z (k, t) : ℝ))) : ℂ))
    let projected := fun y => ∑' z,
      ((selectedResidueSmoothPMF stride cells widths hwidths hmass z).toReal : ℂ) *
        physicalCubePositiveTest U D poly hmem (f y) test (physicalCubeRootDifferences
          (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) base z)
    ‖law.complexMean source / (Z : ℂ) - law.complexMean projected / (Z : ℂ)‖ ≤ Real.exp (-E) := by
  obtain ⟨A₀, _, hprojection⟩ := exists_allocated_original_density_projection m q
  obtain ⟨K, _, hthreshold⟩ := exists_allocatedUnifiedSamplingThreshold_bound m q 0 A₀
  obtain ⟨a, ha, hcut⟩ := exists_allocatedChosenThreshold_bound m 0 K
  refine ⟨a, ha, ?_⟩
  intro G _ _ I _ _ n B _ _ J _ U b R σ hR hσ p E T hp hE hT hvars hI hn hJ hRi hσi hmsp
    S hS x M hM hMp selection hx hq hb o C V hC hV hσ1 Cinv hCinv hchart hsmall hCp hVp
    X _ _ hXp poly hpoly hmem N stride hs rank τ hτ hτp hstrideT hsize hrank hRank base test htest
    cells hcells D f density hproject Z hZ W ξ widths hwidths hmass law source projected
  let P := allocatedChosenScaleBudget m p E T
  let Q := allocatedUnifiedSamplingBudget m q 0 P p E
  obtain ⟨hP, hpP, _, hTP, hDP, hLogP⟩ := allocatedChosenScaleBudget_bounds m hp hE hT
  obtain ⟨_, _, _, hQ, _, hwidth, hPplus, hpQ, hEQ, hnorm⟩ :=
    allocatedUnifiedSamplingBudget_bounds m q 0 hP hp hE
  have hPQ : P ≤ Q := by linarith
  have hpExp := Real.exp_le_exp.mpr hpQ
  have hPExp := Real.exp_le_exp.mpr hPQ
  have hL : (S.value : ℝ) ≤ Real.exp P := by
    rw [hS]
    exact (allocatedPrimitiveNormalizedScale_upper B U b hR hσ hp hE hT hvars hn hRi hσi).trans
      (Real.exp_le_exp.mpr hLogP)
  have hcount (j : Fin m) :
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Q :=
    (boundedCoefficientExponent_card_le_geometricSiteBudget m 0
      (Nat.succ_le_of_lt j.isLt) hp hvars).trans
        ((allocatedComparisonDimension_bounds m hp).2.2.2.2.1.trans (hDP.trans hPQ))
  have hmQ : (m : ℝ) ≤ Q := by
    have hmp : (m : ℝ) ≤ p := by push_cast at hmsp; linarith
    exact hmp.trans hpQ
  have hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Q := by
    obtain ⟨_, _, _, _, _, _, _, _, hprofile⟩ := allocatedComparisonDimension_bounds m hp
    exact (probabilityProfileLipschitz_le_comparisonProfileBound.trans
      (hprofile.trans (hDP.trans hPQ))).trans (by linarith [Real.add_one_le_exp Q])
  have hW : 0 ≤ W := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hroot : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W := by
    dsimp only [W, allocatedPhysicalRootBudget]
    simp
  have hWP : W ≤ Real.exp Q := by
    calc
      W ≤ Real.exp p * Real.exp P :=
        mul_le_mul (hvars.trans (by linarith [Real.add_one_le_exp p])) hL
          (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (P + p) := by rw [← Real.exp_add, add_comm]
      _ ≤ _ := Real.exp_le_exp.mpr hPplus
  have hnormdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ Q := by
    calc
      _ = ((Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 1) * Fintype.card X := by
        simp only [Fintype.card_prod, Fintype.card_option, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      _ ≤ (p + 1) * p := mul_le_mul (add_le_add hvars le_rfl) hXp (Nat.cast_nonneg _) (by positivity)
      _ = p * (p + 1) := mul_comm _ _
      _ ≤ _ := hnorm
  have hGp : (Fintype.card G : ℝ) ≤ p :=
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans hvars
  have hNp : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (allocatedPrincipalIndex_card_le_variables (G := G) B)).trans hvars
  have hmsp' : ((m + 1 : ℕ) : ℝ) ≤ p := by push_cast at hmsp ⊢; linarith
  have hqsp : ((q + 1 : ℕ) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (by omega : q + 1 ≤ m + 2)).trans hmsp
  have hqcard : (Fintype.card (Unit ⊕ Fin q) : ℝ) ≤ p := by
    simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Nat.add_comm 1] using hqsp
  have hchoice := normalizedTupleSpatialChoices (N := PrincipalTupleIndex B (layerSamplerDegree I n))
    (X := X) (m := m) selection hM hp hE hmsp' hqsp hGp hXp hMp
  have hlog := (normalizedTuple_log_envelopes X (PrincipalTupleIndex B (layerSamplerDegree I n))
    selection hp hE (le_refl (0 : ℝ)) hqcard hGp hNp hXp).1
  have hξQ : ξ⁻¹ ≤ Real.exp Q :=
    hchoice.2.2.1.trans (Real.exp_le_exp.mpr (hlog.trans hwidth))
  have hcutQ : (Q + A₀) ^ A₀ ≤ (p + E + T + a) ^ a :=
    (hthreshold hP hp hE).trans (hcut hp hE hT).2.2
  have hZpos : 0 < Z := by linarith
  have hZi : Z⁻¹ ≤ (2 : ℝ) := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hZ
    simpa only [one_div, inv_inv] using h
  have htwo : (2 : ℝ) ≤ Real.exp Q := by
    have hp2 : (2 : ℝ) ≤ p := by push_cast at hmsp; linarith [Nat.cast_nonneg (α := ℝ) m]
    linarith [Real.add_one_le_exp Q]
  have hsmallDensity := allocatedPhysicalChartRadius_density_small B (Fin q) Cinv R
    hCinv (fun j => (hR j).le) hsmall
  have he := hprojection B U b S (fun _ => 0) x hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart
    hsmallDensity hQ hmQ (hvars.trans hpQ) hW hroot hWP (hL.trans hPExp)
    (fun j => (hRi j).trans hpExp) (fun j => (hσi j).trans hpExp) hcount
    (fun j => (hI j).trans hpQ) (fun j => (hn j).trans hpQ) (fun j => (hJ j).trans hpQ)
    hprofile (fun j => (hCp j).trans hpExp) (fun j => (hVp j).trans hpExp) hx.2
    (hXp.trans hpQ) hnormdim poly hpoly hmem base stride hs
    (fun t => (hstrideT t).trans (Real.exp_le_exp.mpr (hTP.trans hPQ)))
    hτ (by simpa only [one_div] using hτp.trans hpExp) hchoice.1 hchoice.2.1 hξQ
    N (fun t => (Real.exp_le_exp.mpr hcutQ).trans (hsize t)) hrank
    ((Real.exp_le_exp.mpr hcutQ).trans hRank) test htest cells hcells D f hproject
    hZpos (hZi.trans htwo) hwidths hmass
  exact he.trans (Real.exp_le_exp.mpr (neg_le_neg hEQ))

end Erdos3.VectorPolynomial

end

end OAI

import OAI.Combinatorics.Progressions.Geometry.AllocatedPositiveSpatialComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel MeasureTheory
open scoped BigOperators

theorem exists_allocated_fixed_product_comparison (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    [DecidableEq (LayerSamplerVariables G I n B)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox (Fin q) S.value)
    {P W κ : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P) (_hW : 0 ≤ W)
    (_hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (_hWP : W ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    (selection : Fin q ↪ G) (_hκ : 0 < κ) {M : ℕ}
    (_hx : GoodScalarKernelTuple selection κ M x) (_hMP : (M : ℝ) ≤ Real.exp P)
    (_hκP : κ⁻¹ ≤ Real.exp P),
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U basis S))
    {X : Type*} [Fintype X] [DecidableEq X]
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    {F : Type*} [Fintype F]
    (frequency : F → ∀ j, (LayerSamplerVariables G I n B →₀ ℕ) → J j → ℤ)
    (_hfrequency : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ Real.exp P),
    ∃ b : F → ∀ j, Matrix (Finset (Fin q)) (J j) ℤ,
      (∀ a j s t, |(b a j s t : ℝ)| ≤ Real.exp ((P + A) ^ A)) ∧
    ∀ (coeff : F → ℂ) (_hcoeff : (∑ a, ‖coeff a‖) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (base : X → ℤ)
    (stride : X → ℕ) (hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {τ δ ε : ℝ} (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hδ : 0 < δ) (_hδP : δ⁻¹ ≤ Real.exp P) (_hε : 0 < ε) (_hεP : ε⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    (_hsmall : (∑ _d : X, shiftedMatrixCountFactor (Unit ⊕ Fin q)
      (Option (LayerSamplerVariables G I n B)) * ε) ≤ 1)
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (test : Finset (Fin q) → (X → ℝ) → ℂ) (_htest : ∀ s v, ‖test s v‖ ≤ 1)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    (density : CoefficientTorus (K := LayerSamplerVariables G I n B) U → ℝ)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ v, ‖(density v : ℂ) - coefficientTorusFourierSum U frequency coeff v‖ ≤ η) {Z : ℝ} (_hZnorm : 0 < Z),
    let V := trimmedSpatialWidths (K := LayerSamplerVariables G I n B) W τ N
    let root := allocatedPhysicalCubeRoot B U basis S c x y
    let dirs := allocatedPhysicalCubeDirections B U basis S x y
    let pa := fun j => translate (fun d => (base d : ℝ)) (p j)
    let hma := fun j => coefficients_translate_mem (U j) (fun d => (base d : ℝ)) (p j) (hm j)
    let sel := selection.trans (Function.Embedding.inl : G ↪ LayerSamplerVariables G I n B)
    let out := fun d => physicalSpatialOutputScale (Fin q)
      (trimmedSpatialRootScale τ N stride d) (trimmedSpatialSlopeScale W τ N stride d) S.value
    ∃ (hV : ∀ z, 0 < V z) (hOut : ∀ d i, 0 < out d i)
      (hpivot : ((physicalCubeCoefficient root dirs).submatrix id (physicalCubePivotIndex sel)).det ≠ 0)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T V z),
      ‖(∑' z, ((selectedResidueSmoothPMF stride T V hV hZ z).toReal : ℂ) *
        (physicalCubeSiteTest test (physicalCubeRootDifferences root dirs base z) *
          (density (affineSampleCoefficientTorus U pa hma (fun k d => (z (k, d) : ℝ))) : ℂ))) / (Z : ℂ) -
        (∑ r : T, (selectedResidueCellWeight stride T V r : ℂ) *
          ∫ v, (shiftedProductGridProxy (fun _ : X => physicalCubeCoefficient root dirs)
            (fun _ => physicalCubePivotIndex sel) (fun _ => hpivot)
            (residueProfileCenter (boundedColumnResidueRepresentative stride r.val) stride)
            (residueProfileWidth stride V) out (residueProfileWidth_pos stride V hs hV) hOut v : ℂ) *
            physicalCubeCoveredTest U root dirs D p hm frequency b coeff test
              (physicalResidueReconstruct root dirs base
                (boundedColumnResidueRepresentative stride r.val) stride v) ∂Measure.count) / (Z : ℂ)‖ ≤
          (η + δ + (∑ a, ‖coeff a‖) * (2 * ∑ _d : X,
            shiftedMatrixCountFactor (Unit ⊕ Fin q) (Option (LayerSamplerVariables G I n B)) * ε)) / Z := by
  classical
  obtain ⟨A₀, _, hprojection⟩ := exists_allocated_fixed_density_projection m q
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + Polynomial.C A₀) ^ A₀ + spatialProjectionBudget q Polynomial.X)
  refine ⟨A, hA, ?_⟩
  intro G _ _ I _ n B _ _ J _ U basis R σ S c x P W κ hP hK hW hroot hWP hL
    selection hκ M hx hMP hκP
  have hsum : (P + A₀) ^ A₀ + spatialProjectionBudget q P ≤ (P + A) ^ A := by
    simpa [spatialProjectionBudget, Polynomial.eval₂_pow] using hbudget P hP
  have hprojcost : (P + A₀) ^ A₀ ≤ (P + A) ^ A := by
    linarith [spatialProjectionBudget_nonneg q hP]
  have hspatialcost : spatialProjectionBudget q P ≤ (P + A) ^ A := by
    linarith [pow_nonneg (add_nonneg hP (Nat.cast_nonneg A₀)) A₀]
  have hG : (Fintype.card G : ℝ) ≤ P :=
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans hK
  obtain ⟨D, hD, hDP, hrows⟩ := hprojection B U basis S c x hP hG hW hroot hWP hL hx.2
  refine ⟨D, hD, hDP.trans (Real.exp_le_exp.mpr hprojcost), ?_⟩
  intro y X _ _ hX hdim F _ frequency hfrequency
  obtain ⟨b, hb, hproj⟩ := hrows y hX hdim frequency hfrequency
  refine ⟨b, fun a j s t => (hb a j s t).trans (Real.exp_le_exp.mpr hprojcost), ?_⟩
  intro coeff hcoeff p hp hm base stride hs hsP τ δ ε hτ hτP hδ hδP hε hεP
    N hsize hsmall rank hrank hRank test htest T hT density η hη happrox Z hZnorm
  obtain ⟨hV, hZ, hfirst⟩ := hproj coeff hcoeff p hp hm base stride hs hsP hτ hτP hδ hδP
    N (fun d => (Real.exp_le_exp.mpr hprojcost).trans (hsize d)) hrank
    ((Real.exp_le_exp.mpr hprojcost).trans hRank) test htest T hT density hη happrox
  let root := allocatedPhysicalCubeRoot B U basis S c x y
  let dirs := allocatedPhysicalCubeDirections B U basis S x y
  let V := trimmedSpatialWidths (K := LayerSamplerVariables G I n B) W τ N
  have hspatial (d) : Real.exp (physicalSpatialLogAllowance
      (selection.trans (Function.Embedding.inl : G ↪ LayerSamplerVariables G I n B)) (P + 2) +
      4 * P + 12) ≤ (N d : ℝ) :=
    (Real.exp_le_exp.mpr ((physicalSpatialLogAllowance_le_projection_budget _ hP hK).trans
      hspatialcost)).trans (hsize d)
  obtain ⟨hV', hOut, hpivot, hZ', hsecond⟩ :=
    allocatedTrimmedSpatial_product_comparison B U basis S c x y selection W τ N stride
      hP hκ hε hx hW hτ hs hroot hWP hL hMP hκP hsP hτP hεP hspatial T hT base hsmall
      (physicalCubeCoveredTest U root dirs D p hm frequency b coeff test)
      (Finset.sum_nonneg (fun a _ => norm_nonneg (coeff a)))
      (fun v => physicalCubeCoveredTest_norm_le U root dirs D p hm frequency b coeff test htest v)
  refine ⟨hV, hOut, hpivot, hZ, ?_⟩
  have h := (norm_sub_le_norm_sub_add_norm_sub _
    (∑' z, ((selectedResidueSmoothPMF stride T V hV hZ z).toReal : ℂ) *
      physicalCubeCoveredTest U root dirs D p hm frequency b coeff test
        (physicalCubeRootDifferences root dirs base z)) _).trans (add_le_add hfirst hsecond)
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZnorm]
  exact div_le_div_of_nonneg_right h hZnorm.le

end Erdos3.VectorPolynomial

end

end OAI

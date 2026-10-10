import OAI.Combinatorics.Progressions.Estimates.PreparedCanonicalNativeSource

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {s nX : ℕ}
variable (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (N : (Fin nX) → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : (Fin nX) → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))

local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N

variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset ((Fin nX) → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S (Fin nX) poly hmem))

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)
local notation "kernelLaw" => FiniteProbabilityWeights.pi
  (fun _ : G => integerScalarCubeWeights (Fin (s + 2)) S.value S.positive)

local notation "Path" => bases × rectangularWeightIndices 0 widths 1
local notation "pathLaw" => allocatedOriginalPathLaw B U b hb o hR hσ S (Fin nX) poly hmem
  N hN hW hτ hξ stride cells hmass bases hbases htotal

variable {M : ℕ} (hM : 0 < M) (selection : Fin (s + 2) ↪ G)
variable {Kcov : Fin m → Type} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (pI p0 pAccuracy w v E0 Dcap O pc gc Pτ : ℝ)

variable (family : ∀ x : {x : G → IntegerScalarCubeBox (Fin (s + 2)) S.value // GoodScalarKernelTuple selection (1 / (M : ℝ)) M x}, ∀ base : Fin nX → ℤ,
  AllocatedCoarseSourceData (Kcov := Kcov) B U b S stride N x.val hM selection x.property τ base
    pI p0 pAccuracy w v E0 Dcap O pc gc Pτ (selectedJointDensityMass bases stride cells (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) (allocatedJointBaseDensity B U b hb o hR hσ S (Fin nX) poly hmem)))

theorem allocatedOriginalPathLaw_niltest_native_detection
    (P : Polynomial ℕ)
    {T : Type} [Fintype T] [Nonempty T]
    (e : T → LayerSamplerVariables G I n B → ℤ) (he : Function.Injective e)
    (hcover : ∀ t ∈ integerBox sides, ∃ u, e u = t)
    {Tests : Path → Type} [∀ z, Nonempty (Tests z)]
    {L : ∀ z, Tests z → Type} [∀ z j, LieRing (L z j)] [∀ z j, LieAlgebra ℚ (L z j)]
    {dims : ∀ z, Tests z → ℕ}
    [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] L z j)]
    [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L z j)]
    [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] L z j)]
    (D : ∀ z j, RationalFilteredNilmanifold (L z j) (s + 1) (dims z j))
    (V : ∀ z j, (D z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
    (slices : ∀ z, Tests z → Finset T)
    (c : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
    (step : ∀ z, Tests z → ℕ)
    (H : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ)
    (hstep : ∀ z j, 0 < step z j)
    (hslices : ∀ z j, (slices z j).image e = commonStrideBox (c z j) (step z j) (H z j))
    (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hdense : ∀ z j, IsDenseCommonStrideBox sides p ((slices z j).image e))
    (hdimension : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) q)
    (hcomplexity : ∀ z j, (V z j).ComplexityLE (P.eval₂ (Nat.castRingHom ℝ) q))
    (hcap : ∀ z j, ((V z j).normBound : ℝ) ≤ 1)
    (f : ((Fin nX) → ℤ) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1)
    (hmesh : Fintype.card (LayerSamplerVariables G I n B) * Real.exp (-p) ≤ α / 8)
    (hthreshold : Real.exp (-q) ≤ α / 4)
    (hdetected : α ≤ sampledSliceSeminorm (pathLaw)
      (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) slices
      (fun z j t => star ((V z j).eval (commonStrideIndex (c z j) (step z j) (e t)))) f)
    {budget E η : ℝ} (hbudget : 0 ≤ budget) (hnX : (nX : ℝ) ≤ budget)
    (hcost : allocatedCoarseNativeLog m (s + 2) pI p0 pAccuracy w v E0 Dcap O pc gc Pτ ≤ budget)
    (hdetectBudget : (p + q + sampledFullboxDetectionConstant s P) ^
      sampledFullboxDetectionConstant s P + 1 ≤ budget)
    (hE : (p + q + sampledFullboxDetectionConstant s P) ^
      sampledFullboxDetectionConstant s P + 5 ≤ E)
    (hη : η ≤ Real.exp (-((p + q + sampledFullboxDetectionConstant s P) ^
      sampledFullboxDetectionConstant s P + 5)))
    (hcomparison :
      ‖(pathLaw).complexMean (fun z =>
        𝔼 cube : SupportedCube (s + 2) (integerBox sides : Set (LayerSamplerVariables G I n B → ℤ)),
          physicalCubeSiteTest (integerSelfSiteTest (s + 2) f)
            (physicalCubeRootDifferences cube.val.2 cube.val.1 z.1.val z.2.val)) -
        (kernelLaw).goodPartBaseMean bases (GoodScalarKernelTuple selection (1 / (M : ℝ)) M)
          (fun x hx base => (family ⟨x, hx⟩ base).source hb o bW cells poly hmem widths f)‖ ≤
        2 * Real.exp (-E) + η) :
    ∃ (x : {x : G → IntegerScalarCubeBox (Fin (s + 2)) S.value // GoodScalarKernelTuple selection (1 / (M : ℝ)) M x}) (base : Fin nX → ℤ), base ∈ bases ∧
      ∃ ψ ∈ (family x base).twists hb o bW cells poly hmem, ∃ g : integerBox N → ℂ,
        Nonempty (NativeSampleModel (fun _ : Fin nX => 1) (s + 1)
          ((budget + 2) ^ Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} (s + 1)))
          (fun u : integerBox N => u.val) g) ∧
        Real.exp (-((budget + 2) ^ Classical.choose
          (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} (s + 1)))) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
              (by let : ∀ i, NeZero (N i) := fun i => ⟨(hN i).ne'⟩; exact integerBox_nonempty N)).correlation
            (fun u => f u.val) (fun u => star (ψ u) * g u)‖ := by
  let : ∀ i, NeZero (N i) := fun i => ⟨(hN i).ne'⟩
  obtain ⟨x, hx, base, _, hbase, hpositive⟩ :=
    allocatedOriginalPathLaw_niltest_selection B U b hb o hR hσ S (Fin nX) poly hmem
      N hN hW hτ hξ stride cells hmass bases hbases htotal P e he hcover D V slices c step H
      hstep hslices p q hp hq hdense hdimension hcomplexity hcap f hf α hα hαone hmesh hthreshold
      hdetected (GoodScalarKernelTuple selection (1 / (M : ℝ)) M) (fun x hx base => (family ⟨x, hx⟩ base).source hb o bW cells poly hmem widths f)
      hE hη hcomparison
  have hsource : Real.exp (-budget) ≤
      ((family ⟨x, hx⟩ base).source hb o bW cells poly hmem widths f).re :=
    (Real.exp_le_exp.mpr (neg_le_neg hdetectBudget)).trans hpositive
  obtain ⟨ψ, hψ, g, hg, hcorrelation⟩ :=
    (family ⟨x, hx⟩ base).detect hb o bW cells poly hmem hbudget hnX hcost htotal widths
      (narrowTrimmedSpatialWidths_pos hW hτ hξ N hN) hmass f (fun u _ => hf u) hsource
  exact ⟨⟨x, hx⟩, base, hbase, ψ, hψ, g, hg, hcorrelation⟩

end Erdos3.VectorPolynomial

end

end OAI

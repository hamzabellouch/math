import OAI.Combinatorics.Progressions.Nilpotent.AllocatedNiltestNativeDetection

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

theorem allocatedOriginalPathLaw_native_approximation
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
    (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1)
    (hmesh : Fintype.card (LayerSamplerVariables G I n B) * Real.exp (-p) ≤ α / 8)
    (hthreshold : Real.exp (-q) ≤ α / 4)
    {budget E η : ℝ} (hbudget : 0 ≤ budget) (hnX : (nX : ℝ) ≤ budget)
    (hcost : allocatedCoarseNativeLog m (s + 2) pI p0 pAccuracy w v E0 Dcap O pc gc Pτ ≤ budget)
    (hdetectBudget : (p + q + sampledFullboxDetectionConstant s P) ^
      sampledFullboxDetectionConstant s P + 1 ≤ budget)
    (hE : (p + q + sampledFullboxDetectionConstant s P) ^
      sampledFullboxDetectionConstant s P + 5 ≤ E)
    (hη : η ≤ Real.exp (-((p + q + sampledFullboxDetectionConstant s P) ^
      sampledFullboxDetectionConstant s P + 5)))
    (hcomparison : ∀ f : (Fin nX → ℤ) → ℂ, (∀ u, ‖f u‖ ≤ 1) →
      ‖(pathLaw).complexMean (fun z =>
        𝔼 cube : SupportedCube (s + 2) (integerBox sides : Set (LayerSamplerVariables G I n B → ℤ)),
          physicalCubeSiteTest (integerSelfSiteTest (s + 2) f)
            (physicalCubeRootDifferences cube.val.2 cube.val.1 z.1.val z.2.val)) -
        (kernelLaw).goodPartBaseMean bases (GoodScalarKernelTuple selection (1 / (M : ℝ)) M)
          (fun x hx base => (family ⟨x, hx⟩ base).source hb o bW cells poly hmem widths f)‖ ≤
        2 * Real.exp (-E) + η)
    (physical : Path → T → integerBox N)
    (hphysical : ∀ z t, (physical z t).val = jointIntegerPhysicalSite (e t) (z.1.val, z.2.val))
    {K C cap tau εtail : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hcapInput : 0 < cap) (htau : 0 < tau)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (hαeq : α = (tau / cap ^ 2) / max 1 (K * (2 * C) / tau))
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N)
        (by let : ∀ i, NeZero (N i) := fun i => ⟨(hN i).ne'⟩; exact integerBox_nonempty N)).excessMass
      ((pathLaw).siteLaw physical) C ≤ εtail)
    (input : integerBox N → ℂ) (hinput : ∀ u, ‖input u‖ ≤ cap) :
    let twists : Set (integerBox N → ℂ) :=
      {ψ | ∃ x : {x : G → IntegerScalarCubeBox (Fin (s + 2)) S.value // GoodScalarKernelTuple selection (1 / (M : ℝ)) M x}, ∃ base ∈ bases,
        ψ ∈ (family x base).twists hb o bW cells poly hmem}
    let qModel := (budget + 2) ^ Classical.choose
      (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} (s + 1))
    ∃ (nterms : ℕ) (_ : 0 < nterms) (Q : Fin nterms → (integerBox N → ℂ))
      (coeff : Fin nterms → ℝ) (err : integerBox N → ℂ),
      (∀ i, Q i ∈ twistedNativeSampleFunctions (fun _ : Fin nX => 1) (s + 1) qModel
        (fun u : integerBox N => u.val) (Subtype.val : twists → integerBox N → ℂ)) ∧
      input = (∑ i, coeff i • Q i) + err ∧
      (∑ i, |coeff i|) ≤ 2 / Real.exp (-qModel) ∧
      sampledSliceSeminorm (pathLaw) physical slices
        (fun z j t => star ((V z j).eval (commonStrideIndex (c z j) (step z j) (e t)))) err ≤
        2 * tau + 2 * K * (cap + 2 / Real.exp (-qModel)) * εtail ∧
      (nterms : ℝ) ≤ 1 + 4 * (K * (2 * C)) ^ 2 / (Real.exp (-qModel) ^ 2 * tau ^ 2) := by
  intro twists qModel
  let : ∀ i, NeZero (N i) := fun i => ⟨(hN i).ne'⟩
  let : Nonempty (integerBox N) := (integerBox_nonempty N).to_subtype
  let weights := fun z j t => star ((V z j).eval (commonStrideIndex (c z j) (step z j) (e t)))
  have hweights (z) (j) (t) : ‖weights z j t‖ ≤ 1 := by
    dsimp only [weights]
    rw [norm_star]
    exact ((V z j).norm_eval_le _).trans (hcap z j)
  have htwists (ψ : twists) (u) : ‖ψ.val u‖ ≤ 1 := by
    obtain ⟨x, base, _, hψ⟩ := ψ.property
    exact (family x base).twists_norm hb o bW cells poly hmem ψ.val hψ u
  have hdetector (g : integerBox N → ℂ) (hg : ∀ u, ‖g u‖ ≤ 1)
      (hlarge : (tau / cap ^ 2) / max 1 (K * (2 * C) / tau) ≤
        sampledSliceSeminorm (pathLaw) physical slices weights g) :
      ∃ (ψ : twists) (G : integerBox N → ℂ),
        Nonempty (NativeSampleModel (fun _ : Fin nX => 1) (s + 1) qModel
          (fun u : integerBox N => u.val) G) ∧
        Real.exp (-qModel) ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
          (integerBox_nonempty N)).correlation g (fun u => star (ψ.val u) * G u)‖ := by
    let f := finiteSiteExtension (Subtype.val : integerBox N → Fin nX → ℤ) g
    have hf (u) : ‖f u‖ ≤ 1 := finiteSiteExtension_norm_le _ g hg u
    have hvalue (z) (t) : f (jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) = g (physical z t) := by
      rw [← hphysical z t]
      exact finiteSiteExtension_apply Subtype.val Subtype.val_injective g (physical z t)
    have heq := sampledSliceSeminorm_congr_values (pathLaw)
      (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) physical
      slices weights hsize hweights f g hvalue
    have hlarge' : α ≤ sampledSliceSeminorm (pathLaw)
        (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) slices weights f := by
      rw [heq, hαeq]
      exact hlarge
    obtain ⟨x, base, hbase, ψ, hψ, G, hG, hcorrelation⟩ :=
      allocatedOriginalPathLaw_niltest_native_detection B U b hb o hR hσ S poly hmem
        N hN hW hτ hξ stride cells hmass bases hbases htotal hM selection bW
        pI p0 pAccuracy w v E0 Dcap O pc gc Pτ family P e he hcover D V slices c step H hstep hslices
        p q hp hq hdense hdimension hcomplexity hcap f hf α hα hαone hmesh hthreshold
        hlarge' hbudget hnX hcost hdetectBudget hE hη (hcomparison f hf)
    refine ⟨⟨ψ, x, base, hbase, hψ⟩, G, hG, ?_⟩
    simpa only [f, finiteSiteExtension_apply Subtype.val Subtype.val_injective] using hcorrelation
  have hr (u : integerBox N) : 0 <
      (FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N)).weight u := by
    change 0 < (Fintype.card (integerBox N) : ℝ)⁻¹
    positivity
  exact exists_sampled_native_model (pathLaw) physical slices weights
    (FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N)) hr
    (fun _ : Fin nX => 1) (s + 1) qModel (fun u : integerBox N => u.val)
    (Subtype.val : twists → integerBox N → ℂ) htwists hK hC hcapInput (Real.exp_pos _) htau
    hsize hweights hdetector hexcess input hinput

end Erdos3.VectorPolynomial

end

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

theorem allocatedOriginalPathLaw_controlled_approximation
    (P : Polynomial ℕ) (u r : ℝ) (hu : 0 ≤ u) (hr : 0 ≤ r)
    (p : ℝ) (hpdef : p = allocatedModelTestLog u r)
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
    (hdense : ∀ z j, IsDenseCommonStrideBox sides p ((slices z j).image e))
    (hdimension : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) p)
    (hcomplexity : ∀ z j, (V z j).ComplexityLE (P.eval₂ (Nat.castRingHom ℝ) p))
    (hcap : ∀ z j, ((V z j).normBound : ℝ) ≤ 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp r)
    {budget E η Ptail : ℝ} (hbudget : 0 ≤ budget) (hnX : (nX : ℝ) ≤ budget)
    (hcost : allocatedCoarseNativeLog m (s + 2) pI p0 pAccuracy w v E0 Dcap O pc gc Pτ ≤ budget)
    (hdetectBudget : (p + p + sampledFullboxDetectionConstant s P) ^
      sampledFullboxDetectionConstant s P + 1 ≤ budget)
    (hE : (p + p + sampledFullboxDetectionConstant s P) ^
      sampledFullboxDetectionConstant s P + 5 ≤ E)
    (hη : η ≤ Real.exp (-((p + p + sampledFullboxDetectionConstant s P) ^
      sampledFullboxDetectionConstant s P + 5)))
    (hcomparison : ∀ f : (Fin nX → ℤ) → ℂ, (∀ u, ‖f u‖ ≤ 1) →
      ‖(pathLaw).complexMean (fun z =>
        𝔼 cube : SupportedCube (s + 2) (integerBox sides : Set (LayerSamplerVariables G I n B → ℤ)),
          physicalCubeSiteTest (integerSelfSiteTest (s + 2) f)
            (physicalCubeRootDifferences cube.val.2 cube.val.1 z.1.val z.2.val)) -
        (kernelLaw).goodPartBaseMean bases (GoodScalarKernelTuple selection (1 / (M : ℝ)) M)
          (fun x hx base => (family ⟨x, hx⟩ base).source hb o bW cells poly hmem widths f)‖ ≤
        2 * Real.exp (-E) + η)
    (physical : Path → T → integerBox N)
    (hphysical : ∀ z t, (physical z t).val = jointIntegerPhysicalSite (e t) (z.1.val, z.2.val))
    {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hKr : K ≤ Real.exp r) (hCr : C ≤ Real.exp r)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (hPtail : u + 2 * r + (budget + 2) ^ Classical.choose
      (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} (s + 1)) + 30 ≤ Ptail)
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N)
        (by let : ∀ i, NeZero (N i) := fun i => ⟨(hN i).ne'⟩; exact integerBox_nonempty N)).excessMass
      ((pathLaw).siteLaw physical) C ≤ 6 * positiveProjectionAccuracy Ptail)
    (input : integerBox N → ℂ) (hinput : ∀ u, ‖input u‖ ≤ Real.exp r) :
    let twists : Set (integerBox N → ℂ) :=
      {ψ | ∃ x : {x : G → IntegerScalarCubeBox (Fin (s + 2)) S.value // GoodScalarKernelTuple selection (1 / (M : ℝ)) M x}, ∃ base ∈ bases,
        ψ ∈ (family x base).twists hb o bW cells poly hmem}
    let qModel := (budget + 2) ^ Classical.choose
      (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} (s + 1))
    ∃ (nterms : ℕ) (_ : 0 < nterms) (Q : Fin nterms → (integerBox N → ℂ))
      (coeff : Fin nterms → ℝ) (err : integerBox N → ℂ),
      (∀ i, Q i ∈ twistedNativeSampleFunctions (fun _ : Fin nX => 1) (s + 1) qModel
        (fun u : integerBox N => u.val) (Subtype.val : twists → integerBox N → ℂ)) ∧
      input = (∑ i, coeff i • Q i) + err ∧
      (∑ i, |coeff i|) ≤ Real.exp (qModel + 2) ∧
      sampledSliceSeminorm (pathLaw) physical slices
        (fun z j t => star ((V z j).eval (commonStrideIndex (c z j) (step z j) (e t)))) err ≤
        Real.exp (-u) ∧
      (nterms : ℝ) ≤ Real.exp (2 * qModel + 2 * u + 4 * r + 30) := by
  intro twists qModel
  have hQ : 0 ≤ qModel := by dsimp only [qModel]; positivity
  obtain ⟨hα, hα1, _⟩ := allocatedModelUnitThreshold_bounds hu hr hK hC hKr hCr
  obtain ⟨hp, hmesh, hthreshold⟩ := allocatedModelTestLog_detection hu hr hK hC hKr hCr hvars
  rw [← hpdef] at hp hmesh hthreshold
  obtain ⟨nterms, hnterms, Q, coeff, err, hmodels, hdecomp, hcoeff, herr, hn⟩ :=
    allocatedOriginalPathLaw_native_approximation B U b hb o hR hσ S poly hmem
      N hN hW hτ hξ stride cells hmass bases hbases htotal hM selection bW
      pI p0 pAccuracy w v E0 Dcap O pc gc Pτ family P e he hcover D V slices c step H hstep hslices
      p p hp hp hdense hdimension hcomplexity hcap
      (allocatedModelUnitThreshold u r K C) hα hα1 hmesh hthreshold
      hbudget hnX hcost hdetectBudget hE hη hcomparison physical hphysical hK hC
      (Real.exp_pos r) (Real.exp_pos (-(u + 3))) hsize rfl hexcess input hinput
  have herror := allocated_native_approximation_error hu hr hQ hK (Real.exp_nonneg r)
    hKr le_rfl (le_refl (Real.exp (-(u + 3)))) hPtail
    (le_refl (6 * positiveProjectionAccuracy Ptail))
  have hbounds := allocatedModel_size_bounds hu hr hQ hK hC hKr hCr
  exact ⟨nterms, hnterms, Q, coeff, err, hmodels, hdecomp, hcoeff.trans hbounds.1,
    herr.trans herror, hn.trans hbounds.2⟩

end Erdos3.VectorPolynomial

end

end OAI

import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleUniversalMaskProductiveGood

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

noncomputable section

attribute [local irreducible] preparedSamplerTransverse preparedCommonBlockCount RankPreparationLayer.rank
attribute [local irreducible] PreparedFiniteScheduleDegreeModelsAtLaw integerBox allocatedPrincipalSides
attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

variable
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j)) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
    (bW : ∀ j, Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (stride : Fin nX → ℕ)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ))
    (gainLog gain : ℝ) (Q : ℕ)
    (e : Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (law : (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1))
    (N : Fin nX → ℕ) (test : (Fin nX → ℝ) → ℝ)
    [IsProbabilityMeasure μ]
    (hweight : ∀ z, Measurable (fun center => (law center).weight z))
    (hgood : PreparedCenteredShortForecastGoodConclusion (m := m) (nX := nX) (M := M)
      prep U b S bW hb o hR hσ μ poly hm stride width bases gainLog gain Q e law)
    (hproductive : PreparedCenteredForecastProductiveConclusion (nX := nX) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S
      hb o hR hσ μ poly hm N width bases gainLog law)
    (htest : ∀ x, |test x| ≤ 1) (hgain : Real.exp (-gainLog) ≤ gain)
    (hmean : gain ≤ 𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ)))

local instance allNilmanifoldContinuousDecidableEq (j : Fin m) : DecidableEq (PreparedSamplerContinuous prep j) := Classical.decEq _
local instance allNilmanifoldBlockDecidableEq (a : LayerSamplerAxis (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)) :
    DecidableEq (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)) a) :=
  Classical.decEq _

variable
    (Pdetect : Polynomial ℕ) (hbox : (integerBox N).Nonempty)
    (physical : (bases × rectangularWeightIndices 0 width 1) → integerBox (Sum.elim (fun _ : (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) => S.value)
      (allocatedPrincipalSides (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S)) → integerBox N)
variable
    {Stage : Type} [Fintype Stage]
    (degree : Stage → ℕ) (u p cap sliceLog testLog budget E : Stage → ℝ)
variable
    (hModel : ∀ k : Stage, PreparedFiniteScheduleDegreeModelsAtLaw
      (m := m) (nX := nX) (R := R) (σ := σ)
      (Path := bases × rectangularWeightIndices 0 width 1) (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j))
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S N Pdetect μ poly hbox law hweight
      physical (degree k) (u k) (p k) (cap k) (sliceLog k) (testLog k) (budget k) (E k))
variable
    (hSliceLog : ∀ k, 0 ≤ sliceLog k)
    (hDetectorBudget : ∀ k, 2 ≤ Pdetect.eval₂ (Nat.castRingHom ℝ) (testLog k))
    (hnum : ∀ k, (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) : ℝ) ≤
      Pdetect.eval₂ (Nat.castRingHom ℝ) (testLog k))
variable
    {Forecast : Stage → Type} [∀ k, Nonempty (Forecast k)]
    (Pnative massLog capLog Edata : Stage → ℝ)
    (data : ∀ k, Forecast k → ActualForecastData N poly (Pnative k) (massLog k) (capLog k) (Edata k))
variable
    (hNative : ∀ k, 0 ≤ Pnative k)
    (hAccuracy : ∀ k, 2 * u k + 4 * p k + 12 ≤ Edata k)
    (hCap : ∀ k, Real.exp (capLog k) ≤ cap k)
    (hPrecision : ∀ k, actualForecastDataModelRequired (budget k) (Pnative k) (massLog k)
      (u k) (p k) ≤ E k)
variable
    {History : Stage → Type} [∀ k, Fintype (History k)]
    {Freq Bin Y : ∀ k, History k → Type}
    [∀ k h, Fintype (Freq k h)] [∀ k h, Fintype (Bin k h)]
    (F : ∀ k h, Freq k h → integerBox N → Y k h → ℂ)
    (netCenters : ∀ k h, Freq k h → Bin k h → Y k h → ℂ)
    {ε : ∀ k, History k → ℝ}
    (hnet : ∀ k h f x, ∃ i, ∀ y, ‖F k h f x y - netCenters k h f i y‖ ≤ ε k h)
variable
    (a : integerBox N → ℝ) (inputCap : ℝ)
    (ha : ∀ x, |a x| ≤ Real.exp inputCap)
    (hInputCap : ∀ k, inputCap ≤ p k)
variable
    (historyLog frequencyLog binLog Eres : Stage → ℝ) (stageLog : ℝ)
    (hHistory : ∀ k, (Fintype.card (History k) : ℝ) ≤ Real.exp (historyLog k))
    (hFrequency : ∀ k h, (Fintype.card (Freq k h) : ℝ) ≤ Real.exp (frequencyLog k))
    (hBin : ∀ k h, (Fintype.card (Bin k h) : ℝ) ≤ Real.exp (binLog k))
    (hStageCount : (Fintype.card Stage : ℝ) + 1 ≤ Real.exp stageLog)
    (hErrorBudget : ∀ k, historyLog k + frequencyLog k + binLog k + gainLog +
      Eres k + stageLog + 6 ≤ u k)

include hgood hproductive htest hgain hmean hModel hSliceLog hDetectorBudget hnum
  hNative hAccuracy hCap hPrecision ha hInputCap hHistory hFrequency hBin
  hStageCount hErrorBudget in

theorem exists_preparedFiniteScheduleAllNilmanifoldMaskProductiveGood :
    let input : ∀ k, ExternalHistoryMaskIndex (Freq k) (Bin k) → integerBox N → ℂ :=
      fun k => externalHistoryMaskFamily (F k) (netCenters k) (hnet k)
        (fun x => (a x : ℂ))
    let Packet := fun k => UniversalLocalMajorSliceTest
      (Sum.elim (fun _ : EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)) => S.value)
        (allocatedPrincipalSides (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S))
      (degree k) (sliceLog k) (Pdetect.eval₂ (Nat.castRingHom ℝ) (testLog k))
    let commonBudget := fun k => max (budget k) (3 * Pnative k + 3)
    let Qmodel := fun k => max (commonBudget k) (2 * u k + 4 * p k + max 0 (massLog k) + 20)
    let native := fun k => twistedNativeSampleFunctions (1 : Fin nX → ℕ) (degree k) (commonBudget k)
      (fun v : integerBox N => v.val)
      (fun (W : NormalizedPolynomialTwist (Fin nX) (Σ j, (fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)
        (Real.exp (commonBudget k)) (Real.exp (commonBudget k))
        ⟨Real.exp (commonBudget k), Real.exp_nonneg _⟩)
        (v : integerBox N) => W.eval N poly v.val)
    let localSeminorm : Stage → (integerBox N → ℂ) → ℝ := fun k =>
      sampledSliceSeminorm (centeredFiniteMarginal μ law hweight) physical
        (fun _ (j : Packet k) => j.slice.subtypeSites)
        (fun _ (j : Packet k) t => j.weight t.val)
    let selectedLocal : Stage → (integerBox N → ℂ) →
        (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U × (bases × rectangularWeightIndices 0 width 1) → ℂ) → Prop :=
      fun k err errLocal => ∀ center z, ∃ j : Packet k, errLocal (center, z) =
        𝔼 t ∈ j.slice.subtypeSites, err (physical z t) * j.weight t.val
    ∃ models : ∀ k, ExternalHistoryMaskIndex (Freq k) (Bin k) → CenteredForecastModel (integerBox N),
      (∀ k branch, CenteredForecastModelBounds (centeredFiniteProbabilityMeasure μ law)
        (native k) (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox)
        (fun f => (data k f).target) (localSeminorm k) (selectedLocal k) (input k branch)
        (Real.exp (Qmodel k + 2)) (Real.exp (-u k))
        (Real.exp (2 * Qmodel k + 2 * u k + 4 * p k + 34)) (models k branch)) ∧
      PreparedCenteredStagedModelProductiveGoodConclusion (m := m) (nX := nX) (M := M)
        prep U b S bW hb o hR hσ μ poly hm stride width bases gainLog gain Q e law N test
        physical (fun k _ (j : Packet k) => j.slice.subtypeSites)
        (fun k _ (j : Packet k) t => j.weight t.val) models Eres := by
  intro input Packet commonBudget Qmodel native localSeminorm selectedLocal
  let sides := Sum.elim
    (fun _ : EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)) => S.value)
    (allocatedPrincipalSides (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S)
  have hSides (i : LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) :
      0 < sides i := by
    cases i with
    | inl g => exact S.positive
    | inr j =>
      exact allocatedPrincipalSides_pos
        (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S j
  let : ∀ k, Nonempty (Packet k) := fun k => UniversalLocalMajorSliceTest.nonempty sides hSides
    (degree k) (sliceLog k) (Pdetect.eval₂ (Nat.castRingHom ℝ) (testLog k))
    (hSliceLog k) (hDetectorBudget k)
  have hmodels := exists_preparedFiniteScheduleExternalMaskProductiveGood
    (prep := prep) (U := U) (b := b) (S := S) (bW := bW) (hb := hb) (o := o)
    (hR := hR) (hσ := hσ) (μ := μ) (poly := poly) (hm := hm) (stride := stride)
    (width := width) (bases := bases) (gainLog := gainLog) (gain := gain) (Q := Q)
    (e := e) (law := law) (N := N) (test := test) (hweight := hweight)
    (hgood := hgood) (hproductive := hproductive) (htest := htest) (hgain := hgain) (hmean := hmean)
    (Pdetect := Pdetect) (hbox := hbox) (physical := physical)
    (degree := degree) (u := u) (p := p) (cap := cap) (sliceLog := sliceLog)
    (testLog := testLog) (budget := budget) (E := E) (hModel := hModel)
    (Tests := fun k _ => Packet k)
    (Ldetect := fun k _ j => j.nativeModel.L) (dims := fun k _ j => j.nativeModel.dim)
    (Ddetect := fun k _ j => j.nativeModel.model) (Vdetect := fun k _ j => j.nativeModel.test)
    (slices := fun k _ j => j.slice.subtypeSites)
    (cdetect := fun k _ j i => (j.slice.start i : ℤ))
    (stepdetect := fun k _ j => j.stride) (Hdetect := fun k _ j => j.slice.length)
    (hstep := fun k _ j => j.stride_pos)
    (hSlices := fun k _ j => j.slice.subtypeSites_image_val.trans j.slice.integerPoints_eq_commonStrideBox)
    (hDense := fun k _ j => j.slice.subtypeSites_dense j.dense) (hnum := hnum)
    (hcomplex := fun k _ j => j.nativeModel.complexity)
    (hcap := fun k _ j => by exact_mod_cast j.nativeModel.norm)
    (Pnative := Pnative) (massLog := massLog) (capLog := capLog) (Edata := Edata)
    (data := data) (hNative := hNative) (hAccuracy := hAccuracy) (hCap := hCap)
    (hPrecision := hPrecision) (F := F) (netCenters := netCenters) (hnet := hnet)
    (a := a) (inputCap := inputCap) (ha := ha) (hInputCap := hInputCap)
    (historyLog := historyLog) (frequencyLog := frequencyLog) (binLog := binLog)
    (hHistory := hHistory) (hFrequency := hFrequency) (hBin := hBin) (Eres := Eres)
    (stageLog := stageLog) (hStageCount := hStageCount) (hErrorBudget := hErrorBudget)
  simpa only [localSeminorm, selectedLocal, UniversalLocalMajorSliceTest.weight_eq_native_eval] using hmodels

end

end Erdos3.VectorPolynomial

end

end OAI

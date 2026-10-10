import OAI.Combinatorics.Progressions.Polynomial.PreparedFiniteForwardPrescribedDegreeProductiveSource

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem exists_preparedFiniteForwardPaddedProductiveSource
    {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m) (depth : ℕ)
    [∀ j : Fin (max m depth), DecidableEq (RankPreparationLayer.Coord ((prep.pad (max m depth)) j))]
    (U : ∀ j, Submodule ℝ ((fun j : Fin (max m depth) => RankPreparationLayer.Coord ((prep.pad (max m depth)) j)) j → ℝ))
    (b : ∀ j, Basis (Fin ((preparedSamplerTransverse (prep.pad (max m depth))) j)) ℝ (euclideanSubspace (U j))ᗮ)
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
    (Vtail : Fin (max m depth) → ℝ≥0)

    (Q : Fin (max m depth) → Type) [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis ((PreparedSamplerContinuous (prep.pad (max m depth))) j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin (max m depth) => RankPreparationLayer.Coord ((prep.pad (max m depth)) j)) j)) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin (max m depth) => RankPreparationLayer.Coord ((prep.pad (max m depth)) j)) j)) (euclideanSubspace (U j)))]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice ((fun j : Fin (max m depth) => RankPreparationLayer.Coord ((prep.pad (max m depth)) j)) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel (max m depth) (modularInitialBlockCount (max m depth) (nX + (max m depth) * M))) (PreparedSamplerContinuous (prep.pad (max m depth))) (preparedSamplerTransverse (prep.pad (max m depth))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m depth)) (modularInitialBlockCount (max m depth) (nX + (max m depth) * M)))) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel (max m depth) (modularInitialBlockCount (max m depth) (nX + (max m depth) * M))) (PreparedSamplerContinuous (prep.pad (max m depth))) (preparedSamplerTransverse (prep.pad (max m depth))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m depth)) (modularInitialBlockCount (max m depth) (nX + (max m depth) * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel (max m depth) (modularInitialBlockCount (max m depth) (nX + (max m depth) * M))) (PreparedSamplerContinuous (prep.pad (max m depth))) (preparedSamplerTransverse (prep.pad (max m depth))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m depth)) (modularInitialBlockCount (max m depth) (nX + (max m depth) * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel (max m depth) (modularInitialBlockCount (max m depth) (nX + (max m depth) * M))) (PreparedSamplerContinuous (prep.pad (max m depth))) (preparedSamplerTransverse (prep.pad (max m depth))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m depth)) (modularInitialBlockCount (max m depth) (nX + (max m depth) * M)))) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
    [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
    [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
    [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]

    (A Cslice Cdirect : ℕ) (stageCountConstant : ℕ → ℕ)
    (hA : 2 ≤ A) (hSliceExponent : Cslice + 1 ≤ A)
    (Bstruct Qstride forecastCap stageLog : ℝ)
    (Qσ Qw Pmin requestedCoarse gainLog gain Vlog : ℝ)
    (Lmin Qgood : ℕ)
    (hm : 0 < m) (hnX : 0 < nX)
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hB : 0 ≤ Bstruct) (hstage : stageLog ∈ Set.Icc 0 Bstruct)
    (hQstride : 0 ≤ Qstride)
    (hQσ : 0 ≤ Qσ) (hQw : 0 ≤ Qw) (hPmin : 0 ≤ Pmin)
    (hLmin : (Lmin : ℝ) ≤ Real.exp Pmin)
    (hg : 0 ≤ gainLog) (hVlog : 0 ≤ Vlog)
    (hQgood : 1 ≤ Qgood) (hQexp : (Qgood : ℝ) ≤ Real.exp Vlog)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hnChart : (nX : ℝ) ≤ Bstruct) (hgChart : gainLog ≤ Bstruct) :
    let K := PreparedFiniteForwardSlot depth
    let degree : K → ℕ := preparedFiniteForwardTerminalDegree
    let Cdetect := fun k : K => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
    let kModel : K := preparedFiniteForwardModelSlot 0
    let sourceU := fun k : K =>
      preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant k.1.val k.2 Bstruct gainLog stageLog
    let modelLog := fun k : K => preparedFiniteForwardWork A stageCountConstant k.1.val Bstruct
    let sliceLog := fun k : K =>
      (preparedFiniteForwardParameter A stageCountConstant k.1.val Bstruct + Cslice) ^ Cslice
    let u := preparedFiniteForwardModelPrecision A stageCountConstant 0 Bstruct gainLog stageLog
    let p := preparedFiniteForwardWork A stageCountConstant 0 Bstruct
    let pnum : ℝ := enlargedPreparedCommonSamplerDimension (max m depth) M (modularInitialBlockCount (max m depth) (nX + (max m depth) * M))
    let R : Fin (max m depth) → ℝ := fun _ => allocatedCommonProductRadius (max m depth) Bstruct Bstruct
    let pRadius := allocatedCommonProductRadiusLog (max m depth) Bstruct Bstruct
    let D := allocatedComparisonDimension (max m depth) pnum
    let pDetect := fun k => allocatedModelTestLog (sourceU k) (modelLog k)
    let aDetect := fun k => 2 * sourceU k + 4 * modelLog k + 7
    let detectionGain := fun s : K => slicedDetectionGainLog (degree s) (Cdetect s)
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m depth) (modularInitialBlockCount (max m depth) (nX + (max m depth) * M))) (PreparedSamplerContinuous (prep.pad (max m depth))) (preparedSamplerTransverse (prep.pad (max m depth))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m depth)) (modularInitialBlockCount (max m depth) (nX + (max m depth) * M))))) (pDetect s) (pDetect s) (aDetect s)
    let Pk := fun s : K => scalarKernelLogarithmicBudget (Fin ((degree s) + 1)) (EnlargedPreparedCommonKernel (max m depth) (modularInitialBlockCount (max m depth) (nX + (max m depth) * M)))
      (detectionGain s + pDetect s + 4)
    let Pphysical := fun k : K => preparedFiniteScheduleLocalPhysical (max m depth) nX
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m depth) (modularInitialBlockCount (max m depth) (nX + (max m depth) * M))) (PreparedSamplerContinuous (prep.pad (max m depth))) (preparedSamplerTransverse (prep.pad (max m depth))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m depth)) (modularInitialBlockCount (max m depth) (nX + (max m depth) * M))))) Qstride (Pk k)
    let target := fun k => detectionGain k + 40 + coefficientErrorSpatialLog (Pphysical k)
    let E := fun s : K => target s + D * (((max m depth) * 2 ^ ((max m depth) + 1) : ℕ) * Pk s) + 5
    let Prho := fun s : K => 2 * affineProfileInputEnvelope D
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2) + 2
    let Ptail := fun s : K => affineProfileToleranceEnvelope (max m depth) D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2)
    let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
    let Tmod := fun s : K => (((max m depth) + 1 : ℕ) : ℝ) * Pk s + nX * Qstride
    let lengthLogs := fun s : K => allocatedAffineLengthLog (max m depth) D Pscale (Prho s) (Pk s)
      (target s) (pDetect s + 2) (Tmod s)
    let Pseed := allocatedScaleLog (Pscale + ∑ s, lengthLogs s + Pmin + 1)
    let W := physicalBadProductGap ((modularInitialBlockCount (max m depth) (nX + (max m depth) * M)) * (nX + (max m depth) * M)) (gainLog + 8) Vlog Qgood
    let Pmaster := fun k : K => preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride
      (Pphysical k) (sourceU k) (modelLog k) (Prho k) (target k) (detectionGain k)
    let coarseTarget := preparedFiniteScheduleDirectCoarse detectionGain requestedCoarse
    let Plate := ∑ k : K, preparedUniformDegreeDirectLate (Pmaster k) Pscale
      (Pphysical k) coarseTarget (allocatedWitnessScaleLog Pseed Qw)
    let τ := Real.exp (-(gainLog + (nX : ℝ) + 8))
    pnum ≤ Bstruct →
    W ≤ Real.exp Qw →
    (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous (prep.pad (max m depth))) j)) ((preparedSamplerTransverse (prep.pad (max m depth))) j) (R j) (Vtail j)) ≤ Real.exp p →
    0 ≤ forecastCap → forecastCap ≤ Real.exp p →
    ∃ (hR : ∀ j, 0 < R j) (σ : ℝ) (hσ : 0 < σ)
      (S : LayerSamplerScale («G» := (EnlargedPreparedCommonKernel (max m depth) (modularInitialBlockCount (max m depth) (nX + (max m depth) * M)))) («I» := (PreparedSamplerContinuous (prep.pad (max m depth)))) («n» := (preparedSamplerTransverse (prep.pad (max m depth)))) («J» := (fun j : Fin (max m depth) => RankPreparationLayer.Coord ((prep.pad (max m depth)) j))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m depth)) (modularInitialBlockCount (max m depth) (nX + (max m depth) * M))) U b R (fun _ => σ)),
      0 ≤ pRadius ∧ (∀ j, R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      σ ≤ 1 ∧ σ ≤ Real.exp (-Qσ) ∧ σ⁻¹ ≤ Real.exp Pscale ∧
      Lmin ≤ S.value ∧ (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog Pseed Qw) ∧
      (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
        8 * (probabilityProfileLipschitz : ℝ) * W ≤
          (layerSamplerGapWidth («G» := (EnlargedPreparedCommonKernel (max m depth) (modularInitialBlockCount (max m depth) (nX + (max m depth) * M)))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m depth)) (modularInitialBlockCount (max m depth) (nX + (max m depth) * M))) R ⟨j, i⟩ / 2) *
            ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
      (∀ s : K, PreparedUniformDegreeGeometryAt («G» := (EnlargedPreparedCommonKernel (max m depth) (modularInitialBlockCount (max m depth) (nX + (max m depth) * M)))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m depth)) (modularInitialBlockCount (max m depth) (nX + (max m depth) * M))) U b S (degree s) (Cdetect s) nX
        Bstruct Pscale D (target s) (Pk s) (Prho s) Qstride (pDetect s) pRadius (aDetect s) (detectionGain s)) ∧
      (∀ k, PreparedUniformDegreeDirectScalarBounds (max m depth) (degree k) nX
        (Fintype.card (LayerSamplerVariables
          (EnlargedPreparedCommonKernel (max m depth) (modularInitialBlockCount (max m depth) (nX + (max m depth) * M)))
          (PreparedSamplerContinuous (prep.pad (max m depth))) (preparedSamplerTransverse (prep.pad (max m depth)))
          (EnlargedPreparedCommonSamplerBlock (prep.pad (max m depth)) (modularInitialBlockCount (max m depth) (nX + (max m depth) * M)))))
        (Cdetect k) Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (Pmaster k) Plate
        (detectionGain k) (Pphysical k) coarseTarget pRadius (sourceU k) (modelLog k) (sliceLog k)) ∧
      (∀ k, PreparedScheduledDirectSourceAvailability
          (B := EnlargedPreparedCommonSamplerBlock (prep.pad (max m depth)) (modularInitialBlockCount (max m depth) (nX + (max m depth) * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection (max m depth)
            (modularInitialBlockCount (max m depth) (nX + (max m depth) * M)) (degree k) (preparedFiniteForwardTerminalDegree_le (Nat.le_max_right m depth) k))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) ∧
      (∀ k, PreparedScheduledDegreeModelAvailability
          (B := EnlargedPreparedCommonSamplerBlock (prep.pad (max m depth)) (modularInitialBlockCount (max m depth) (nX + (max m depth) * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection (max m depth)
            (modularInitialBlockCount (max m depth) (nX + (max m depth) * M)) (degree k)
              (preparedFiniteForwardTerminalDegree_le (Nat.le_max_right m depth) k))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o) (μ := μ)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) ∧
      PreparedUniformDegreeProductiveSourceConclusion
        (m := (max m depth)) (nX := nX) (M := M) (prep := (prep.pad (max m depth))) (U := U) (b := b) (S := S)
        (hR := hR) (hσ := fun _ => hσ) (stride := stride) (N := N)
        (Pdetect := Pdetect) (pModel := modelLog kModel) (pSlice := sliceLog kModel)
        (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
        (hb := hb) (o := o) (bW := bW) (μ := μ)
        Bstruct Qstride (Pmaster kModel) Plate (detectionGain kModel) (Pphysical kModel) coarseTarget
        pRadius Pscale Pseed Qw gainLog gain Vlog Qgood := by
  exact exists_preparedFiniteForwardPrescribedDegreeProductiveSource
    (m := max m depth) (nX := nX) (M := M) (prep.pad (max m depth)) U b stride N Pdetect Vtail
    Q hb o bW ν μ μrows depth A Cslice Cdirect stageCountConstant
    preparedFiniteForwardTerminalDegree
    (preparedFiniteForwardTerminalDegree_le (Nat.le_max_right m depth))
    (preparedFiniteForwardTerminalDegree_anchor depth)
    (Nat.le_max_right m depth) hA hSliceExponent
    Bstruct Qstride forecastCap stageLog Qσ Qw Pmin requestedCoarse gainLog gain Vlog
    Lmin Qgood (hm.trans_le (Nat.le_max_left m depth)) hnX
    (prep.pad_coordinate_card_le hCoord)
    hB hstage hQstride hQσ hQw hPmin hLmin hg hVlog hQgood hQexp hgain hnChart hgChart

end Erdos3.VectorPolynomial

end

end OAI

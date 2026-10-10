import OAI.Combinatorics.Progressions.Sampling.PreparedProductiveGoodForecastSource

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem preparedShortForecastSourceModelAttachment
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale
      (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j => RankPreparationLayer.Coord (prep j))
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    (selection : Fin (0 + 1) ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ)
    (Vtail : Fin m → ℝ≥0) (τ u p forecastCap : ℝ)
    {Q : Fin m → Type} [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection
      (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [IsProbabilityMeasure μ]
    [μ.IsAddLeftInvariant]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j)))
        (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (baseB0 Vlog gainLog gain Pwidth : ℝ) (Qgood : ℕ)
    (spatialEmbedding : Fin 2 × Fin nX ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))))
    {D : ℝ}
    (H : PreparedShortForecastSourceRawBounds (m := m) (nX := nX) (M := M)
      (prep := prep) (U := U) (b := b) (S := S)
      (selection := selection) (Pdetect := Pdetect) (uSource := uSource)
      (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
      (u := u) (p := p) (forecastCap := forecastCap)
      Pchart Qstride Pmaster Plate Pphysical coarseTarget
      baseB0 Vlog gainLog gain Pwidth Qgood D)
    (hModel : PreparedCenteredForecastModelInterface
      (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j)))
      (B := (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (U := U) (basis := b) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget) :
    let Bcert := preparedForecastGoodCertificateBudget baseB0 Pchart Pwidth gainLog Vlog
    let Pgood := preparedForecastGoodAnalyticBudget
      (preparedCenteredShortForecastSpatialExponent m) baseB0 Pchart Pwidth gainLog Vlog
    PreparedCenteredShortForecastGoodModelInterface (m := m) (nX := nX) (M := M)
      (prep := prep) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (bW := bW) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
      Bcert gainLog gain Pgood Qgood spatialEmbedding := by
  intro Bcert Pgood
  exact preparedCenteredShortForecastGoodModelInterface_of_model
    (m := m) (nX := nX) (M := M) (X₀ := X₀) (J₀ := J₀)
    (prep := prep) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
    (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
    (hb := hb) (o := o) (bW := bW) (μ := μ) (ν := ν)
    Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
    Bcert Vlog gainLog gain Pwidth Pchart Pgood Qgood spatialEmbedding
    (D := D) (preparedShortForecastSourceRawBounds_to_good
      (m := m) (nX := nX) (M := M) prep U b S selection
      Pdetect uSource pModel pSlice Vtail u p forecastCap
      Pchart Qstride Pmaster Plate Pphysical coarseTarget
      baseB0 Vlog gainLog gain Pwidth Qgood D H) hModel

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem preparedShortForecastProductiveModelAttachment
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale
      (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j => RankPreparationLayer.Coord (prep j))
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    (selection : Fin (0 + 1) ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ)
    (Vtail : Fin m → ℝ≥0) (τ u p forecastCap : ℝ)
    {Q : Fin m → Type} [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection
      (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [IsProbabilityMeasure μ]
    [μ.IsAddLeftInvariant]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j)))
        (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (baseB0 Vlog gainLog gain Pwidth : ℝ) (Qgood : ℕ)
    (spatialEmbedding : Fin 2 × Fin nX ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))))
    {D : ℝ}
    (H : PreparedShortForecastSourceRawBounds (m := m) (nX := nX) (M := M)
      (prep := prep) (U := U) (b := b) (S := S)
      (selection := selection) (Pdetect := Pdetect) (uSource := uSource)
      (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
      (u := u) (p := p) (forecastCap := forecastCap)
      Pchart Qstride Pmaster Plate Pphysical coarseTarget
      baseB0 Vlog gainLog gain Pwidth Qgood D)
    (hchartMaster : Pchart ≤ Pmaster) (hstrideMaster : Qstride ≤ Pmaster)
    (hGainMaster : gainLog + (nX : ℝ) + 8 ≤ Pmaster)
    (hτeq : τ = Real.exp (-(gainLog + (nX : ℝ) + 8)))
    (hξLate : (normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) selection
      (allocatedDetectedKernelCutoff 0 (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
        (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
        Pdetect (allocatedModelTestLog uSource pModel) (allocatedModelTestLog uSource pModel) ((forecastAugmentedUnitThreshold u p (Real.exp (pSlice * Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))) (max 1 (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous prep) j)) ((preparedSamplerTransverse prep) j) (R j) (Vtail j))) forecastCap) / 2)) Pphysical coarseTarget)⁻¹ ≤ Real.exp Plate)
    (hModel : PreparedCenteredForecastModelInterface
      (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j)))
      (B := (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (U := U) (basis := b) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget) :
    let Bcert := preparedForecastGoodCertificateBudget baseB0 Pchart Pwidth gainLog Vlog
    let Pgood := preparedForecastGoodAnalyticBudget
      (preparedCenteredShortForecastSpatialExponent m) baseB0 Pchart Pwidth gainLog Vlog
    PreparedCenteredShortForecastProductiveGoodModelInterface (m := m) (nX := nX) (M := M)
      (prep := prep) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (bW := bW) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
      Bcert gainLog gain Pgood Qgood spatialEmbedding (4 * (Plate + 8) ^ 2) := by
  intro Bcert Pgood
  have hGood := preparedShortForecastSourceModelAttachment
    (m := m) (nX := nX) (M := M) (X₀ := X₀) (J₀ := J₀)
    (prep := prep) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
    (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
    (hb := hb) (o := o) (bW := bW) (μ := μ) (ν := ν)
    Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
    baseB0 Vlog gainLog gain Pwidth Qgood spatialEmbedding (D := D) H hModel
  have hBounds : PreparedCenteredForecastProductiveBounds
      prep U b S selection Pdetect uSource pModel pSlice Vtail τ u p forecastCap
      Pchart Qstride Pmaster Plate Pphysical coarseTarget gainLog (4 * (Plate + 8) ^ 2) D := {
    hnX := H.hnX
    hσ1 := H.hσ1
    hsmall := H.hsmall
    hMaster := H.hMaster
    hLate := H.hLate
    hd := H.hd
    hD := H.hD
    hnMaster := H.hnMaster
    hRi := H.hRi
    hσi := H.hσi
    hS := H.hS
    hchartMaster := hchartMaster
    hstrideMaster := hstrideMaster
    hProd := le_rfl
    hg := H.hg
    hGainMaster := hGainMaster
    hτeq := hτeq
    hξLate := hξLate }
  exact preparedCenteredShortForecastProductiveGoodModelInterface_of_goodModel
    (m := m) (nX := nX) (M := M) (X₀ := X₀) (J₀ := J₀)
    (prep := prep) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
    (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
    (hb := hb) (o := o) (bW := bW) (μ := μ) (ν := ν)
    Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
    Bcert gainLog gain Pgood Qgood spatialEmbedding (4 * (Plate + 8) ^ 2)
    (D := D) hBounds hGood

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
attribute [local irreducible] PreparedShortCertifiedSameScaleBadProductInterface
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

def PreparedShortGoodForecastSourceStatement (m : ℕ) (Pdetect : Polynomial ℕ) : Prop :=
    let Cdetect := sampledSupportedSlicedDetectionConstant 0 Pdetect
    let Aearly := Classical.choose (exists_preparedModularGeneralCanonicalEarlyParameters m 0 Cdetect)
    let Aalloc := Classical.choose (exists_preparedModularCanonicalDetectorAllocationBudget m)
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {X J₀ : Type} (L : RankPreparationFamily X J₀ m) {M nX : ℕ},
      (∀ j, Fintype.card (L j).Coord ≤ M) →
      ∀ {Pstruct pSlice Qstride g₀ : ℝ},
      0 < m → 0 ≤ Pstruct → (M : ℝ) ≤ Pstruct →
      pSlice ∈ Set.Icc 0 Pstruct → Qstride ∈ Set.Icc 0 Pstruct → (nX : ℝ) ≤ Pstruct → 0 < nX → 0 ≤ g₀ → g₀ ≤ Pstruct →
      let Jalloc := modularInitialBlockCount m (nX + m * M)
      let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M Jalloc
      let Bstruct := (Pstruct + Aalloc) ^ Aalloc
      let G := EnlargedPreparedCommonKernel m Jalloc
      let I := PreparedSamplerContinuous L
      let n := preparedSamplerTransverse L
      let B := EnlargedPreparedCommonSamplerBlock L Jalloc
      let selection := enlargedPreparedCommonCanonicalSelection m Jalloc 0 (Nat.zero_le m)
    let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let radiusBudget := Bstruct + (2 * Bstruct + A) ^ A + 2
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)
      let T := allocatedIdealCoverSupport (G := G) B rowSets
      let siteRadius := allocatedProductIdealSiteRadius (G := G) B rowSets
      let D := allocatedComparisonDimension m pnum
      ∃ (pRadius : ℝ) (R : Fin m → ℝ),
      pRadius ∈ Set.Icc 0 radiusBudget ∧
      (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      1 ≤ siteRadius ∧ (∀ j, 0 ≤ T j) ∧
      (∀ j, partitionedIdealRadius (Fin (0 + 1)) m + 1 ≤ T j) ∧
      (∀ j, (Fintype.card (BoundedCoefficientExponent
        (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
          ((2 : ℝ) ^ Fintype.card (Fin (0 + 1)) *
            ((Fintype.card (Fin (0 + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j) ∧
      (∀ j, (rowSets j).card * T j ≤ (siteRadius : ℝ)) ∧
      (∀ j, T j ≤ Real.exp pRadius) ∧ 2 * (siteRadius : ℝ) ≤ Real.exp pRadius ∧
      (∀ Cchart : Fin m → ℝ, (∀ j, 0 ≤ Cchart j) → (∀ j, Cchart j ≤ Real.exp Bstruct) →
        (∀ j, Cchart j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) ∧
        (∀ j, Cchart j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
        (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin (0 + 1))) *
          (Cchart j * (((Fintype.card (I j) : ℝ) + 1) *
            (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4)) ∧
      AllocatedComparisonDimensions (G := G) B (Fin (0 + 1)) (fun j => (rowSets j : Type)) D ∧
      ∀ {uModel pForecast P : ℝ}, 0 ≤ uModel → 0 ≤ pForecast →
      allocatedEarlyModelLog radiusBudget pSlice (Fintype.card (LayerSamplerVariables G I n B)) ≤ pForecast →
      Bstruct + (uModel + 2 * pForecast + 1) ≤ P →
      let u := uModel + 2 * pForecast + 1
      let Pearly := P + (2 * P + A) ^ A + 2
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let gainLog := slicedDetectionGainLog 0 Cdetect (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let Pk := scalarKernelLogarithmicBudget (Fin (0 + 1)) G (gainLog + pDetect + 4)
      let Qearly := (P + Aearly) ^ Aearly
      let Pphysical := Qearly + Pk + Qstride + nX + (m + 1 : ℕ) + 8
      let Eextra := coefficientErrorSpatialLog Pphysical + 8
      let target := gainLog + 32 + Eextra
      let F := pDetect + 2
      let Tmod := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
      let _δ := Real.exp (-(pDetect + 1))
      let E := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let _η := Real.exp (-E)
      let Prho := 2 * affineProfileInputEnvelope D (canonicalSublevelCutoffLip : ℝ)
        (canonicalTransitionLip : ℝ) E F + 2
      let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F
      let _K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
      let budget := (P + Eextra + C) ^ C
      let master := budget + Pphysical + Pearly + gainLog + 32
      pRadius ≤ budget ∧ (∀ j, T j ≤ Real.exp budget) ∧
      2 * (siteRadius : ℝ) ≤ Real.exp budget ∧ radiusBudget ≤ Pearly ∧
      P ≤ Pearly ∧ Pearly ≤ budget ∧ pModel ∈ Set.Icc 0 budget ∧ pDetect ∈ Set.Icc 0 budget ∧
      aDetect ∈ Set.Icc 0 budget ∧ target ∈ Set.Icc 0 budget ∧ D ∈ Set.Icc 0 budget ∧ gainLog ∈ Set.Icc 0 budget ∧ Pk ∈ Set.Icc 0 budget ∧
      Prho ∈ Set.Icc 0 budget ∧ Ptail ∈ Set.Icc 0 budget ∧ Tmod ∈ Set.Icc 0 budget ∧
      g₀ + (nX : ℝ) + 8 ≤ Pphysical ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      t⁻¹ ≤ Real.exp Ptail ∧ t⁻¹ ≤ Real.exp budget ∧
      ∀ {Ppert Epert : ℝ}, 0 ≤ Ppert → 0 ≤ Epert →
      let Qσ := fixedPathPerturbationLog D (D + Ppert + 4) Epert m
      let σ := min t (Real.exp (-Qσ))
      let Pscale := pRadius + Ptail + Qσ
      let lengthLog := allocatedAffineLengthLog m D Pscale Prho Pk target F Tmod
      let Pseed := allocatedScaleLog (D + Pscale + lengthLog + 1)
      0 < σ ∧ σ ≤ t ∧ σ ≤ Real.exp (-Qσ) ∧
      σ⁻¹ ≤ Real.exp Pscale ∧ Pscale ∈ Set.Icc 0 (2 * budget + Qσ) ∧
      ∀ (Lmin : ℕ) {Pmin Vlog : ℝ} (Qbad : ℕ),
        0 ≤ Pmin → (Lmin : ℝ) ≤ Real.exp Pmin →
        0 ≤ Vlog → 1 ≤ Qbad → (Qbad : ℝ) ≤ Real.exp Vlog →
      let Elog := g₀ + 8
      let W := physicalBadProductGap (Jalloc * (nX + m * M)) Elog Vlog Qbad
      let Qw := 2 * Bstruct + 2 * Vlog + 5 * Elog + 24
      let J := fun j : Fin m => (L j).Coord
      let Pbase := Bstruct + Pscale + pRadius
      let B0 := 1 + Pbase + Pseed + Qw + Pmin + Elog + Vlog
      ∀ (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
        ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => σ),
          Pk ≤ Pscale ∧ Lmin ≤ S.value ∧
          (S.value : ℝ) ≤ Real.exp
            (allocatedWitnessScaleLog Pseed Qw + (1 + Pseed ^ 2) * Pmin) ∧
          (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
            8 * (probabilityProfileLipschitz : ℝ) * W ≤
              (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
                ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
          (∀ Bcert : ℝ, B0 ≤ Bcert →
            PreparedShortCertifiedSameScaleBadProductInterface L U basis S Bcert Elog Vlog Qbad) ∧
          (∀ (Apert : ℝ≥0) {ηpert : ℝ}, 0 < ηpert →
            (Apert : ℝ) ≤ Real.exp Ppert → ηpert⁻¹ ≤ Real.exp Epert →
            let active := fun a => ¬allocatedShortAxis (I := I) U basis S.value a
            let inputs := PrincipalTupleIndex (fun a : {a // active a} => B a.val)
              (fun a => layerSamplerDegree I n a.val)
            σ * polynomialMassC2Budget (Fintype.card inputs) m 1 ≤
              slicedPrincipalC2Tolerance (Fintype.card inputs) (Fintype.card {a // active a})
                m 1 (unitProfilePrincipalLowerBound B) (1 / 2) Apert ηpert) ∧
          (∀ lateTarget : ℝ, gainLog + 32 ≤ lateTarget →
            let Plate := preparedModularGeneralDetectorLateMaster master Pseed Qw Pphysical lateTarget +
              (1 + Pseed ^ 2) * Pmin + Pscale
            let resources := preparedModularGeneralDetectorResources
              (preparedModularGeneralDetectorConstants m 0) (0 + 1) master Plate
            let Pwidth := resources.Pproj
            let Bcert := preparedForecastGoodCertificateBudget B0 Bstruct Pwidth g₀ Vlog
            let Pgood := preparedForecastGoodAnalyticBudget
              (preparedCenteredShortForecastSpatialExponent m) B0 Bstruct Pwidth g₀ Vlog
            resources.nativeBudget = (preparedModularGeneralDetectorResources
              (preparedModularGeneralDetectorConstants m 0) (0 + 1) master master).nativeBudget ∧
            (∀ (hRpos : ∀ j, 0 < R j) (hσpos : ∀ _j : Fin m, 0 < σ)
              (stride N : Fin nX → ℕ)
              (Q : Fin m → Type) [∀ j, Fintype (Q j)]
              (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
              (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
              (_bW : ∀ j, Module.Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
              [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
              (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
                (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
              [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
              [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
              [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
              [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
              (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
              [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
              [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
              [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
              [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
              (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
              [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
              [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
              [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
              (Vtail : Fin m → ℝ≥0) (forecastCap gain : ℝ),
              0 ≤ forecastCap → forecastCap ≤ Real.exp pForecast → Real.exp (-g₀) ≤ gain →
              PreparedCenteredShortForecastGoodModelInterface
                (prep := L) (U := U) (b := basis) (S := S) (hR := hRpos) (hσ := hσpos)
                (selection := selection) (stride := stride) (N := N)
                (Pdetect := Pdetect) (uSource := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
                (τ := Real.exp (-(g₀ + (nX : ℝ) + 8))) (u := uModel) (p := pForecast) (forecastCap := forecastCap)
                (hb := hb) (o := o) (bW := _bW) (μ := μ)
                Bstruct Qstride master Plate gainLog Pphysical lateTarget
                Bcert g₀ gain Pgood Qbad (preparedSpatialKernelBlocks m M nX))) ∧
          ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
            Real.exp (-gainLog) ≤
              (Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1)) ∧
            (scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) : ℝ) ≤ Real.exp Pk ∧
            scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
              (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) ≤ S.value

theorem exists_prepared_short_good_forecast_source (m : ℕ) (Pdetect : Polynomial ℕ) :
    PreparedShortGoodForecastSourceStatement m Pdetect := by
  unfold PreparedShortGoodForecastSourceStatement
  intro Cdetect Aearly Aalloc
  have hactual := exists_prepared_short_certified_forecast_source m Pdetect
  unfold PreparedShortCertifiedForecastSourceStatement at hactual
  obtain ⟨C, hC, hsource⟩ := hactual
  refine ⟨C, hC, ?_⟩
  intro X J₀ L M nX hCoord Pstruct pSlice Qstride g₀ hm hPstruct hM hpSlice hQstride hnX hnXpos hg hgStruct
    Jalloc pnum Bstruct G I n B selection A radiusBudget rowSets T siteRadius D
  obtain ⟨hStruct, _, hnum, _⟩ :=
    (Classical.choose_spec (exists_preparedModularCanonicalDetectorAllocationBudget m)).2
      hPstruct hM hnX
  have hB : 0 ≤ Bstruct := hPstruct.trans hStruct
  obtain ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource,
      hTradius, hTbound, hrbound, hsmall, hdimensions, hlate⟩ :=
    hsource L hCoord hm hPstruct hM hpSlice hQstride hnX hg hgStruct
  refine ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource,
    hTradius, hTbound, hrbound, hsmall, hdimensions, ?_⟩
  intro uModel pForecast P huModel hpForecast hModelForecast hmaster u Pearly pModel pDetect aDetect
    gainLog Pk Qearly Pphysical Eextra target F Tmod δ E η Prho Ptail K budget master
  obtain ⟨hpRadiusBudget, hTbudget, hrbudget, hRadiusEarly, hPEarly, hEarlyBudget,
      hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
      hGainPhysical, t, ht, htone, htPtail, htbudget, htolerances⟩ :=
    hlate huModel hpForecast hModelForecast hmaster
  refine ⟨hpRadiusBudget, hTbudget, hrbudget, hRadiusEarly, hPEarly, hEarlyBudget,
    hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
    hGainPhysical, t, ht, htone, htPtail, htbudget, ?_⟩
  intro Ppert Epert hPpert hEpert Qσ σ Pscale lengthLog Pseed
  obtain ⟨hσ, hσt, hσexp, hσinv, hScaleBound, hsamplers⟩ := htolerances hPpert hEpert
  refine ⟨hσ, hσt, hσexp, hσinv, hScaleBound, ?_⟩
  intro Lmin Pmin Vlog Qbad hPmin hLmin hVlog hQbad hQexp Elog W Qw J Pbase B0 U basis
  obtain ⟨S, hPkScale, hFloor, hSWitness, hgap, hcert, hperturb, hdetector, hgainKernel⟩ :=
    hsamplers Lmin Qbad hPmin hLmin hVlog hQbad hQexp U basis
  refine ⟨S, hPkScale, hFloor, hSWitness, hgap, hcert, hperturb, ?_, hgainKernel⟩
  intro lateTarget hCoarseLower Plate resources Pwidth Bcert Pgood
  obtain ⟨hnative, hprepared⟩ := hdetector lateTarget hCoarseLower
  refine ⟨hnative, ?_⟩
  intro hRpos hσpos stride N Q _ hb o bW _ ν _ _ _ _ _ μ
    _ _ _ _ _ μrows _ _ _ _ Vtail forecastCap gain hForecastCap hForecastCapP hGain
    hstride hstrideBound Cchart hCchart hCchartBound hchart Cforward hforward
    hForward hVtail hVactual hprofile hcutoff
  have hModelActual := hprepared hRpos hσpos stride N Q hb o bW ν μ μrows
    Vtail forecastCap hForecastCap hForecastCapP
  have hAearly : 2 ≤ Aearly :=
    (Classical.choose_spec (exists_preparedModularGeneralCanonicalEarlyParameters m 0 Cdetect)).1
  have hrawData := preparedShortForecastRawSourceBounds
    (m := m) (nX := nX) (M := M) (R := R) (σ := fun _ => σ)
    L U basis S o selection Pdetect Vtail A Aearly Qbad
    hCoord hB hnum.2 hpRadius hpSlice.1 (fun j => (hR j).1)
    (fun j => (hR j).2.2) (fun _ => hσt.trans htone) (fun _ => hσinv)
    (fun C hC hCb => (hsmall C hC hCb).1) hdimensions
    (hnX.trans hStruct) hnXpos hg (hgStruct.trans hStruct)
    ⟨hQstride.1, hQstride.2.trans hStruct⟩ hVtail hprofile
    huModel hpForecast hModelForecast hmaster hPEarly hEarlyBudget hModel hDetect.1
    hgain.1 hPk.1 hD hScaleBound.1 hPrho.1 htarget.1 hTmod.1 hpRadiusBudget
    hPmin hVlog hQexp hCoarseLower hAearly hForecastCapP hGain
    (fun α hα => (hgainKernel α hα).2.1) hSWitness hcert
  have hcombined := preparedShortForecastSourceModelAttachment
    (m := m) (nX := nX) (M := M) (X₀ := X) (J₀ := J₀)
    (prep := L) (U := U) (b := basis) (hR := hRpos) (hσ := hσpos) (S := S)
    (selection := selection) (stride := stride) (N := N) (Pdetect := Pdetect)
    (uSource := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
    (τ := Real.exp (-(g₀+(nX:ℝ)+8))) (u := uModel) (p := pForecast) (forecastCap := forecastCap)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (μ := μ) (ν := ν)
    Bstruct Qstride master Plate gainLog Pphysical lateTarget
    B0 Vlog g₀ gain Pwidth Qbad (preparedSpatialKernelBlocks m M nX)
    (D := D)
  have hcombined := hcombined hrawData.1 hModelActual
  intro Eforecast
  exact hcombined hstride hstrideBound Cchart hCchart hCchartBound hchart Cforward hforward
    hForward hVtail hVactual hprofile hcutoff (E := Eforecast)

end Erdos3.VectorPolynomial

end

end OAI

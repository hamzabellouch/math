import OAI.Combinatorics.Progressions.Estimates.PreparedPerturbativeCertifiedSource
import OAI.Combinatorics.Progressions.Estimates.PreparedShortLateToleranceCertifiedAttachment
import OAI.Combinatorics.Progressions.Sampling.PreparedCenteredForecastGoodModel
import OAI.Combinatorics.Progressions.Sampling.PreparedCenteredShortForecastProductiveGoodModel
import OAI.Combinatorics.Progressions.Sampling.PreparedShortForecastRawSourceBounds

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

def PreparedPerturbativeForecastSourceStatement (m : ℕ) (Pdetect : Polynomial ℕ) : Prop :=
    let Cdetect := sampledSupportedSlicedDetectionConstant 0 Pdetect
    let Aearly := Classical.choose (exists_preparedModularGeneralCanonicalEarlyParameters m 0 Cdetect)
    let Aalloc := Classical.choose (exists_preparedModularCanonicalDetectorAllocationBudget m)
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {X J₀ : Type} (L : RankPreparationFamily X J₀ m) {M nX : ℕ},
      (∀ j, Fintype.card (L j).Coord ≤ M) →
      ∀ {Pstruct pSlice Qstride : ℝ},
      0 < m → 0 ≤ Pstruct → (M : ℝ) ≤ Pstruct →
      pSlice ∈ Set.Icc 0 Pstruct → Qstride ∈ Set.Icc 0 Pstruct → (nX : ℝ) ≤ Pstruct →
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
      ∀ (Lmin : ℕ) {Pmin Elog Vlog : ℝ} (Qbad : ℕ),
        0 ≤ Pmin → (Lmin : ℝ) ≤ Real.exp Pmin →
        0 ≤ Elog → 0 ≤ Vlog → 1 ≤ Qbad → (Qbad : ℝ) ≤ Real.exp Vlog →
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
            PreparedCertifiedSameScaleBadProductInterface L U basis S Bcert Elog Vlog Qbad) ∧
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
              (Vtail : Fin m → ℝ≥0) (τfree forecastCap : ℝ),
              0 ≤ forecastCap → forecastCap ≤ Real.exp pForecast →
              PreparedCenteredForecastModelInterface
                (B := B) (U := U) (basis := basis) (S := S) (hR := hRpos) (hσ := hσpos)
                (selection := selection) (stride := stride) (N := N)
                (Pdetect := Pdetect) (uSource := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
                (τ := τfree) (u := uModel) (p := pForecast) (forecastCap := forecastCap)
                (hb := hb) (o := o) (μ := μ) Bstruct Qstride master Plate gainLog Pphysical lateTarget)) ∧
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

theorem exists_prepared_perturbative_forecast_source (m : ℕ) (Pdetect : Polynomial ℕ) :
    PreparedPerturbativeForecastSourceStatement m Pdetect := by
  unfold PreparedPerturbativeForecastSourceStatement
  intro Cdetect Aearly Aalloc
  have hactual := exists_prepared_perturbative_certified_source m Pdetect
  unfold PreparedPerturbativeCertifiedSourceStatement at hactual
  obtain ⟨C, hC, hsource⟩ := hactual
  refine ⟨C, hC, ?_⟩
  intro X J₀ L M nX hCoord Pstruct pSlice Qstride hm hPstruct hM hpSlice hQstride hnX
    Jalloc pnum Bstruct G I n B selection A radiusBudget rowSets T siteRadius D
  obtain ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource,
      hTradius, hTbound, hrbound, hsmall, hdimensions, hlate⟩ :=
    hsource L hCoord hm hPstruct hM hpSlice hQstride hnX
  refine ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource,
    hTradius, hTbound, hrbound, hsmall, hdimensions, ?_⟩
  intro uModel pForecast P huModel hpForecast hModelForecast hmaster u Pearly pModel pDetect aDetect
    gainLog Pk Qearly Pphysical Eextra target F Tmod δ E η Prho Ptail K budget master
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  obtain ⟨hpRadiusBudget, hTbudget, hrbudget, hRadiusEarly, hPEarly, hEarlyBudget,
      hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
      t, ht, htone, htPtail, htbudget, htolerances⟩ := hlate hu hmaster
  refine ⟨hpRadiusBudget, hTbudget, hrbudget, hRadiusEarly, hPEarly, hEarlyBudget,
    hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
    t, ht, htone, htPtail, htbudget, ?_⟩
  intro Ppert Epert hPpert hEpert Qσ σ Pscale lengthLog Pseed
  obtain ⟨hσ, hσt, hσexp, hσinv, hScaleBound, hsamplers⟩ := htolerances hPpert hEpert
  refine ⟨hσ, hσt, hσexp, hσinv, hScaleBound, ?_⟩
  intro Lmin Pmin Elog Vlog Qbad hPmin hLmin hElog hVlog hQbad hQexp W Qw J Pbase B0 U basis
  obtain ⟨S, hPkScale, hFloor, hSWitness, hgap, hcert, hperturb, hdetector, hgainKernel⟩ :=
    hsamplers Lmin Qbad hPmin hLmin hElog hVlog hQbad hQexp U basis
  refine ⟨S, hPkScale, hFloor, hSWitness, hgap, hcert, hperturb, ?_, hgainKernel⟩
  intro lateTarget hCoarseLower Plate resources
  obtain ⟨hnative, hprepared⟩ := hdetector lateTarget hCoarseLower
  refine ⟨hnative, ?_⟩
  intro hRpos hσpos stride N Q _ hb o bW _ ν _ _ _ _ _ μ
    _ _ _ _ _ μrows _ _ _ _ Vtail τfree forecastCap hForecastCap hForecastCapP
    hstride hstrideBound Cchart hCchart hCchartBound hchart Cforward hforward
    hForward hVtail hVactual hprofile hcutoff
  obtain ⟨hStruct, _, hnum, _⟩ :=
    (Classical.choose_spec (exists_preparedModularCanonicalDetectorAllocationBudget m)).2
      hPstruct hM hnX
  have hB : 0 ≤ Bstruct := hPstruct.trans hStruct
  have hcapData := preparedModularCanonicalDetector_early_cap L Jalloc A hCoord
    hB hnum.2 hpSlice.1 (le_refl (0 : ℝ)) R Vtail
    (fun j => (hR j).1) (fun j => (hR j).2.2) hpRadius.2 hVtail hprofile
  have hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ pForecast :=
    hcapData.2.2.2.1.trans hModelForecast
  have hCtail : (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j)) ≤ Real.exp pForecast :=
    hcapData.2.2.2.2.2.1.trans (Real.exp_le_exp.mpr hModelForecast)
  let cap := 4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j)
  let Kslice := Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
  let α := forecastAugmentedUnitThreshold uModel pForecast Kslice (max 1 cap) forecastCap
  have hKp : Kslice ≤ Real.exp pForecast := Real.exp_le_exp.mpr hSliceLog
  have hCap := marginalCap_max_one_exp_bound hpForecast hCtail
  have hαlower : Real.exp (-aDetect) ≤ α / 2 :=
    (forecastAugmented_separate_source_precision huModel hpForecast hModel.1
      (Real.exp_nonneg _) (zero_le_one.trans hCap.1) hKp hCap.2 hForecastCapP).2
  have hαone : α ≤ 1 := (forecastAugmentedUnitThreshold_bounds huModel hpForecast
    (Real.exp_nonneg _) (zero_le_one.trans hCap.1) hKp hCap.2 hForecastCapP).2.1
  have hRadius := hprepared hRpos hσpos stride N Q hb o bW ν μ μrows Vtail α τfree hαlower hαone
  have hP : 0 ≤ P := hB.trans ((le_add_of_nonneg_right hu).trans hmaster)
  have hQearly : 0 ≤ Qearly := by dsimp only [Qearly]; positivity
  have hphysical : 0 ≤ Pphysical := by
    dsimp only [Pphysical]
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg hQearly hPk.1)
      hQstride.1) (Nat.cast_nonneg nX)) (Nat.cast_nonneg (m+1))) (by norm_num)
  have hearly : 0 ≤ Pearly := hP.trans hPEarly
  have hbudget : 0 ≤ budget := hModel.1.trans hModel.2
  have hMaster : 0 ≤ master := by
    dsimp only [master]
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg hbudget hphysical) hearly) hgain.1) (by norm_num)
  have hF : 0 ≤ F := by change 0 ≤ pDetect+2; linarith only [hDetect.1]
  have hlength : 0 ≤ lengthLog :=
    (allocatedAffineLengthLog_bounds m hD.1 hScaleBound.1 hPrho.1 hPk.1
      htarget.1 hF hTmod.1).2.2.1
  have hseed : 0 ≤ Pseed := allocatedScaleLog_nonneg
    (add_nonneg (add_nonneg (add_nonneg hD.1 hScaleBound.1) hlength) (by norm_num))
  have hQw : 0 ≤ Qw := by dsimp only [Qw]; positivity
  have hlateTarget : 0 ≤ lateTarget := hgain.1.trans
    ((le_add_of_nonneg_right (by norm_num)).trans hCoarseLower)
  have hLateBase := (preparedModularGeneralDetectorLateMaster_bounds
    hMaster hseed hQw hphysical hlateTarget).2.1
  have hLate : master ≤ Plate := by
    calc
      master ≤ preparedModularGeneralDetectorLateMaster master Pseed Qw Pphysical lateTarget := hLateBase
      _ ≤ preparedModularGeneralDetectorLateMaster master Pseed Qw Pphysical lateTarget +
          (1 + Pseed ^ 2) * Pmin := le_add_of_nonneg_right (mul_nonneg (by positivity) hPmin)
      _ ≤ Plate := le_add_of_nonneg_right hScaleBound.1
  intro Eforecast
  exact preparedCenteredForecastModelInterface_of_radius
    (B := B) (U := U) (basis := basis) (hR := hRpos) (hσ := hσpos) (S := S)
    (selection := selection) (stride := stride) (N := N) (Pdetect := Pdetect)
    (uSource := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
    (τ := τfree) (u := uModel) (p := pForecast) (forecastCap := forecastCap)
    (hb := hb) (o := o) (μ := μ)
    Bstruct Qstride master Plate gainLog Pphysical lateTarget hMaster hLate
    huModel hpForecast hSliceLog hCtail hForecastCap hForecastCapP hRadius
    hstride hstrideBound Cchart hCchart hCchartBound hchart Cforward hforward
    hForward hVtail hVactual hprofile hcutoff (E := Eforecast)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

def PreparedEarlyWidthForecastSourceStatement (m : ℕ) (Pdetect : Polynomial ℕ) : Prop :=
    let Cdetect := sampledSupportedSlicedDetectionConstant 0 Pdetect
    let Aearly := Classical.choose (exists_preparedModularGeneralCanonicalEarlyParameters m 0 Cdetect)
    let Aalloc := Classical.choose (exists_preparedModularCanonicalDetectorAllocationBudget m)
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {X J₀ : Type} (L : RankPreparationFamily X J₀ m) {M nX : ℕ},
      (∀ j, Fintype.card (L j).Coord ≤ M) →
      ∀ {Pstruct pSlice Qstride g₀ : ℝ},
      0 < m → 0 ≤ Pstruct → (M : ℝ) ≤ Pstruct →
      pSlice ∈ Set.Icc 0 Pstruct → Qstride ∈ Set.Icc 0 Pstruct → (nX : ℝ) ≤ Pstruct → 0 ≤ g₀ → g₀ ≤ Pstruct →
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
            PreparedCertifiedSameScaleBadProductInterface L U basis S Bcert Elog Vlog Qbad) ∧
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
              (Vtail : Fin m → ℝ≥0) (forecastCap : ℝ),
              0 ≤ forecastCap → forecastCap ≤ Real.exp pForecast →
              PreparedCenteredForecastEarlyWidthModelInterface
                (B := B) (U := U) (basis := basis) (S := S) (hR := hRpos) (hσ := hσpos)
                (selection := selection) (stride := stride) (N := N)
                (Pdetect := Pdetect) (uSource := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
                (u := uModel) (p := pForecast) (forecastCap := forecastCap)
                (hb := hb) (o := o) (μ := μ) g₀ Bstruct Qstride master Plate gainLog Pphysical lateTarget)) ∧
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

theorem exists_prepared_early_width_forecast_source (m : ℕ) (Pdetect : Polynomial ℕ) :
    PreparedEarlyWidthForecastSourceStatement m Pdetect := by
  unfold PreparedEarlyWidthForecastSourceStatement
  intro Cdetect Aearly Aalloc
  have hactual := exists_prepared_perturbative_forecast_source m Pdetect
  unfold PreparedPerturbativeForecastSourceStatement at hactual
  obtain ⟨C, hC, hsource⟩ := hactual
  refine ⟨C, hC, ?_⟩
  intro X J₀ L M nX hCoord Pstruct pSlice Qstride g₀ hm hPstruct hM hpSlice hQstride hnX hg hgStruct
    Jalloc pnum Bstruct G I n B selection A radiusBudget rowSets T siteRadius D
  obtain ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource,
      hTradius, hTbound, hrbound, hsmall, hdimensions, hlate⟩ :=
    hsource L hCoord hm hPstruct hM hpSlice hQstride hnX
  refine ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource,
    hTradius, hTbound, hrbound, hsmall, hdimensions, ?_⟩
  intro uModel pForecast P huModel hpForecast hModelForecast hmaster u Pearly pModel pDetect aDetect
    gainLog Pk Qearly Pphysical Eextra target F Tmod δ E η Prho Ptail K budget master
  obtain ⟨hpRadiusBudget, hTbudget, hrbudget, hRadiusEarly, hPEarly, hEarlyBudget,
      hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
      t, ht, htone, htPtail, htbudget, htolerances⟩ :=
    hlate huModel hpForecast hModelForecast hmaster
  have hStruct : Pstruct ≤ Bstruct :=
    ((Classical.choose_spec (exists_preparedModularCanonicalDetectorAllocationBudget m)).2
      hPstruct hM hnX).1
  have hB : 0 ≤ Bstruct := hPstruct.trans hStruct
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have hBP : Bstruct ≤ P := (le_add_of_nonneg_right hu).trans hmaster
  have hP : 0 ≤ P := hB.trans hBP
  have hAearly : 2 ≤ Aearly :=
    (Classical.choose_spec (exists_preparedModularGeneralCanonicalEarlyParameters m 0 Cdetect)).1
  have hPQ : P ≤ Qearly := by
    have hbase : 1 ≤ P + Aearly := by
      have ha : (2 : ℝ) ≤ Aearly := Nat.cast_le.mpr hAearly
      linarith only [hP, ha]
    exact (le_add_of_nonneg_right (Nat.cast_nonneg Aearly)).trans
      (le_self_pow₀ hbase (by omega))
  have hGainPhysical : g₀ + (nX : ℝ) + 8 ≤ Pphysical := by
    have hgQ := hgStruct.trans (hStruct.trans (hBP.trans hPQ))
    change g₀ + (nX : ℝ) + 8 ≤ Qearly + Pk + Qstride + nX + (m+1:ℕ) + 8
    linarith only [hgQ, hPk.1, hQstride.1, Nat.cast_nonneg (α := ℝ) (m+1)]
  refine ⟨hpRadiusBudget, hTbudget, hrbudget, hRadiusEarly, hPEarly, hEarlyBudget,
    hModel, hDetect, hAlog, htarget, hD, hgain, hPk, hPrho, hPtail, hTmod,
    hGainPhysical, t, ht, htone, htPtail, htbudget, ?_⟩
  intro Ppert Epert hPpert hEpert Qσ σ Pscale lengthLog Pseed
  obtain ⟨hσ, hσt, hσexp, hσinv, hScaleBound, hsamplers⟩ := htolerances hPpert hEpert
  refine ⟨hσ, hσt, hσexp, hσinv, hScaleBound, ?_⟩
  intro Lmin Pmin Vlog Qbad hPmin hLmin hVlog hQbad hQexp Elog W Qw J Pbase B0 U basis
  have hElog : 0 ≤ Elog := by change 0 ≤ g₀+8; linarith only [hg]
  obtain ⟨S, hPkScale, hFloor, hSWitness, hgap, hcert, hperturb, hdetector, hgainKernel⟩ :=
    hsamplers Lmin (Elog := Elog) Qbad hPmin hLmin hElog hVlog hQbad hQexp U basis
  refine ⟨S, hPkScale, hFloor, hSWitness, hgap, hcert, hperturb, ?_, hgainKernel⟩
  intro lateTarget hCoarseLower Plate resources
  obtain ⟨hnative, hprepared⟩ := hdetector lateTarget hCoarseLower
  refine ⟨hnative, ?_⟩
  intro hRpos hσpos stride N Q _ hb o bW _ ν _ _ _ _ _ μ
    _ _ _ _ _ μrows _ _ _ _ Vtail forecastCap hForecastCap hForecastCapP
  exact hprepared hRpos hσpos stride N Q hb o bW ν μ μrows Vtail
    (Real.exp (-(g₀ + (nX : ℝ) + 8))) forecastCap hForecastCap hForecastCapP

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

def PreparedGoodForecastSourceStatement (m : ℕ) (Pdetect : Polynomial ℕ) : Prop :=
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
            PreparedCertifiedSameScaleBadProductInterface L U basis S Bcert Elog Vlog Qbad) ∧
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
              (preparedCenteredForecastSpatialExponent m) B0 Bstruct Pwidth g₀ Vlog
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
              PreparedCenteredForecastGoodModelInterface
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

theorem exists_prepared_good_forecast_source (m : ℕ) (Pdetect : Polynomial ℕ) :
    PreparedGoodForecastSourceStatement m Pdetect := by
  unfold PreparedGoodForecastSourceStatement
  intro Cdetect Aearly Aalloc
  have hactual := exists_prepared_early_width_forecast_source m Pdetect
  unfold PreparedEarlyWidthForecastSourceStatement at hactual
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
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have hBP : Bstruct ≤ P := (le_add_of_nonneg_right hu).trans hmaster
  have hP : 0 ≤ P := hB.trans hBP
  have hQearly : 0 ≤ Qearly := by dsimp only [Qearly]; positivity
  have hphysical : 0 ≤ Pphysical := by
    dsimp only [Pphysical]
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg hQearly hPk.1)
      hQstride.1) (Nat.cast_nonneg nX)) (Nat.cast_nonneg (m+1))) (by norm_num)
  have hearly : 0 ≤ Pearly := hP.trans hPEarly
  have hbudget : 0 ≤ budget := hModel.1.trans hModel.2
  have hMaster : 0 ≤ master := by
    dsimp only [master]
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg hbudget hphysical) hearly) hgain.1) (by norm_num)
  have hBudgetMaster : budget ≤ master := by
    dsimp only [master]
    linarith only [hphysical, hearly, hgain.1]
  have hPhysicalMaster : Pphysical ≤ master := by
    dsimp only [master]
    linarith only [hbudget, hearly, hgain.1]
  have hBMaster : Bstruct ≤ master := hBP.trans (hPEarly.trans (hEarlyBudget.trans hBudgetMaster))
  have hF : 0 ≤ F := by change 0 ≤ pDetect+2; linarith only [hDetect.1]
  have hlength : 0 ≤ lengthLog :=
    (allocatedAffineLengthLog_bounds m hD.1 hScaleBound.1 hPrho.1 hPk.1
      htarget.1 hF hTmod.1).2.2.1
  have hseed : 0 ≤ Pseed := allocatedScaleLog_nonneg
    (add_nonneg (add_nonneg (add_nonneg hD.1 hScaleBound.1) hlength) (by norm_num))
  have hQw : 0 ≤ Qw := by dsimp only [Qw, Elog]; positivity
  have hlateTarget : 0 ≤ lateTarget := hgain.1.trans
    ((le_add_of_nonneg_right (by norm_num)).trans hCoarseLower)
  obtain ⟨hBase0, hMasterBase, hWitnessBase, _, hXiBase⟩ :=
    preparedModularGeneralDetectorLateMaster_bounds hMaster hseed hQw hphysical hlateTarget
  have hFloorCost : 0 ≤ (1+Pseed^2)*Pmin := mul_nonneg (by positivity) hPmin
  have hBaseLate : preparedModularGeneralDetectorLateMaster master Pseed Qw Pphysical lateTarget ≤ Plate := by
    exact (le_add_of_nonneg_right hFloorCost).trans (le_add_of_nonneg_right hScaleBound.1)
  have hLate := hMasterBase.trans hBaseLate
  have hScaleLate : Pscale ≤ Plate := le_add_of_nonneg_left (add_nonneg hBase0 hFloorCost)
  have hWitnessLate : allocatedWitnessScaleLog Pseed Qw + (1+Pseed^2)*Pmin ≤ Plate := by
    exact (add_le_add hWitnessBase (le_refl _)).trans (le_add_of_nonneg_right hScaleBound.1)
  have hRi := fun j => (hR j).2.2.trans (Real.exp_le_exp.mpr (hpRadiusBudget.trans hBudgetMaster))
  have hσi := fun _j : Fin m => hσinv.trans (Real.exp_le_exp.mpr hScaleLate)
  have hSi := hSWitness.trans (Real.exp_le_exp.mpr hWitnessLate)
  have hproj := preparedCenteredMarginalProjectionBounds B U basis S o hMaster hLate
    hdimensions (hD.2.trans hBudgetMaster) (hnX.trans (hStruct.trans hBMaster)) hRi hσi hSi
  have hB00 : 0 ≤ B0 := by
    dsimp only [B0, Pbase, Elog]
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg
      (add_nonneg (by norm_num)
        (add_nonneg (add_nonneg hB hScaleBound.1) hpRadius.1)) hseed) hQw)
      hPmin) (add_nonneg hg (by norm_num))) hVlog
  obtain ⟨hBcert0, hBaseCert, hChartCert, hPhysicalCert, _, hCertGood,
      hWidthGood, hCutoffGood, hGainGood⟩ :=
    preparedForecastGoodBudgets (preparedCenteredForecastSpatialExponent m)
      hB00 hB hproj.Pproj_nonneg hg hVlog
  have hcapData := preparedModularCanonicalDetector_early_cap L Jalloc A hCoord
    hB hnum.2 hpSlice.1 (le_refl (0 : ℝ)) R Vtail
    (fun j => (hR j).1) (fun j => (hR j).2.2) hpRadius.2 hVtail hprofile
  have hCtail := hcapData.2.2.2.2.2.1.trans (Real.exp_le_exp.mpr hModelForecast)
  have hSliceLog := hcapData.2.2.2.1.trans hModelForecast
  have hCap := marginalCap_max_one_exp_bound hpForecast hCtail
  have hαlower := (forecastAugmented_separate_source_precision huModel hpForecast hModel.1
    (Real.exp_nonneg _) (zero_le_one.trans hCap.1)
    (Real.exp_le_exp.mpr hSliceLog) hCap.2 hForecastCapP).2
  have hMkPk := (hgainKernel _ hαlower).2.1
  have hAearly : 2 ≤ Aearly :=
    (Classical.choose_spec (exists_preparedModularGeneralCanonicalEarlyParameters m 0 Cdetect)).1
  have hPQ : P ≤ Qearly := preparedModularGeneralProductivity_le_budget hP hAearly
  obtain ⟨hQPhysical, hDimPhysical, hnPhysical, hPkPhysical⟩ :=
    preparedModularGeneralProductivity_physical_bounds m 0 nX hQearly hPk.1 hQstride.1
      (Nat.zero_le m)
  obtain ⟨hvars, _, _⟩ := enlargedPreparedCommonSampler_dimensions L Jalloc hCoord
  have hvarsPhysical := (Nat.cast_le.mpr hvars).trans (hnum.2.trans (hBP.trans (hPQ.trans hQPhysical)))
  have hξ := (preparedModularDetector_narrow_width B selection hphysical hlateTarget
    (hMkPk.trans (Real.exp_le_exp.mpr hPkPhysical)) hDimPhysical hvarsPhysical hnPhysical).2.trans
      (Real.exp_le_exp.mpr ((hXiBase.trans hBaseLate).trans hproj.late_projection))
  intro Eforecast
  have hcombined := preparedCenteredForecastGoodModelInterface_of_model
    (m := m) (nX := nX) (M := M) (X₀ := X) (J₀ := J₀)
    (prep := L) (U := U) (b := basis) (hR := hRpos) (hσ := hσpos) (S := S)
    (selection := selection) (stride := stride) (N := N) (Pdetect := Pdetect)
    (uSource := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
    (τ := Real.exp (-(g₀+(nX:ℝ)+8))) (u := uModel) (p := pForecast) (forecastCap := forecastCap)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (μ := μ) (ν := ν)
    Bstruct Qstride master Plate gainLog Pphysical lateTarget
    Bcert Vlog g₀ gain Pwidth Bstruct Pgood Qbad (preparedSpatialKernelBlocks m M nX)
    (D := D) ⟨hcert Bcert hBaseCert, hnXpos, (fun _ => hσt.trans htone),
      (fun C hC hCb => (hsmall C hC hCb).1), hMaster, hLate, hdimensions,
      (hD.2.trans hBudgetMaster), (hnX.trans (hStruct.trans hBMaster)), hRi, hσi, hSi,
      hChartCert, (le_refl _), hPhysicalCert, hVlog, hQexp, hB, (hnX.trans hStruct),
      (hgStruct.trans hStruct), hCutoffGood, hCertGood, hWidthGood, hg, hGainGood, hGain,
      (hQstride.2.trans (hStruct.trans (hBMaster.trans hproj.master_projection))),
      (hPhysicalMaster.trans hproj.master_projection), hξ⟩ hModelActual
  exact hcombined hstride hstrideBound Cchart hCchart hCchartBound hchart Cforward hforward
    hForward hVtail hVactual hprofile hcutoff (E := Eforecast)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

def PreparedShortCertifiedForecastSourceStatement (m : ℕ) (Pdetect : Polynomial ℕ) : Prop :=
    let Cdetect := sampledSupportedSlicedDetectionConstant 0 Pdetect
    let Aearly := Classical.choose (exists_preparedModularGeneralCanonicalEarlyParameters m 0 Cdetect)
    let Aalloc := Classical.choose (exists_preparedModularCanonicalDetectorAllocationBudget m)
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {X J₀ : Type} (L : RankPreparationFamily X J₀ m) {M nX : ℕ},
      (∀ j, Fintype.card (L j).Coord ≤ M) →
      ∀ {Pstruct pSlice Qstride g₀ : ℝ},
      0 < m → 0 ≤ Pstruct → (M : ℝ) ≤ Pstruct →
      pSlice ∈ Set.Icc 0 Pstruct → Qstride ∈ Set.Icc 0 Pstruct → (nX : ℝ) ≤ Pstruct → 0 ≤ g₀ → g₀ ≤ Pstruct →
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
              (Vtail : Fin m → ℝ≥0) (forecastCap : ℝ),
              0 ≤ forecastCap → forecastCap ≤ Real.exp pForecast →
              PreparedCenteredForecastEarlyWidthModelInterface
                (B := B) (U := U) (basis := basis) (S := S) (hR := hRpos) (hσ := hσpos)
                (selection := selection) (stride := stride) (N := N)
                (Pdetect := Pdetect) (uSource := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
                (u := uModel) (p := pForecast) (forecastCap := forecastCap)
                (hb := hb) (o := o) (μ := μ) g₀ Bstruct Qstride master Plate gainLog Pphysical lateTarget)) ∧
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

theorem exists_prepared_short_certified_forecast_source (m : ℕ) (Pdetect : Polynomial ℕ) :
    PreparedShortCertifiedForecastSourceStatement m Pdetect := by
  unfold PreparedShortCertifiedForecastSourceStatement
  intro Cdetect Aearly Aalloc
  have hactual := exists_prepared_early_width_forecast_source m Pdetect
  unfold PreparedEarlyWidthForecastSourceStatement at hactual
  obtain ⟨C, hC, hsource⟩ := hactual
  refine ⟨C, hC, ?_⟩
  intro X J₀ L M nX hCoord Pstruct pSlice Qstride g₀ hm hPstruct hM hpSlice hQstride hnX hg hgStruct
    Jalloc pnum Bstruct G I n B selection A radiusBudget rowSets T siteRadius D
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
  obtain ⟨S, hPkScale, hFloor, hSWitness, hgap, _, hperturb, hdetector, hgainKernel⟩ :=
    hsamplers Lmin Qbad hPmin hLmin hVlog hQbad hQexp U basis
  refine ⟨S, hPkScale, hFloor, hSWitness, hgap, ?_, hperturb, hdetector, hgainKernel⟩
  have hStruct : Pstruct ≤ Bstruct :=
    ((Classical.choose_spec (exists_preparedModularCanonicalDetectorAllocationBudget m)).2
      hPstruct hM hnX).1
  have hB : 0 ≤ Bstruct := hPstruct.trans hStruct
  have hF : 0 ≤ F := by change 0 ≤ pDetect + 2; linarith only [hDetect.1]
  have hlength : 0 ≤ lengthLog :=
    (allocatedAffineLengthLog_bounds m hD.1 hScaleBound.1 hPrho.1 hPk.1
      htarget.1 hF hTmod.1).2.2.1
  have hseed : 0 ≤ Pseed := allocatedScaleLog_nonneg
    (add_nonneg (add_nonneg (add_nonneg hD.1 hScaleBound.1) hlength) (by norm_num))
  have hElog : 0 ≤ Elog := add_nonneg hg (by norm_num)
  have hQw : 0 ≤ Qw := add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (by norm_num) hB) (mul_nonneg (by norm_num) hVlog))
    (mul_nonneg (by norm_num) hElog)) (by norm_num)
  exact preparedShortCertifiedSameScaleBadProductInterface_of_lateTolerance_larger
    (nX := nX) (M := M) (R := R) (σ := fun _ => σ) L U basis S
    (Bstruct := Bstruct) (pRadius := pRadius) (Pscale := Pscale)
    (Pseed := Pseed) (Qw := Qw) (Pmin := Pmin) (Elog := Elog) (Vlog := Vlog)
    Qbad hB hpRadius.1 hScaleBound.1 (hM.trans hStruct) (hnX.trans hStruct)
    (fun j => (hR j).2.2) (fun _ => hσinv) hseed hQw hPmin hElog hVlog
    hQbad hQexp hm hCoord hSWitness hgap

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

def PreparedProductiveGoodForecastSourceStatement (m : ℕ) (Pdetect : Polynomial ℕ) : Prop :=
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
            PreparedCertifiedSameScaleBadProductInterface L U basis S Bcert Elog Vlog Qbad) ∧
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
              (preparedCenteredForecastSpatialExponent m) B0 Bstruct Pwidth g₀ Vlog
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
              PreparedCenteredForecastProductiveGoodModelInterface (m := m) (nX := nX) (M := M)
                (prep := L) (U := U) (b := basis) (S := S) (hR := hRpos) (hσ := hσpos)
                (selection := selection) (stride := stride) (N := N)
                (Pdetect := Pdetect) (uSource := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
                (τ := Real.exp (-(g₀ + (nX : ℝ) + 8))) (u := uModel) (p := pForecast) (forecastCap := forecastCap)
                (hb := hb) (o := o) (bW := _bW) (μ := μ)
                Bstruct Qstride master Plate gainLog Pphysical lateTarget
                Bcert g₀ gain Pgood Qbad (preparedSpatialKernelBlocks m M nX)
                (4 * (Plate + 8) ^ 2))) ∧
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

theorem exists_prepared_productive_good_forecast_source (m : ℕ) (Pdetect : Polynomial ℕ) :
    PreparedProductiveGoodForecastSourceStatement m Pdetect := by
  unfold PreparedProductiveGoodForecastSourceStatement
  intro Cdetect Aearly Aalloc
  have hactual := exists_prepared_good_forecast_source m Pdetect
  unfold PreparedGoodForecastSourceStatement at hactual
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
    hsource L hCoord hm hPstruct hM hpSlice hQstride hnX hnXpos hg hgStruct
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
    Vtail forecastCap gain hForecastCap hForecastCapP hGain
  have hs := preparedForecastSourceScalarBounds m nX Aearly huModel hpForecast hB
    hmaster hPEarly hEarlyBudget hModel hDetect.1 hgain.1 hPk.1 hQstride.1
    hD.1 hScaleBound.1 hPrho.1 htarget.1 hTmod.1 hPmin hVlog hg hCoarseLower
  have hBP := hs.struct_input
  have hP := hs.P_nonneg
  have hQearly := hs.Qearly_nonneg
  have hphysical := hs.physical_nonneg
  have hMaster := hs.master_nonneg
  have hBudgetMaster := hs.budget_master
  have hPhysicalMaster := hs.physical_master
  have hBMaster := hs.struct_master
  have hlateTarget := hs.lateTarget_nonneg
  have hLate := hs.master_late
  have hScaleLate := hs.scale_late
  have hWitnessLate := hs.witness_late
  have hRi := fun j => (hR j).2.2.trans (Real.exp_le_exp.mpr (hpRadiusBudget.trans hBudgetMaster))
  have hσi := fun _j : Fin m => hσinv.trans (Real.exp_le_exp.mpr hScaleLate)
  have hSi := hSWitness.trans (Real.exp_le_exp.mpr hWitnessLate)
  have hAearly : 2 ≤ Aearly :=
    (Classical.choose_spec (exists_preparedModularGeneralCanonicalEarlyParameters m 0 Cdetect)).1
  have hPQ : P ≤ Qearly := preparedModularGeneralProductivity_le_budget hP hAearly
  obtain ⟨hQPhysical, hDimPhysical, _, hPkPhysical⟩ :=
    preparedModularGeneralProductivity_physical_bounds m 0 nX hQearly hPk.1 hQstride.1 (Nat.zero_le m)
  have hnPhysical : (nX : ℝ) ≤ Pphysical :=
    hnX.trans (hStruct.trans (hBP.trans (hPQ.trans hQPhysical)))
  have hξ := preparedForecastSource_width (nX := nX) L Jalloc A hCoord selection Pdetect R Vtail
    hB hnum.2 hpSlice.1 (fun j => (hR j).1) (fun j => (hR j).2.2)
    hpRadius.2 hVtail hprofile huModel hpForecast hModel.1 hModelForecast hForecastCapP
    hphysical hlateTarget hPkPhysical hDimPhysical
    (hnum.2.trans (hBP.trans (hPQ.trans hQPhysical))) hnPhysical
    hs.xi_late (fun α hα => (hgainKernel α hα).2.1)
  have hproductiveModel := preparedCenteredForecastProductiveGoodModelInterface_of_goodModel (m := m) (nX := nX) (M := M)
    (prep := L) (U := U) (b := basis) (hR := hRpos) (hσ := hσpos) (S := S)
    (selection := selection) (stride := stride) (N := N) (Pdetect := Pdetect)
    (uSource := u) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
    (τ := Real.exp (-(g₀+(nX:ℝ)+8))) (u := uModel) (p := pForecast) (forecastCap := forecastCap)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (μ := μ) (ν := ν)
    Bstruct Qstride master Plate gainLog Pphysical lateTarget
    Bcert g₀ gain Pgood Qbad (preparedSpatialKernelBlocks m M nX) (4 * (Plate+8)^2)
    (D := D)
    ⟨hnXpos, (fun _ => hσt.trans htone), (fun C hC hCb => (hsmall C hC hCb).1),
      hMaster, hLate, hdimensions, (hD.2.trans hBudgetMaster), (hnX.trans (hStruct.trans hBMaster)),
      hRi, hσi, hSi, hBMaster, (hQstride.2.trans (hStruct.trans hBMaster)),
      le_rfl, hg, (hGainPhysical.trans hPhysicalMaster), rfl, hξ⟩ hModelActual
  intro forecastError
  exact hproductiveModel
    hstride hstrideBound Cchart hCchart hCchartBound hchart Cforward hforward
    hForward hVtail hVactual hprofile hcutoff (E := forecastError)

end Erdos3.VectorPolynomial

end

end OAI

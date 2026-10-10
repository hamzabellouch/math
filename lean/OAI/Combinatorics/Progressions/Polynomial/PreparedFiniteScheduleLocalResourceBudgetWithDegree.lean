import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleLocalScalarConstruction

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem exists_preparedFiniteScheduleLocalPrecisionBudgetWithDegree
    (m degree Cdetect : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {G : Type} [Fintype G] {count nX : ℕ}
      {P pDetect aDetect Qstride : ℝ},
      0 ≤ P → pDetect ∈ Set.Icc 0 P → aDetect ∈ Set.Icc 0 P →
      Qstride ∈ Set.Icc 0 P →
      (count : ℝ) ≤ P → (nX : ℝ) ≤ P → (Fintype.card G : ℝ) ≤ P →
      let gainLog := slicedDetectionGainLog degree Cdetect count
        pDetect pDetect aDetect
      let Pk := scalarKernelLogarithmicBudget (Fin (degree + 1)) G
        (gainLog + pDetect + 4)
      let Pphysical := preparedFiniteScheduleLocalPhysical m nX count Qstride Pk
      let target := gainLog + 40 + coefficientErrorSpatialLog Pphysical
      let budget := (P + C) ^ C
      P ≤ budget ∧ gainLog ∈ Set.Icc 0 budget ∧ Pk ∈ Set.Icc 0 budget ∧
        Pphysical ∈ Set.Icc 0 budget ∧ target ∈ Set.Icc 0 budget := by
  obtain ⟨A, _, hEarly⟩ :=
    exists_primitiveCanonicalSliceEarlyScale_budget m degree Cdetect
  let X : Polynomial ℕ := Polynomial.X
  let earlyPoly := (X + Polynomial.C A) ^ A
  let physicalPoly := Polynomial.C (m + 2) + 3 * X + earlyPoly
  let precisionPoly := earlyPoly + 40 + coefficientErrorSpatialLog physicalPoly
  obtain ⟨C, hC, hBound⟩ :=
    exists_natPolynomial_eval_budget (earlyPoly + physicalPoly + precisionPoly)
  refine ⟨C, hC, ?_⟩
  intro G _ count nX P pDetect aDetect Qstride hP hp ha hQ hcount hnX hG
    gainLog Pk Pphysical target budget
  let early := (P + A) ^ A
  let physical : ℝ := ((m + 2 : ℕ) : ℝ) + 3 * P + early
  let precision := early + 40 + coefficientErrorSpatialLog physical
  have hearly0 : 0 ≤ early := by dsimp only [early]; positivity
  have hphysical0 : 0 ≤ physical := by dsimp only [physical]; positivity
  have hprecision0 : 0 ≤ precision := by
    have := coefficientErrorSpatialLog_nonneg hphysical0
    dsimp only [precision]
    positivity
  have htotal : early + physical + precision ≤ budget := by
    simpa [X, earlyPoly, physicalPoly, precisionPoly, early, physical, precision,
      coefficientErrorSpatialLog, coefficientErrorVolumeLog, anisotropicSpatialCapLog,
      Polynomial.eval₂_pow] using hBound P hP
  have hearlyCap : early ≤ budget := by linarith only [htotal, hphysical0, hprecision0]
  have hphysicalCap : physical ≤ budget := by linarith only [htotal, hearly0, hprecision0]
  have hprecisionCap : precision ≤ budget := by linarith only [htotal, hearly0, hphysical0]
  have hzero : (0 : ℝ) ∈ Set.Icc 0 P := ⟨le_rfl, hP⟩
  obtain ⟨hPEarly, _, hg, hk, _, _, _, _, _⟩ :=
    hEarly (G := G) hP hzero hp hp ha hzero hQ hzero hcount hnX hG
  have hgain : gainLog ∈ Set.Icc 0 early := hg
  have hkernel : Pk ∈ Set.Icc 0 early := hk
  have hactual0 : 0 ≤ Pphysical := by
    have hkernel0 := hkernel.1
    have hstride0 := hQ.1
    dsimp only [Pphysical, preparedFiniteScheduleLocalPhysical]
    positivity
  have hactual : Pphysical ≤ physical := by
    dsimp only [Pphysical, preparedFiniteScheduleLocalPhysical, physical]
    linarith only [hcount, hnX, hQ.2, hkernel.2]
  have hspatial : coefficientErrorSpatialLog Pphysical ≤
      coefficientErrorSpatialLog physical := by
    unfold coefficientErrorSpatialLog coefficientErrorVolumeLog anisotropicSpatialCapLog
    gcongr
  refine ⟨hPEarly.trans hearlyCap, ⟨hgain.1, hgain.2.trans hearlyCap⟩,
    ⟨hkernel.1, hkernel.2.trans hearlyCap⟩, ⟨hactual0, hactual.trans hphysicalCap⟩, ?_⟩
  constructor
  · have hgain0 := hgain.1
    have hspatial0 := coefficientErrorSpatialLog_nonneg hactual0
    dsimp only [target]
    positivity
  · apply le_trans _ hprecisionCap
    dsimp only [target, precision]
    linarith only [hgain.2, hspatial]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem exists_preparedFiniteScheduleLocalResourceBudgetWithDegree
    (m degree Cdetect : ℕ) (K : PreparedModularCanonicalDetectorResourceConstants) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G : Type} [Fintype G] {count nX : ℕ}
      {P Bstruct pnum Pchart Qstride u pModel : ℝ},
      0 ≤ P → Bstruct ∈ Set.Icc 0 P → pnum ∈ Set.Icc 0 P →
      Pchart ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P →
      u ∈ Set.Icc 0 P → pModel ∈ Set.Icc 0 P →
      (count : ℝ) ≤ P → (nX : ℝ) ≤ P → (Fintype.card G : ℝ) ≤ P →
      let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
      let D := allocatedComparisonDimension m pnum
      let pDetect := allocatedModelTestLog u pModel
      let gainLog := slicedDetectionGainLog degree Cdetect count
        pDetect pDetect (2 * u + 4 * pModel + 7)
      let Pk := scalarKernelLogarithmicBudget (Fin (degree + 1)) G
        (gainLog + pDetect + 4)
      let Pphysical := preparedFiniteScheduleLocalPhysical m nX count Qstride Pk
      let target := gainLog + 40 + coefficientErrorSpatialLog Pphysical
      let Eprofile := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let Prho := 2 * affineProfileInputEnvelope D
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ)
        Eprofile (pDetect + 2) + 2
      let Pmaster := preparedFiniteScheduleLocalMaster Pchart D pRadius Qstride
        Pphysical u pModel Prho target gainLog
      ∀ L : ℝ,
      let r := preparedModularGeneralDetectorResources K (degree + 1) Pmaster L
      let budget := (P + C) ^ C
      Pmaster ∈ Set.Icc 0 budget ∧ r.Pnative ∈ Set.Icc 0 budget ∧
      r.nativeBudget ∈ Set.Icc 0 budget ∧ r.E ∈ Set.Icc 0 budget := by
  obtain ⟨Cp, _, hprecision⟩ :=
    exists_preparedFiniteScheduleLocalPrecisionBudgetWithDegree m degree Cdetect
  obtain ⟨Ce, _, hearly⟩ :=
    exists_preparedFiniteScheduleEarlyBudgetWithCutoff m degree 1 Cdetect
  obtain ⟨Cn, _, hnative⟩ :=
    exists_preparedModularGeneralDetector_early_native_budget K (degree + 1)
  let X : Polynomial ℕ := Polynomial.X
  let rawPoly := 7 * X + 12
  let precisionPoly := (rawPoly + Polynomial.C Cp) ^ Cp
  let earlyPoly := (precisionPoly + Polynomial.C Ce) ^ Ce
  let masterPoly := 17 * earlyPoly + 44
  let nativePoly := (2 * masterPoly + Polynomial.C Cn) ^ Cn
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget (masterPoly + nativePoly)
  refine ⟨C, hC, ?_⟩
  intro G _ count nX P Bstruct pnum Pchart Qstride u pModel
    hP hB hnum hchart hstride hu hmodel hcount hnX hG
    pRadius D pDetect gainLog Pk Pphysical target Eprofile Prho Pmaster L r budget
  let raw : ℝ := 7 * P + 12
  let precision : ℝ := (raw + Cp) ^ Cp
  let early : ℝ := (precision + Ce) ^ Ce
  let master : ℝ := 17 * early + 44
  let native : ℝ := (2 * master + Cn) ^ Cn
  have hraw0 : 0 ≤ raw := by dsimp only [raw]; positivity
  have hPraw : P ≤ raw := by dsimp only [raw]; linarith only [hP]
  have hp : pDetect ∈ Set.Icc 0 raw := by
    dsimp only [pDetect, allocatedModelTestLog, raw]
    constructor <;> linarith only [hu.1, hu.2, hmodel.1, hmodel.2]
  have ha : 2 * u + 4 * pModel + 7 ∈ Set.Icc 0 raw := by
    dsimp only [raw]
    constructor <;> linarith only [hu.1, hu.2, hmodel.1, hmodel.2, hP]
  have liftRaw {a : ℝ} (ha : a ∈ Set.Icc 0 P) : a ∈ Set.Icc 0 raw :=
    ⟨ha.1, ha.2.trans hPraw⟩
  obtain ⟨hrawPrecision, hgain, hkernel, hphysical, htarget⟩ :=
    hprecision (G := G) hraw0 hp ha (liftRaw hstride)
      (hcount.trans hPraw) (hnX.trans hPraw) (hG.trans hPraw)
  change raw ≤ precision at hrawPrecision
  change gainLog ∈ Set.Icc 0 precision at hgain
  change Pk ∈ Set.Icc 0 precision at hkernel
  change Pphysical ∈ Set.Icc 0 precision at hphysical
  change target ∈ Set.Icc 0 precision at htarget
  have hprecision0 : 0 ≤ precision := hraw0.trans hrawPrecision
  have hPprecision : P ≤ precision := hPraw.trans hrawPrecision
  have liftPrecision {a : ℝ} (ha : a ∈ Set.Icc 0 P) : a ∈ Set.Icc 0 precision :=
    ⟨ha.1, ha.2.trans hPprecision⟩
  obtain ⟨hprecisionEarly, hradius, hD, hdata⟩ :=
    hearly (fun _ : Unit => degree) (fun _ : Unit => Cdetect) (G := G)
      (fun _ => pDetect) (fun _ => 2 * u + 4 * pModel + 7) (fun _ => target)
      (by simp) (fun _ => le_rfl) (fun _ => le_rfl)
      hprecision0 (liftPrecision hB) (liftPrecision hnum)
      (fun _ => ⟨hp.1, hp.2.trans hrawPrecision⟩)
      (fun _ => ⟨ha.1, ha.2.trans hrawPrecision⟩) (liftPrecision hstride)
      (fun _ => htarget) (hcount.trans hPprecision) (hnX.trans hPprecision)
      (hG.trans hPprecision)
  change precision ≤ early at hprecisionEarly
  change pRadius ∈ Set.Icc 0 early at hradius
  change D ∈ Set.Icc 0 early at hD
  have hrho : Prho ∈ Set.Icc 0 early := (hdata ()).2.2.1
  have hearly0 : 0 ≤ early := hprecision0.trans hprecisionEarly
  have hPearly : P ≤ early := hPprecision.trans hprecisionEarly
  have hdetectEarly : pDetect ≤ early := hp.2.trans (hrawPrecision.trans hprecisionEarly)
  have hmaster0 : 0 ≤ Pmaster := by
    have hchart0 := hchart.1
    have hD0 := hD.1
    have hradius0 := hradius.1
    have hstride0 := hstride.1
    have hphysical0 := hphysical.1
    have hu0 := hu.1
    have hmodel0 := hmodel.1
    have hrho0 := hrho.1
    have htarget0 := htarget.1
    have hgain0 := hgain.1
    have hdetect0 := hp.1
    change 0 ≤ Pchart + D + pRadius + Qstride + Pphysical +
      (u + pModel + pDetect + Prho + target + gainLog + 32)
    positivity
  have hmaster : Pmaster ≤ master := by
    change Pchart + D + pRadius + Qstride + Pphysical +
      (u + pModel + pDetect + Prho + target + gainLog + 32) ≤ 17 * early + 44
    linarith only [hchart.2.trans hPearly, hD.2, hradius.2, hstride.2.trans hPearly,
      hphysical.2.trans hprecisionEarly, hu.2.trans hPearly, hmodel.2.trans hPearly,
      hdetectEarly, hrho.2, htarget.2.trans hprecisionEarly,
      hgain.2.trans hprecisionEarly, hearly0]
  have hmasterBound0 : 0 ≤ master := hmaster0.trans hmaster
  have hnativeBound0 : 0 ≤ native := by dsimp only [native]; positivity
  have htotal : master + native ≤ budget := by
    simpa [masterPoly, nativePoly, earlyPoly, precisionPoly, rawPoly, X,
      master, native, early, precision, raw, budget, Polynomial.eval₂_pow]
      using hpoly P hP
  have hmasterCap : master ≤ budget := by linarith only [htotal, hnativeBound0]
  have hnativeCap : native ≤ budget := by linarith only [htotal, hmasterBound0]
  have hraise : (2 * Pmaster + Cn) ^ Cn ≤ budget := by
    apply le_trans _ hnativeCap
    apply pow_le_pow_left₀ (by positivity)
    linarith only [hmaster]
  obtain ⟨hnative, hbudget, hE⟩ := hnative hmaster0 L
  exact ⟨⟨hmaster0, hmaster.trans hmasterCap⟩,
    ⟨hnative.1, hnative.2.trans hraise⟩,
    ⟨hbudget.1, hbudget.2.trans hraise⟩, ⟨hE.1, hE.2.trans hraise⟩⟩

theorem exists_preparedFiniteScheduleLocalResourceBudgetWithDegree_source_model
    (m degree Cdetect : ℕ) (K : PreparedModularCanonicalDetectorResourceConstants) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G : Type} [Fintype G] {count nX : ℕ}
      {Bstruct pnum Pchart Qstride u pModel : ℝ},
      0 ≤ u → 0 ≤ pModel →
      Bstruct ∈ Set.Icc 0 (u + pModel) → pnum ∈ Set.Icc 0 (u + pModel) →
      Pchart ∈ Set.Icc 0 (u + pModel) → Qstride ∈ Set.Icc 0 (u + pModel) →
      (count : ℝ) ≤ u + pModel → (nX : ℝ) ≤ u + pModel →
      (Fintype.card G : ℝ) ≤ u + pModel →
      let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
      let D := allocatedComparisonDimension m pnum
      let pDetect := allocatedModelTestLog u pModel
      let gainLog := slicedDetectionGainLog degree Cdetect count
        pDetect pDetect (2 * u + 4 * pModel + 7)
      let Pk := scalarKernelLogarithmicBudget (Fin (degree + 1)) G
        (gainLog + pDetect + 4)
      let Pphysical := preparedFiniteScheduleLocalPhysical m nX count Qstride Pk
      let target := gainLog + 40 + coefficientErrorSpatialLog Pphysical
      let Eprofile := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let Prho := 2 * affineProfileInputEnvelope D
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ)
        Eprofile (pDetect + 2) + 2
      let Pmaster := preparedFiniteScheduleLocalMaster Pchart D pRadius Qstride
        Pphysical u pModel Prho target gainLog
      ∀ L : ℝ,
      let r := preparedModularGeneralDetectorResources K (degree + 1) Pmaster L
      let budget := (u + pModel + C) ^ C
      Pmaster ∈ Set.Icc 0 budget ∧ r.Pnative ∈ Set.Icc 0 budget ∧
      r.nativeBudget ∈ Set.Icc 0 budget ∧ r.E ∈ Set.Icc 0 budget := by
  obtain ⟨C, hC, hbound⟩ := exists_preparedFiniteScheduleLocalResourceBudgetWithDegree m degree Cdetect K
  refine ⟨C, hC, ?_⟩
  intro G _ count nX Bstruct pnum Pchart Qstride u pModel
    hu hmodel hB hnum hchart hstride hcount hnX hG
  exact hbound (add_nonneg hu hmodel) hB hnum hchart hstride
    ⟨hu, le_add_of_nonneg_right hmodel⟩ ⟨hmodel, le_add_of_nonneg_left hu⟩
    hcount hnX hG

end Erdos3.VectorPolynomial

end

end OAI

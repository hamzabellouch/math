import OAI.Combinatorics.Progressions.Polynomial.PreparedFiniteScheduleLocalResourceBudgetWithDegree

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem exists_preparedFiniteScheduleUniformLocalResourceBudgetWithCutoff
    (m d : ℕ) (Pdetect : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ s : Fin (d + 1), ∀ {G : Type} [Fintype G] {count nX : ℕ}
      {P Bstruct pnum Pchart Qstride u pModel : ℝ},
      0 ≤ P → Bstruct ∈ Set.Icc 0 P → pnum ∈ Set.Icc 0 P →
      Pchart ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P →
      u ∈ Set.Icc 0 P → pModel ∈ Set.Icc 0 P →
      (count : ℝ) ≤ P → (nX : ℝ) ≤ P → (Fintype.card G : ℝ) ≤ P →
      let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
      let D := allocatedComparisonDimension m pnum
      let pDetect := allocatedModelTestLog u pModel
      let gainLog := slicedDetectionGainLog s.val (sampledSupportedSlicedDetectionConstant s.val Pdetect) count
        pDetect pDetect (2 * u + 4 * pModel + 7)
      let Pk := scalarKernelLogarithmicBudget (Fin (s.val + 1)) G
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
      let r := preparedModularGeneralDetectorResources
        (preparedModularGeneralDetectorConstants m s.val) (s.val + 1) Pmaster L
      let budget := (P + C) ^ C
      Pmaster ∈ Set.Icc 0 budget ∧ r.Pnative ∈ Set.Icc 0 budget ∧
      r.nativeBudget ∈ Set.Icc 0 budget ∧ r.E ∈ Set.Icc 0 budget := by
  let Cs (s : Fin (d + 1)) := Classical.choose
    (exists_preparedFiniteScheduleLocalResourceBudgetWithDegree m s.val
      (sampledSupportedSlicedDetectionConstant s.val Pdetect)
      (preparedModularGeneralDetectorConstants m s.val))
  let poly : Polynomial ℕ := ∑ s : Fin (d + 1),
    (Polynomial.X + Polynomial.C (Cs s)) ^ Cs s
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro s G _ count nX P Bstruct pnum Pchart Qstride u pModel
    hP hB hnum hchart hstride hu hmodel hcount hnX hG
    pRadius D pDetect gainLog Pk Pphysical target Eprofile Prho Pmaster L r budget
  have hbound : (P + Cs s) ^ Cs s ≤ budget := by
    have hsum : (P + Cs s) ^ Cs s ≤
        ∑ t : Fin (d + 1), (P + Cs t) ^ Cs t :=
      Finset.single_le_sum (f := fun t : Fin (d + 1) => (P + (Cs t : ℝ)) ^ Cs t)
        (fun t _ => by positivity) (Finset.mem_univ s)
    apply hsum.trans
    simpa [poly, budget, Polynomial.eval₂_finsetSum, Polynomial.eval₂_pow] using hpoly P hP
  have hlocal := (Classical.choose_spec
    (exists_preparedFiniteScheduleLocalResourceBudgetWithDegree m s.val
      (sampledSupportedSlicedDetectionConstant s.val Pdetect)
      (preparedModularGeneralDetectorConstants m s.val))).2
    (G := G) hP hB hnum hchart hstride hu hmodel
    hcount hnX hG L
  have lift {a : ℝ} (ha : a ∈ Set.Icc 0 ((P + Cs s) ^ Cs s)) :
      a ∈ Set.Icc 0 budget := ⟨ha.1, ha.2.trans hbound⟩
  exact ⟨lift hlocal.1, lift hlocal.2.1, lift hlocal.2.2.1, lift hlocal.2.2.2⟩

theorem exists_preparedFiniteScheduleUniformLocalResourceBudgetWithCutoff_source_model
    (m d : ℕ) (Pdetect : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ s : Fin (d + 1), ∀ {G : Type} [Fintype G] {count nX : ℕ}
      {Bstruct pnum Pchart Qstride u pModel : ℝ},
      0 ≤ u → 0 ≤ pModel →
      Bstruct ∈ Set.Icc 0 (u + pModel) → pnum ∈ Set.Icc 0 (u + pModel) →
      Pchart ∈ Set.Icc 0 (u + pModel) → Qstride ∈ Set.Icc 0 (u + pModel) →
      (count : ℝ) ≤ u + pModel → (nX : ℝ) ≤ u + pModel →
      (Fintype.card G : ℝ) ≤ u + pModel →
      let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
      let D := allocatedComparisonDimension m pnum
      let pDetect := allocatedModelTestLog u pModel
      let gainLog := slicedDetectionGainLog s.val (sampledSupportedSlicedDetectionConstant s.val Pdetect) count
        pDetect pDetect (2 * u + 4 * pModel + 7)
      let Pk := scalarKernelLogarithmicBudget (Fin (s.val + 1)) G
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
      let r := preparedModularGeneralDetectorResources
        (preparedModularGeneralDetectorConstants m s.val) (s.val + 1) Pmaster L
      let budget := (u + pModel + C) ^ C
      Pmaster ∈ Set.Icc 0 budget ∧ r.Pnative ∈ Set.Icc 0 budget ∧
      r.nativeBudget ∈ Set.Icc 0 budget ∧ r.E ∈ Set.Icc 0 budget := by
  obtain ⟨C, hC, hbound⟩ := exists_preparedFiniteScheduleUniformLocalResourceBudgetWithCutoff m d Pdetect
  refine ⟨C, hC, ?_⟩
  intro s G _ count nX Bstruct pnum Pchart Qstride u pModel
    hu hmodel hB hnum hchart hstride hcount hnX hG
  exact hbound s (add_nonneg hu hmodel) hB hnum hchart hstride
    ⟨hu, le_add_of_nonneg_right hmodel⟩ ⟨hmodel, le_add_of_nonneg_left hu⟩
    hcount hnX hG

end Erdos3.VectorPolynomial

end

end OAI

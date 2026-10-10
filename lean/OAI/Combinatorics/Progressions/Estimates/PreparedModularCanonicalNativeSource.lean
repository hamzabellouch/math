import OAI.Combinatorics.Progressions.Estimates.PreparedDetectedCanonicalNativeSource

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

theorem exists_prepared_modular_canonical_native_source (m Cdetect : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {X J₀ : Type} (L : RankPreparationFamily X J₀ m) {M nX : ℕ},
      (∀ j, Fintype.card (L j).Coord ≤ M) →
      let Jalloc := modularInitialBlockCount m (nX + m * M)
      let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M Jalloc
      ∀ {P pSlice u Qstride Eextra : ℝ},
      0 < m → 0 ≤ P → 0 ≤ Eextra → pnum ≤ P →
      pSlice ∈ Set.Icc 0 P → u ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P → (nX : ℝ) ≤ P →
      let G := EnlargedPreparedCommonKernel m Jalloc
      let I := PreparedSamplerContinuous L
      let n := preparedSamplerTransverse L
      let B := EnlargedPreparedCommonSamplerBlock L Jalloc
      let _selection := enlargedPreparedCommonCanonicalSelection m Jalloc 0 (Nat.zero_le m)
      let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let Pearly := P + (2 * P + A) ^ A + 2
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)
      let _T := allocatedIdealCoverSupport (G := G) B rowSets
      let _siteRadius := allocatedProductIdealSiteRadius (G := G) B rowSets
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let D := allocatedComparisonDimension m pnum
      let gainLog := slicedDetectionGainLog 0 Cdetect (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let target := gainLog + 32 + Eextra
      let Pk := scalarKernelLogarithmicBudget (Fin (0 + 1)) G (gainLog + pDetect + 4)
      let F := pDetect + 2
      let _Tmod := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
      let _δ := Real.exp (-(pDetect + 1))
      let E := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let _η := Real.exp (-E)
      let Prho := 2 * affineProfileInputEnvelope D (canonicalSublevelCutoffLip : ℝ)
        (canonicalTransitionLip : ℝ) E F + 2
      let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F
      let _K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
      let budget := (P + Eextra + C) ^ C
      ∃ (pRadius : ℝ) (R : Fin m → ℝ),
        pRadius ∈ Set.Icc 0 Pearly ∧ pRadius ≤ budget ∧
        (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
        pModel ∈ Set.Icc 0 budget ∧ pDetect ∈ Set.Icc 0 budget ∧
        gainLog ∈ Set.Icc 0 budget ∧ target ∈ Set.Icc 0 budget ∧
        ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
        ∀ {J : Fin m → Type} [∀ j, Fintype (J j)]
          (U : ∀ j, Submodule ℝ (J j → ℝ))
          (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
          let Pscale := pRadius + Ptail
          ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
            Pscale ∈ Set.Icc 0 budget ∧ Pk ≤ Pscale ∧ (S.value : ℝ) ≤ Real.exp budget ∧
            Nonempty (AllocatedEarlyNativeSourceGeometry (B := B) (U := U) (basis := basis) (S := S) (nX := nX)
              P Pscale D target Pk Prho Qstride pDetect (Real.toNNReal (Real.exp pRadius))) ∧
            ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
              Real.exp (-gainLog) ≤
                (Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                  Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1)) ∧
              (scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
                (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                  Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) : ℝ) ≤ Real.exp Pk ∧
              scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
                (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                  Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (0 + 1))) / 2) ≤ S.value := by
  obtain ⟨C, hC, hsource⟩ := exists_detected_canonical_native_source m Cdetect
  refine ⟨C, hC, ?_⟩
  intro X J₀ L M nX hM Jalloc pnum P pSlice u Qstride Eextra hm hP hExtra hnum
    hpSlice hu hQstride hnX G I n B selection A Pearly rowSets T siteRadius
    pModel pDetect aDetect D gainLog target Pk F Tmod δ E η Prho Ptail K budget
  obtain ⟨hvars, hI, hn⟩ := enlargedPreparedCommonSampler_dimensions L Jalloc hM
  have hblocks (a : LayerSamplerAxis I n) :
      (boundedBooleanJetRows (Fin (0 + 1)) (a.1.val + 1)).card ≤ Fintype.card (B a) := by
    calc
      _ = Fintype.card (BoundedBooleanJet (Fin (0 + 1)) (a.1.val + 1)) :=
        (Fintype.card_coe _).symm.trans (Fintype.card_congr (boundedBooleanJetRowsEquiv _ _))
      _ ≤ _ := enlargedPreparedCommonSamplerBlock_jets L Jalloc 0 (Nat.zero_le m) a
  exact hsource (G := G) B hm hP hExtra
    ⟨Nat.cast_nonneg _, hnum⟩ (Nat.cast_le.mpr hvars)
    (fun j => Nat.cast_le.mpr (hI j)) (fun j => Nat.cast_le.mpr (hn j))
    hblocks hpSlice hu hQstride hnX

end Erdos3.VectorPolynomial

end

end OAI

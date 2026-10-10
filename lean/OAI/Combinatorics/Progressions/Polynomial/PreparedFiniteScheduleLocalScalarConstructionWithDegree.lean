import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleLocalScalarConstruction

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem preparedFiniteScheduleDirectScalarBoundsWithDegree_explicit
    (m : ℕ) {K : Type*} [Fintype K] (degree Cdetect : K → ℕ)
    (G : Type) [Fintype G]
    (nX count : ℕ) (Pchart D pRadius Qstride Pscale requestedCoarse extraLate : ℝ)
    (u pModel pSlice Prho : K → ℝ)
    (hchart : 0 ≤ Pchart) (hD : 0 ≤ D) (hradius : 0 ≤ pRadius)
    (hu : ∀ k, 0 ≤ u k) (hmodel : ∀ k, 0 ≤ pModel k) (hstride : 0 ≤ Qstride)
    (hrho : ∀ k, 0 ≤ Prho k) (hslice : ∀ k, pSlice k ≤ pModel k)
    (hcount : ∀ k, (count : ℝ) ≤ Real.exp (pModel k)) :
    let pDetect := fun k => allocatedModelTestLog (u k) (pModel k)
    let gainLog := fun k => slicedDetectionGainLog (degree k) (Cdetect k) count
      (pDetect k) (pDetect k) (2 * u k + 4 * pModel k + 7)
    let Pk := fun k => scalarKernelLogarithmicBudget (Fin (degree k + 1)) G
      (gainLog k + pDetect k + 4)
    let Pphysical : ℝ := ((m + 2 : ℕ) : ℝ) + nX + count + Qstride + ∑ k, Pk k
    let target := fun k => gainLog k + 40 + coefficientErrorSpatialLog Pphysical
    let Pmaster := preparedFiniteScheduleDirectMaster Pchart D pRadius Qstride
      Pphysical u pModel Prho target gainLog
    let coarseTarget := preparedFiniteScheduleDirectCoarse gainLog requestedCoarse
    let Plate := preparedUniformDegreeDirectLate Pmaster Pscale Pphysical coarseTarget extraLate
    (∀ k, Pk k ≤ Pscale) → ∀ k,
      PreparedUniformDegreeDirectScalarBounds m (degree k) nX count (Cdetect k)
        Pchart Pscale D (target k) (Pk k) (Prho k) Qstride Pmaster Plate
        (gainLog k) Pphysical coarseTarget pRadius (u k) (pModel k) (pSlice k) := by
  intro pDetect gainLog Pk Pphysical target Pmaster coarseTarget Plate hkernelScale
  have hp (k) : 0 ≤ pDetect k := by
    dsimp only [pDetect, allocatedModelTestLog]
    have := hu k
    have := hmodel k
    positivity
  have ha (k) : 0 ≤ 2 * u k + 4 * pModel k + 7 := by
    have := hu k
    have := hmodel k
    positivity
  have hg (k) : 0 ≤ gainLog k :=
    slicedDetectionGainLog_nonneg (degree k) (Cdetect k) count (hp k) (hp k) (ha k)
  have hk (k) : 0 ≤ Pk k := by
    dsimp only [Pk]
    rw [scalarKernelLogarithmicBudget_eq]
    have := hg k
    have := hp k
    positivity
  have hkSum0 : 0 ≤ ∑ k, Pk k := Finset.sum_nonneg (fun k _ => hk k)
  have hkSum (k) : Pk k ≤ ∑ t, Pk t :=
    Finset.single_le_sum (fun t _ => hk t) (Finset.mem_univ k)
  have hphysEq : Pphysical = (m : ℝ) + 2 + nX + count + Qstride + ∑ k, Pk k := by
    simp only [Pphysical, Nat.cast_add, Nat.cast_ofNat]
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hnX0 : (0 : ℝ) ≤ nX := Nat.cast_nonneg nX
  have hcount0 : (0 : ℝ) ≤ count := Nat.cast_nonneg count
  have hphysical0 : 0 ≤ Pphysical := by
    linarith only [hphysEq, hm0, hnX0, hcount0, hstride, hkSum0]
  have hkernelPhysical (k) : Pk k ≤ Pphysical := by
    linarith only [hphysEq, hm0, hnX0, hcount0, hstride, hkSum k]
  have herror0 := coefficientErrorSpatialLog_nonneg hphysical0
  have ht (k) : 0 ≤ target k := by
    dsimp only [target]
    have := hg k
    positivity
  let total := ∑ k, (u k + pModel k + pDetect k + Prho k + target k + gainLog k + 32)
  have hentry (k) : 0 ≤ u k + pModel k + pDetect k + Prho k + target k + gainLog k + 32 := by
    have := hu k
    have := hmodel k
    have := hp k
    have := hrho k
    have := ht k
    have := hg k
    positivity
  have htotal0 : 0 ≤ total := Finset.sum_nonneg (fun k _ => hentry k)
  have htotal (k) : u k + pModel k + pDetect k + Prho k + target k + gainLog k + 32 ≤ total :=
    Finset.single_le_sum (fun k _ => hentry k) (Finset.mem_univ k)
  have hmasterEq : Pmaster = Pchart + D + pRadius + Qstride + Pphysical + total := rfl
  have hmaster0 : 0 ≤ Pmaster := by
    linarith only [hmasterEq, hchart, hD, hradius, hstride, hphysical0, htotal0]
  have hphysicalMaster : Pphysical ≤ Pmaster := by
    linarith only [hmasterEq, hchart, hD, hradius, hstride, htotal0]
  have htotalMaster : total ≤ Pmaster := by
    linarith only [hmasterEq, hchart, hD, hradius, hstride, hphysical0]
  have hlate : Pmaster ≤ Plate := le_max_left _ _
  have hscaleLate : Pscale ≤ Plate := (le_max_left _ _).trans (le_max_right _ _)
  have hcoarseLate : coarseTarget ≤ Plate :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hxiLate : 2 * (spatialPrimitiveEnvelope Pphysical coarseTarget 0 +
      spatialTupleToleranceLog (spatialPrimitiveEnvelope Pphysical coarseTarget 0)) + 4
      ≤ Plate :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  intro k
  have hdetectorKernel : ((degree k + 2 : ℕ) : ℝ) ≤ Pk k := by
    dsimp only [Pk]
    rw [scalarKernelLogarithmicBudget_eq]
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    let T : ℝ := 10 + ((degree k : ℝ) + 1) + Fintype.card G +
      Fintype.card G * ((degree k : ℝ) + 1 + 1) + (gainLog k + pDetect k + 4)
    have hT : (degree k : ℝ) + 2 ≤ T := by
      dsimp only [T]
      have hprod : 0 ≤ (Fintype.card G : ℝ) * ((degree k : ℝ) + 1 + 1) := by positivity
      have hd0 : (0 : ℝ) ≤ degree k := Nat.cast_nonneg _
      have hG0 : (0 : ℝ) ≤ Fintype.card G := Nat.cast_nonneg _
      linarith only [hg k, hp k, hprod, hd0, hG0]
    have hT1 : 1 ≤ T := by
      have hd0 : (0 : ℝ) ≤ degree k := Nat.cast_nonneg _
      linarith only [hT, hd0]
    have hcube : T ≤ T^3 := by
      calc
        T = T^1 := by simp
        _ ≤ T^3 := pow_le_pow_right₀ hT1 (by decide)
    have hprod : 0 ≤ 3 * ((Fintype.card G : ℝ) * ((degree k : ℝ) + 1 + 1) *
        ((degree k : ℝ) + 1)) := by positivity
    change (degree k : ℝ) + 2 ≤
      2 * ((4 + 3 * ((Fintype.card G : ℝ) * ((degree k : ℝ) + 1 + 1) *
        ((degree k : ℝ) + 1))) * (16 * T^3 + 2)) + 8
    have hcube0 : 0 ≤ T^3 := (zero_le_one.trans hT1).trans hcube
    nlinarith [mul_nonneg hprod (show 0 ≤ 16 * T^3 + 2 by positivity)]
  have hlocalMaster := (htotal k).trans htotalMaster
  have hgainEntry (t : K) : (0 : ℝ) ≤ gainLog t + 32 := by
    have := hg t
    positivity
  have hcoarseSum : gainLog k + 32 ≤ ∑ t, (gainLog t + 32) :=
    Finset.single_le_sum (fun t _ => hgainEntry t) (Finset.mem_univ k)
  refine {
    master_nonneg := hmaster0
    late := hlate
    chart_master := ?_
    dimension_master := ?_
    radius_master := ?_
    scale_late := hscaleLate
    kernel_scale := hkernelScale k
    kernel_master := ⟨hk k, (hkernelPhysical k).trans hphysicalMaster⟩
    stride_master := ⟨hstride, ?_⟩
    detect_master := ⟨hp k, ?_⟩
    ambient_master := le_trans ?_ hphysicalMaster
    u_master := ⟨hu k, ?_⟩
    model_master := ⟨hmodel k, ?_⟩
    slice_model := hslice k
    count_model := hcount k
    rho_master := ⟨hrho k, ?_⟩
    target_master := ⟨ht k, ?_⟩
    gain_master := ⟨hg k, ?_⟩
    coarse_master := ?_
    coarse_lower := hcoarseSum.trans (le_max_left _ _)
    coarse_late := hcoarseLate
    physical_master := ⟨hphysical0, hphysicalMaster⟩
    degree_physical := ?_
    detector_physical := ?_
    variables_physical := ?_
    ambient_physical := ?_
    kernel_physical := hkernelPhysical k
    stride_physical := ?_
    gain_log := le_rfl
    precision := ?_
    xi_late := hxiLate }
  · linarith only [hmasterEq, hD, hradius, hstride, hphysical0, htotal0]
  · linarith only [hmasterEq, hchart, hradius, hstride, hphysical0, htotal0]
  · linarith only [hmasterEq, hchart, hD, hstride, hphysical0, htotal0]
  · linarith only [hmasterEq, hchart, hD, hradius, hphysical0, htotal0]
  · linarith only [hlocalMaster, hu k, hmodel k, hrho k, ht k, hg k]
  · linarith only [hphysEq, hm0, hcount0, hstride, hkSum0]
  · linarith only [hlocalMaster, hmodel k, hp k, hrho k, ht k, hg k]
  · linarith only [hlocalMaster, hu k, hp k, hrho k, ht k, hg k]
  · linarith only [hlocalMaster, hu k, hmodel k, hp k, ht k, hg k]
  · linarith only [hlocalMaster, hu k, hmodel k, hp k, hrho k, hg k]
  · linarith only [hlocalMaster, hu k, hmodel k, hp k, hrho k, ht k]
  · linarith only [hlocalMaster, hu k, hmodel k, hp k, hrho k, ht k]
  · simp only [Nat.cast_add, Nat.cast_one]
    linarith only [hphysEq, hnX0, hcount0, hstride, hkSum0]
  · simp only [Nat.cast_add, Nat.cast_ofNat]
    have hkSum := hkSum k
    simp only [Nat.cast_add, Nat.cast_ofNat] at hdetectorKernel
    linarith only [hphysEq, hdetectorKernel, hkSum, hm0, hnX0, hcount0, hstride]
  · linarith only [hphysEq, hm0, hnX0, hstride, hkSum0]
  · linarith only [hphysEq, hm0, hcount0, hstride, hkSum0]
  · linarith only [hphysEq, hm0, hnX0, hcount0, hkSum0]
  · dsimp only [target]
    linarith only

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem preparedFiniteScheduleLocalScalarBoundsWithDegree_explicit
    (m degree Cdetect : ℕ) (G : Type) [Fintype G]
    (nX count : ℕ) (Pchart D pRadius Qstride Pscale coarseTarget extraLate : ℝ)
    (u pModel pSlice Prho : ℝ)
    (hchart : 0 ≤ Pchart) (hD : 0 ≤ D) (hradius : 0 ≤ pRadius)
    (hu : 0 ≤ u) (hmodel : 0 ≤ pModel) (hstride : 0 ≤ Qstride)
    (hrho : 0 ≤ Prho) (hslice : pSlice ≤ pModel)
    (hcount : (count : ℝ) ≤ Real.exp pModel) :
    let pDetect := allocatedModelTestLog u pModel
    let gainLog := slicedDetectionGainLog degree Cdetect count
      pDetect pDetect (2 * u + 4 * pModel + 7)
    let Pk := scalarKernelLogarithmicBudget (Fin (degree + 1)) G
      (gainLog + pDetect + 4)
    let Pphysical := preparedFiniteScheduleLocalPhysical m nX count Qstride Pk
    let target := gainLog + 40 + coefficientErrorSpatialLog Pphysical
    let Pmaster := preparedFiniteScheduleLocalMaster Pchart D pRadius Qstride
      Pphysical u pModel Prho target gainLog
    let localLate := preparedUniformDegreeDirectLate Pmaster Pscale Pphysical
      coarseTarget extraLate
    Pk ≤ Pscale → gainLog + 32 ≤ coarseTarget →
    ∀ {Plate : ℝ}, localLate ≤ Plate →
      PreparedUniformDegreeDirectScalarBounds m degree nX count Cdetect
        Pchart Pscale D target Pk Prho Qstride Pmaster Plate gainLog
        Pphysical coarseTarget pRadius u pModel pSlice := by
  intro pDetect gainLog Pk Pphysical target Pmaster localLate hkernel hcoarse Plate hLate
  have h := preparedFiniteScheduleDirectScalarBoundsWithDegree_explicit
    m (fun _ : Unit => degree) (fun _ : Unit => Cdetect) G
    nX count Pchart D pRadius Qstride Pscale coarseTarget extraLate
    (fun _ => u) (fun _ => pModel) (fun _ => pSlice) (fun _ => Prho)
    hchart hD hradius (fun _ => hu) (fun _ => hmodel) hstride
    (fun _ => hrho) (fun _ => hslice) (fun _ => hcount)
    (fun _ => hkernel) ()
  have hlocal : PreparedUniformDegreeDirectScalarBounds m degree nX count Cdetect
      Pchart Pscale D target Pk Prho Qstride Pmaster localLate gainLog
      Pphysical coarseTarget pRadius u pModel pSlice := by
    simpa only [preparedFiniteScheduleDirectMaster, preparedFiniteScheduleDirectCoarse,
      Finset.univ_unique, Finset.sum_singleton, max_eq_right hcoarse,
      Pmaster, Pphysical, target, localLate, gainLog, pDetect, Pk,
      preparedFiniteScheduleLocalPhysical, preparedFiniteScheduleLocalMaster] using h
  exact hlocal.late_mono hLate

end Erdos3.VectorPolynomial

end

end OAI

import OAI.Combinatorics.Progressions.Dynamics.PreparedDetectedCanonicalNativeSourceScaleBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

private theorem exists_preparedCanonicalGeometry_extra_budget (A C : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {P Eextra : ℝ}, 0 ≤ P → 0 ≤ Eextra →
      let Q := P + (2 * P + A) ^ A + 2
      0 ≤ Q ∧ P ≤ Q ∧ (P + P + A) ^ A ≤ Q ∧
        (Q + Eextra + C) ^ C ≤ (P + Eextra + D) ^ D := by
  obtain ⟨D, hD, hbound⟩ := exists_preparedCanonicalGeometry_budget A C
  refine ⟨D, hD, ?_⟩
  intro P Eextra hP hE Q
  obtain ⟨hQ, hPQ, hAQ, _⟩ := hbound hP
  refine ⟨hQ, hPQ, hAQ, ?_⟩
  have hpow : (2 * P + A) ^ A ≤ (2 * (P + Eextra) + A) ^ A :=
    pow_le_pow_left₀ (by positivity) (by linarith) A
  have hbase : Q + Eextra + C ≤
      (P + Eextra) + (2 * (P + Eextra) + A) ^ A + 2 + C := by
    dsimp only [Q]
    linarith only [hpow]
  exact (pow_le_pow_left₀
    (add_nonneg (add_nonneg hQ hE) (Nat.cast_nonneg C)) hbase C).trans
      (hbound (add_nonneg hP hE)).2.2.2

private theorem chart_budget_le_exp {a v r p : ℝ}
    (ha : 1 ≤ a) (hv : 0 ≤ v) (hr : 0 < r) (hinv : r⁻¹ ≤ Real.exp p)
    (hbudget : a * (v * r) ≤ 1 / 4) : v ≤ Real.exp p := by
  have hmul : v * r ≤ a * (v * r) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ha (mul_nonneg hv hr.le)
  have hunit : v * r ≤ 1 := hmul.trans (hbudget.trans (by norm_num))
  exact ((le_div_iff₀ hr).mpr hunit).trans (by simpa only [one_div] using hinv)

private theorem coefficient_count_add_one_le_support {K : Type*} [Fintype K]
    (s h : ℕ) {T : ℝ}
    (hsource : (Fintype.card (BoundedCoefficientExponent K h) : ℝ) *
      ((2 : ℝ) ^ Fintype.card (Fin (s + 1)) *
        ((Fintype.card (Fin (s + 1)) : ℝ) + 1) ^ h) ≤ T) :
    (Fintype.card (BoundedCoefficientExponent K h) : ℝ) + 1 ≤ T := by
  have hc : (1 : ℝ) ≤ Fintype.card (BoundedCoefficientExponent K h) := by
    have hpos : 0 < Fintype.card (BoundedCoefficientExponent K h) :=
      Fintype.card_pos_iff.mpr ⟨⟨0, by simp⟩⟩
    exact_mod_cast hpos
  have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ Fintype.card (Fin (s + 1)) := by
    rw [Fintype.card_fin, pow_succ]
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ s := one_le_pow₀ (by norm_num)
    linarith
  have hone : (1 : ℝ) ≤ (((Fintype.card (Fin (s + 1)) : ℝ) + 1) ^ h) :=
    one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg _))
  have hfactor : (2 : ℝ) ≤ (2 : ℝ) ^ Fintype.card (Fin (s + 1)) *
      (((Fintype.card (Fin (s + 1)) : ℝ) + 1) ^ h) := by
    simpa only [mul_one] using mul_le_mul htwo hone (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ Fintype.card (Fin (s + 1)))
  have hmult := mul_le_mul_of_nonneg_left hfactor (Nat.cast_nonneg
    (Fintype.card (BoundedCoefficientExponent K h)))
  linarith

theorem exists_prepared_detected_canonical_native_source_geometry (m s Cdetect : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {X J₀ : Type} (L : RankPreparationFamily X J₀ m) {M : ℕ},
      (∀ j, Fintype.card (L j).Coord ≤ M) →
      let pnum : ℝ := preparedCommonSamplerDimension m M
      ∀ {P pSlice u Qstride Eextra : ℝ} {nX : ℕ},
      0 < m → ∀ hs : s ≤ m, 0 ≤ P → 0 ≤ Eextra → pnum ≤ P →
      pSlice ∈ Set.Icc 0 P → u ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P → (nX : ℝ) ≤ P →
      let G := PreparedCommonKernel m
      let I := PreparedSamplerContinuous L
      let n := preparedSamplerTransverse L
      let B := PreparedCommonSamplerBlock L
      let selection := preparedCommonCanonicalSelection m s hs
      let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
      let Pearly := P + (2 * P + A) ^ A + 2
      let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)
      let T := allocatedIdealCoverSupport (G := G) B rowSets
      let siteRadius := allocatedProductIdealSiteRadius (G := G) B rowSets
      let pModel := allocatedEarlyModelLog Pearly pSlice (Fintype.card (LayerSamplerVariables G I n B))
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let D := allocatedComparisonDimension m pnum
      let gainLog := slicedDetectionGainLog s Cdetect (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
      let target := gainLog + 32 + Eextra
      let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + pDetect + 4)
      let F := pDetect + 2
      let Tmod := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
      let δ := Real.exp (-(pDetect + 1))
      let E := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let η := Real.exp (-E)
      let Prho := 2 * affineProfileInputEnvelope D (canonicalSublevelCutoffLip : ℝ)
        (canonicalTransitionLip : ℝ) E F + 2
      let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F
      let K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
      let budget := (P + Eextra + C) ^ C
      ∃ (pRadius : ℝ) (R : Fin m → ℝ),
      pRadius ∈ Set.Icc 0 Pearly ∧ pRadius ≤ budget ∧
      (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      1 ≤ siteRadius ∧ (∀ j, 0 ≤ T j) ∧
      (∀ j, partitionedIdealRadius (Fin (s + 1)) m + 1 ≤ T j) ∧
      (∀ j, (Fintype.card (BoundedCoefficientExponent
        (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
          ((2 : ℝ) ^ Fintype.card (Fin (s + 1)) *
            ((Fintype.card (Fin (s + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j) ∧
      (∀ j, (rowSets j).card * T j ≤ (siteRadius : ℝ)) ∧
      (∀ j, T j ≤ Real.exp pRadius) ∧ 2 * (siteRadius : ℝ) ≤ Real.exp pRadius ∧
      (∀ j, T j ≤ Real.exp budget) ∧ 2 * (siteRadius : ℝ) ≤ Real.exp budget ∧
      (∀ Cchart : Fin m → ℝ, (∀ j, 0 ≤ Cchart j) → (∀ j, Cchart j ≤ Real.exp P) →
        (∀ j, Cchart j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) ∧
        (∀ j, Cchart j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
        (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin (s + 1))) *
          (Cchart j * (((Fintype.card (I j) : ℝ) + 1) *
            (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4)) ∧
      AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) (fun j => (rowSets j : Type)) D ∧
      ((s + 1) * ((s + 1) + 2) ≤ Fintype.card G) ∧
      (∀ i, (selection i).val = i.val) ∧
      P ≤ Pearly ∧ Pearly ≤ budget ∧ pModel ∈ Set.Icc 0 budget ∧ pDetect ∈ Set.Icc 0 budget ∧
      aDetect ∈ Set.Icc 0 budget ∧ target ∈ Set.Icc 0 budget ∧ D ∈ Set.Icc 0 budget ∧ gainLog ∈ Set.Icc 0 budget ∧ Pk ∈ Set.Icc 0 budget ∧
      Prho ∈ Set.Icc 0 budget ∧ Ptail ∈ Set.Icc 0 budget ∧ Tmod ∈ Set.Icc 0 budget ∧
      ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
        (∀ partition, 0 < ρ partition ∧ ρ partition ≤ 1 ∧
          (ρ partition : ℝ)⁻¹ ≤ Real.exp Prho ∧ (ρ partition : ℝ)⁻¹ ≤ Real.exp budget) ∧
      ∃ t : ℝ, 0 < t ∧ ∃ htone : t ≤ 1,
        t⁻¹ ≤ Real.exp Ptail ∧ t⁻¹ ≤ Real.exp budget ∧
        AllocatedAffineCoveredComparison.{uJ,uQ,_,_,_,_,_} (G := G) B
          (fun j : Fin m => (Subtype.val :
            boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) → Finset (Fin (s + 1))))
          δ η ρ t htone ∧
        ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
          (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
          let Pscale := pRadius + Ptail
          let scaleLog := (D + Pscale + Prho + Pk + target + F + Tmod + K) ^ K
          Pscale ∈ Set.Icc 0 budget ∧ scaleLog ∈ Set.Icc 0 budget ∧
          ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
            (∀ j, (R j)⁻¹ ≤ Real.exp Pscale) ∧
            (∀ j : Fin m, ((fun _ => t) j)⁻¹ ≤ Real.exp Pscale) ∧
            (∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
              (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp Pscale) ∧
            Real.exp (allocatedAffineLengthLog m D Pscale Prho Pk target F Tmod) ≤ S.value ∧
            (S.value : ℝ) ≤ Real.exp budget ∧
            ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
              scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊
                (((Real.exp (-((5 * pDetect + 20) * Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
                  Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1))) / 2) ≤ S.value := by
  let A := Classical.choose (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)
  obtain ⟨Cscale, hCscale, hscales⟩ := exists_prepared_detected_canonical_native_source_scales.{uJ,uQ} m s Cdetect
  obtain ⟨C, hC, hcompose⟩ := exists_preparedCanonicalGeometry_extra_budget A Cscale
  refine ⟨C, hC, ?_⟩
  intro X J₀ L M hM pnum P pSlice u Qstride Eextra nX hm hs hP hExtra hnum hpSlice hu hQstride hnX
    G I n B selection A' Pearly rowSets T siteRadius pModel pDetect aDetect D gainLog target Pk F Tmod
    δ E η Prho Ptail K budget
  have hcompose' := hcompose hP hExtra
  change 0 ≤ Pearly ∧ P ≤ Pearly ∧ (P + P + A') ^ A' ≤ Pearly ∧
    (Pearly + Eextra + Cscale) ^ Cscale ≤ budget at hcompose'
  obtain ⟨hPearly, hPEarly, hRadiusEarly, hScaleBudget⟩ := hcompose'
  obtain ⟨hvars, hI, hn⟩ := preparedCommonSampler_dimensions L hM
  have hdim : Fintype.card (Fin (s + 1)) ≤ m + 1 := by simpa using Nat.succ_le_succ hs
  have hdimensions : AllocatedComparisonDimensions (G := G) B (Fin (s + 1))
      (fun j => (rowSets j : Type)) D :=
    allocatedComparisonDimensions_of_primitive (G := G) B
      (fun j => (Subtype.val : rowSets j → Finset (Fin (s + 1)))) hdim
      (fun _ => Subtype.val_injective) (Nat.cast_nonneg _)
      (Nat.cast_le.mpr hvars) (fun j => Nat.cast_le.mpr (hI j)) (fun j => Nat.cast_le.mpr (hn j))
  let : ∀ j : Fin m, Nonempty (rowSets j) := fun j =>
    ⟨⟨∅, (mem_boundedBooleanJetRows (j.val + 1) ∅).mpr (by simp)⟩⟩
  obtain ⟨pRadius, R, hpRadius, hR, hrone, hT0, hTideal, hTsource, hTradius, hsmall⟩ :=
    (Classical.choose_spec (exists_allocatedCanonicalSlice_early_radius.{0,0,0,0} m)).2
      (G := G) B rowSets hP hP hdim
      ((Nat.cast_le.mpr hvars).trans hnum)
      (fun j => (Nat.cast_le.mpr (hI j)).trans hnum)
      (fun j => (Nat.cast_le.mpr (hn j)).trans hnum)
  have hpRadiusEarly : pRadius ∈ Set.Icc 0 Pearly := ⟨hpRadius.1, hpRadius.2.trans hRadiusEarly⟩
  have hactual := hscales L hM (P := Pearly) hm hs hPearly hExtra (hnum.trans hPEarly)
    ⟨hpSlice.1, hpSlice.2.trans hPEarly⟩ ⟨hu.1, hu.2.trans hPEarly⟩
    ⟨hQstride.1, hQstride.2.trans hPEarly⟩ (hnX.trans hPEarly)
  obtain ⟨hcapacity, hselection, hPbudget, hpModel, hpDetect, haDetect, htarget, hD,
    hgain, hPk, hPrho, hPtail, hTmod, ρ, hρ, t, ht, htone, htinv, htbudget, hcomparison, hsampler⟩ := hactual
  have hPearlyBudget : Pearly ≤ budget := hPbudget.trans hScaleBudget
  have hRadBudget : pRadius ≤ budget := hpRadiusEarly.2.trans hPearlyBudget
  have hexp : Real.exp ((Pearly + Eextra + Cscale) ^ Cscale) ≤ Real.exp budget :=
    Real.exp_le_exp.mpr hScaleBudget
  have hOne := hsmall (fun _ => 1) (fun _ => by norm_num) (fun _ => Real.one_le_exp hP)
  have hTbound (j) : T j ≤ Real.exp pRadius := by
    have ha : 1 ≤ (Fintype.card (I j) : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
    apply chart_budget_le_exp ha (hT0 j) (hR j).1
      (hR j).2.2
    simpa only [one_mul] using hOne.2.1 j
  have hrbound : 2 * (siteRadius : ℝ) ≤ Real.exp pRadius := by
    let j : Fin m := ⟨0, hm⟩
    have ha : 1 ≤ (Fintype.card (I j) : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
    have hb : 1 ≤ ((rowSets j).card : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
    have hc : (1 : ℝ) ≤ Fintype.card (Finset (Fin (s + 1))) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Finset (Fin (s + 1)))))
    have hfactor : 1 ≤ (((rowSets j).card : ℝ) + 1) *
        ((Fintype.card (Finset (Fin (s + 1))) : ℝ) * ((Fintype.card (I j) : ℝ) + 1)) :=
      one_le_mul_of_one_le_of_one_le hb (one_le_mul_of_one_le_of_one_le hc ha)
    apply chart_budget_le_exp hfactor (mul_nonneg (by norm_num) siteRadius.coe_nonneg) (hR j).1
      (hR j).2.2
    simpa only [mul_assoc, one_mul] using hOne.2.2 j
  refine ⟨pRadius, R, hpRadiusEarly, hRadBudget, hR, hrone, hT0, hTideal, hTsource,
    hTradius, hTbound, hrbound,
    fun j => (hTbound j).trans (Real.exp_le_exp.mpr hRadBudget),
    hrbound.trans (Real.exp_le_exp.mpr hRadBudget), hsmall, hdimensions, hcapacity, hselection, hPEarly, hPearlyBudget,
    ⟨hpModel.1, hpModel.2.trans hScaleBudget⟩,
    ⟨hpDetect.1, hpDetect.2.trans hScaleBudget⟩,
    ⟨haDetect.1, haDetect.2.trans hScaleBudget⟩,
    ⟨htarget.1, htarget.2.trans hScaleBudget⟩,
    ⟨hD.1, hD.2.trans hScaleBudget⟩,
    ⟨hgain.1, hgain.2.trans hScaleBudget⟩,
    ⟨hPk.1, hPk.2.trans hScaleBudget⟩,
    ⟨hPrho.1, hPrho.2.trans hScaleBudget⟩,
    ⟨hPtail.1, hPtail.2.trans hScaleBudget⟩,
    ⟨hTmod.1, hTmod.2.trans hScaleBudget⟩, ρ,
    fun partition => ⟨(hρ partition).1, (hρ partition).2.1, (hρ partition).2.2.1,
      (hρ partition).2.2.2.trans hexp⟩,
    t, ht, htone, htinv, htbudget.trans hexp, hcomparison, ?_⟩
  intro J _ U basis Pscale scaleLog
  obtain ⟨hPscale, hScaleLog, S, hRinv, htinv', hlength, hS, hcutoff⟩ :=
    hsampler U basis R (fun j => (hR j).1) hpRadiusEarly (fun j => (hR j).2.2)
  exact ⟨⟨hPscale.1, hPscale.2.trans hScaleBudget⟩,
    ⟨hScaleLog.1, hScaleLog.2.trans hScaleBudget⟩, S, hRinv, htinv',
    fun j => ((coefficient_count_add_one_le_support s (j.val + 1) (hTsource j)).trans
      (hTbound j)).trans (Real.exp_le_exp.mpr (le_add_of_nonneg_right hPtail.1)),
    hlength, hS.trans hexp, hcutoff⟩

end Erdos3.VectorPolynomial

end

end OAI

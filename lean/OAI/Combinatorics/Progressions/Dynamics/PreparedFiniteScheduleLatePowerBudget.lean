import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleLocalScalarConstruction

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem exists_preparedFiniteScheduleLate_power_budget
    (stageCount inputPower : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {Stage : Type*} [Fintype Stage] {B Pscale extraLate requestedCoarse : ℝ}
        (Pmaster Pphysical detectionGain : Stage → ℝ),
        Fintype.card Stage ≤ stageCount → 0 ≤ B →
        (∀ k, Pmaster k ∈ Set.Icc 0 ((B + 2) ^ inputPower)) →
        (∀ k, Pphysical k ∈ Set.Icc 0 ((B + 2) ^ inputPower)) →
        (∀ k, detectionGain k ∈ Set.Icc 0 ((B + 2) ^ inputPower)) →
        Pscale ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
        extraLate ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
        requestedCoarse ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
        let coarseTarget := preparedFiniteScheduleDirectCoarse detectionGain requestedCoarse
        let Plate := ∑ k, preparedUniformDegreeDirectLate (Pmaster k) Pscale
          (Pphysical k) coarseTarget extraLate
        coarseTarget ∈ Set.Icc 0 ((B + 2) ^ C) ∧
        Plate ∈ Set.Icc 0 ((B + 2) ^ C) ∧ ∀ k, Pmaster k ≤ Plate := by
  obtain ⟨Asp, _, hsp⟩ := exists_spatialParameterBudget_bound
  let T : Polynomial ℕ := (Polynomial.X + 2) ^ inputPower
  let Coarse : Polynomial ℕ := Polynomial.C stageCount * (T + 32) + T
  let Narrow : Polynomial ℕ := (T + Coarse + Polynomial.C Asp) ^ Asp
  let Late : Polynomial ℕ := 3 * T + Coarse + Narrow
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget
    (Coarse + Polynomial.C stageCount * Late)
  refine ⟨C, hC, ?_⟩
  intro Stage _ B Pscale extraLate requestedCoarse Pmaster Pphysical detectionGain
    hcard hB hmaster hphysical hgain hscale hextra hrequested coarseTarget Plate
  let t : ℝ := (B + 2) ^ inputPower
  let coarseBound : ℝ := (stageCount : ℝ) * (t + 32) + t
  let narrowBound : ℝ := (t + coarseBound + Asp) ^ Asp
  let lateBound : ℝ := 3 * t + coarseBound + narrowBound
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hcoarseBound : 0 ≤ coarseBound := by dsimp only [coarseBound]; positivity
  have hnarrowBound : 0 ≤ narrowBound := by dsimp only [narrowBound]; positivity
  have hlateBound : 0 ≤ lateBound := by dsimp only [lateBound]; positivity
  have hsumGain : (∑ k, (detectionGain k + 32)) ≤ (stageCount : ℝ) * (t + 32) := by
    calc
      _ ≤ ∑ _k : Stage, (t + 32) :=
        Finset.sum_le_sum (fun k _ => add_le_add (hgain k).2 le_rfl)
      _ = (Fintype.card Stage : ℝ) * (t + 32) := by simp [mul_add]
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) (by positivity)
  have hcoarse : coarseTarget ∈ Set.Icc 0 coarseBound := by
    refine ⟨hrequested.1.trans (le_max_right _ _), ?_⟩
    exact max_le
      (hsumGain.trans (le_add_of_nonneg_right ht))
      (hrequested.2.trans (le_add_of_nonneg_left (by positivity)))
  have hnarrow (k : Stage) :
      2 * (spatialPrimitiveEnvelope (Pphysical k) coarseTarget 0 +
        spatialTupleToleranceLog (spatialPrimitiveEnvelope (Pphysical k) coarseTarget 0)) + 4 ≤
          narrowBound := by
    apply (spatialParameterBudget_bounds (hphysical k).1 hcoarse.1 le_rfl).2.1.trans
    apply (hsp (hphysical k).1 hcoarse.1 le_rfl).trans
    apply pow_le_pow_left₀
      (by linarith only [(hphysical k).1, hcoarse.1, Nat.cast_nonneg (α := ℝ) Asp])
    have hp : Pphysical k ≤ t := (hphysical k).2
    change Pphysical k + coarseTarget + 0 + (Asp : ℝ) ≤ t + coarseBound + Asp
    linarith only [hp, hcoarse.2]
  have hlate (k : Stage) :
      preparedUniformDegreeDirectLate (Pmaster k) Pscale (Pphysical k)
        coarseTarget extraLate ∈ Set.Icc 0 lateBound := by
    refine ⟨(hmaster k).1.trans (le_max_left _ _), ?_⟩
    unfold preparedUniformDegreeDirectLate
    apply max_le _ (max_le _ (max_le _ (max_le _ _))) <;>
      dsimp only [lateBound] <;>
      linarith only [(hmaster k).2, hscale.2, hcoarse.2, hnarrow k, hextra.2,
        ht, hcoarseBound, hnarrowBound]
  have hPlate : Plate ∈ Set.Icc 0 ((stageCount : ℝ) * lateBound) := by
    refine ⟨Finset.sum_nonneg (fun k _ => (hlate k).1), ?_⟩
    calc
      _ ≤ ∑ _k : Stage, lateBound := Finset.sum_le_sum (fun k _ => (hlate k).2)
      _ = (Fintype.card Stage : ℝ) * lateBound := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hlateBound
  have hfinal : coarseBound + (stageCount : ℝ) * lateBound ≤ (B + 2) ^ C := by
    simpa [T, Coarse, Narrow, Late, t, coarseBound, narrowBound, lateBound,
      Polynomial.eval₂_pow] using hbound B hB
  have hsumLateBound : 0 ≤ (stageCount : ℝ) * lateBound :=
    mul_nonneg (Nat.cast_nonneg _) hlateBound
  refine ⟨⟨hcoarse.1, by linarith only [hcoarse.2, hfinal, hsumLateBound]⟩,
    ⟨hPlate.1, by linarith only [hPlate.2, hfinal, hcoarseBound]⟩, ?_⟩
  intro k
  exact (le_max_left _ _).trans
    (Finset.single_le_sum (fun j _ => (hlate j).1) (Finset.mem_univ k))

end Erdos3.VectorPolynomial

end

end OAI

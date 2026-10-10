import OAI.NumberTheory.DukePrimeDegree.Arithmetic.StarkDescent
import OAI.NumberTheory.DukePrimeDegree.Arithmetic.StarkScale
import OAI.NumberTheory.DukePrimeDegree.Arithmetic.StarkZeros

namespace OAI

/-!
# Assembling the normal-closure argument

Realizing cyclic Frobenius characters by even ray characters gives
zero propagation to the normal closure. Simplicity near one and
odd-index descent then exclude an exceptional real zero.
-/

noncomputable section
open Module Set IntermediateField
open scoped NumberField Classical

namespace DukePrimeDegree
open PrimeDegreePackets PrimeDegreePackets.HeckeMellin PrimeDegreePackets.AnalyticGrowth

universe u

lemma fixedFieldMultiplicity_fixingSubgroup
    {K E : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    [Field E] [NumberField E] [NumberField.IsTotallyReal E] [IsGalois ℚ E]
    (f : K →ₐ[ℚ] E) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    fixedFieldMultiplicity β f.fieldRange.fixingSubgroup = zetaMultiplicity K β := by
  let L := f.fieldRange
  let e : IntermediateField.fixedField L.fixingSubgroup ≃ₐ[ℚ] L :=
    IntermediateField.equivOfEq (IsGalois.fixedField_fixingSubgroup L)
  exact (zetaMultiplicity_algEquiv e hβ0 hβ1).trans
    (zetaMultiplicity_algEquiv f.equivFieldRange hβ0 hβ1).symm

lemma fixingSubgroup_index_of_embedding
    {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E]
    [IsGalois ℚ E] (f : K →ₐ[ℚ] E) :
    f.fieldRange.fixingSubgroup.index = finrank ℚ K := by
  rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
  exact f.equivFieldRange.toLinearEquiv.finrank_eq.symm

/-- The zero-exclusion consequence of cyclic reciprocity, for the exact
family of normal closures required by the application. -/
theorem exceptionalRealZeroExclusion_of_ray_realizations
    (d : ℕ) (hodd : Odd (d + 1))
    (hray : ∀ (E : Type u) [Field E] [NumberField E] [IsGalois ℚ E]
      [NumberField.IsTotallyReal E], HasCyclicRayRealizations E) :
    ExceptionalRealZeroExclusion.{u} d := by
  obtain ⟨a, T, ha, ha1, hT, hsimple⟩ := normalClosure_simple_zero_scaled d
  obtain ⟨b, hb, hQ⟩ := rational_zetaMultiplicity_zero_scaled
  refine ⟨min a b, T, lt_min ha hb, hT, ?_⟩
  intro K _ _ _ hn σ hL β hβ hβ1 hzero
  have hLp : 0 < Real.log |(NumberField.discr K : ℝ)| := lt_of_lt_of_le (by linarith) hL
  have hfrac : min a b / Real.log |(NumberField.discr K : ℝ)| ≤ 1 / 4 := by
    have ha' : min a b ≤ 1 := (min_le_left _ _).trans ha1
    apply (div_le_iff₀ hLp).mpr
    have hL4 := hT.trans hL
    nlinarith
  have hβ0 : 0 < β := by linarith
  let E := normalClosure ℚ K (AlgebraicClosure K)
  let : Algebra.IsAlgebraic ℚ (AlgebraicClosure K) := Algebra.IsAlgebraic.trans ℚ K _
  let : IsAlgClosure ℚ (AlgebraicClosure K) := ⟨inferInstance, inferInstance⟩
  let : Nonempty (K →ₐ[ℚ] AlgebraicClosure K) := ⟨IsScalarTower.toAlgHom ℚ K _⟩
  let : IsNormalClosure ℚ K E := isNormalClosure_normalClosure ℚ K (AlgebraicClosure K)
  let : Normal ℚ E := IsNormalClosure.normal (K := K)
  let : IsGalois ℚ E := {}
  let : NumberField E := {}
  let : NumberField.IsTotallyReal E := normalClosure_isTotallyReal
  obtain ⟨f⟩ := IntermediateField.nonempty_algHom_of_splits
    (fun x : K => ⟨Algebra.IsIntegral.isIntegral x,
      IsNormalClosure.splits (F := ℚ) (K := K) (L := E) x⟩)
  let H := f.fieldRange.fixingSubgroup
  have hHodd : Odd H.index := by
    rw [fixingSubgroup_index_of_embedding f, hn]
    exact hodd
  have hKpos : 0 < zetaMultiplicity K β := by
    rw [zetaMultiplicity_eq_zeroMultiplicity σ hn hβ0 hβ1]
    exact lt_of_le_of_ne (zeroMultiplicity_nonneg (completedThetaXi_entire σ hn) _)
      (Ne.symm ((zeroMultiplicity_ne_zero_iff (completedThetaXi_entire σ hn)
        (dedekindXiZeros_ne_zero_totallyReal σ hn) (β : ℂ)).mpr hzero))
  have hHpos : 0 < fixedFieldMultiplicity β H := by
    rw [fixedFieldMultiplicity_fixingSubgroup f hβ0 hβ1]
    exact hKpos
  have hEpos := extension_multiplicity_pos_of_ray_realizations (hray E) hβ0 hβ1 H hHpos
  have hβa : 1 - a / Real.log |(NumberField.discr K : ℝ)| ≤ β := by
    have hh := div_le_div_of_nonneg_right (min_le_left a b) hLp.le
    linarith
  have hEone := hsimple σ hn hL β hβ0 hβ1 hβa (ne_of_gt hEpos)
  have hβb : 1 - b / Real.log |(NumberField.discr K : ℝ)| ≤ β := by
    have hh := div_le_div_of_nonneg_right (min_le_right a b) hLp.le
    linarith
  exact no_odd_index_zero_of_ray_realizations (hray E) hβ0 hβ1 hEone H hHodd hHpos
    (hQ _ (hT.trans hL) β ⟨hβb, hβ1.le⟩ hβ0 hβ1)

end DukePrimeDegree

end

end OAI

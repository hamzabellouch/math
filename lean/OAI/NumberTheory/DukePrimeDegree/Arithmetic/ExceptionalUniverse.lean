import OAI.NumberTheory.DukePrimeDegree.Arithmetic.StarkNormalClosure

namespace OAI

/-!
# Transporting exceptional-zero exclusion between universes

Every ordered totally real number field embeds in the real numbers.
Its image is a small isomorphic number field with the same discriminant
and continued zeta zero orders. Thus a Type-level class-field theorem
suffices for the universe-polymorphic main statement.
-/

noncomputable section
open Module Set
open scoped NumberField Classical

namespace DukePrimeDegree
open PrimeDegreePackets PrimeDegreePackets.HeckeMellin PrimeDegreePackets.AnalyticGrowth

universe u

theorem exceptionalRealZeroExclusion_lift (d : ℕ)
    (H : ExceptionalRealZeroExclusion.{0} d) : ExceptionalRealZeroExclusion.{u} d := by
  obtain ⟨a, T, ha, hT, hzero⟩ := H
  refine ⟨min a 1, T, lt_min ha zero_lt_one, hT, ?_⟩
  intro K _ _ _ hn σ hL β hβ hβ1 hKzero
  have hLp : 0 < Real.log |(NumberField.discr K : ℝ)| := lt_of_lt_of_le (by linarith) hL
  have hfrac : min a 1 / Real.log |(NumberField.discr K : ℝ)| ≤ 1 / 4 := by
    apply (div_le_iff₀ hLp).mpr
    have := min_le_right a (1 : ℝ)
    have := hT.trans hL
    nlinarith
  have hβ0 : 0 < β := by linarith
  let f : K →ₐ[ℚ] ℝ := { __ := σ 0, commutes' := fun q => by simp }
  let L := f.fieldRange
  let e : K ≃ₐ[ℚ] L := f.equivFieldRange
  let : FiniteDimensional ℚ L := e.toLinearEquiv.finiteDimensional
  let : NumberField L := {}
  let : NumberField.IsTotallyReal L := NumberField.IsTotallyReal.ofRingEquiv e.toRingEquiv
  have hnL : finrank ℚ L = d + 1 := e.toLinearEquiv.finrank_eq.symm.trans hn
  have hdim : degreePred L + 1 = d + 1 := (degreePred_spec L).symm.trans hnL
  let τ : OrderedEmbeddings (d + 1) L := hdim ▸ canonicalRealEmbeddings L
  have hdisc : NumberField.discr K = NumberField.discr L :=
    NumberField.discr_eq_discr_of_algEquiv K e
  have hβa : 1 - a / Real.log |(NumberField.discr L : ℝ)| ≤ β := by
    rw [← hdisc]
    have := div_le_div_of_nonneg_right (min_le_left a 1) hLp.le
    linarith
  have hzL := hzero L hnL τ (by rwa [← hdisc]) β hβa hβ1
  have hmL := zetaMultiplicity_eq_zero_of_completed_ne_zero τ hnL hβ0 hβ1 hzL
  have hmK : zetaMultiplicity K β ≠ 0 := by
    rw [zetaMultiplicity_eq_zeroMultiplicity σ hn hβ0 hβ1]
    exact (zeroMultiplicity_ne_zero_iff (completedThetaXi_entire σ hn)
      (dedekindXiZeros_ne_zero_totallyReal σ hn) (β : ℂ)).mpr hKzero
  exact hmK ((zetaMultiplicity_algEquiv e hβ0 hβ1).trans hmL)

end DukePrimeDegree

end

end OAI

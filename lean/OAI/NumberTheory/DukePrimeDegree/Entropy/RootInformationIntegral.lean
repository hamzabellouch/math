import OAI.NumberTheory.DukePrimeDegree.Geometry.CanonicalRootBasic

namespace OAI

/-!
# Signed mean information at every real time

Finite coefficients imply integrability. The actual leaf cocycle extends
the mean identity to negative times as well as positive times.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
  (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
  (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)

include hA

lemma integrable_rootInformation_nonneg {t : ℝ} (ht : 0 ≤ t) :
    Integrable (rootInformation hij μ t) μ := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (aemeasurable_rootInformation d hij μ hA t).aestronglyMeasurable
    (ae_rootInformation_nonneg d hij μ hA ht)).mp
  change rootInformationMean hij μ t ≠ ∞
  rw [rootInformationMean_eq_coefficient d μ hA i j hij ht]
  exact ENNReal.ofReal_ne_top

lemma integral_rootInformation_nonneg {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, rootInformation hij μ t x ∂μ) = t * canonicalRootCoefficient d μ i j := by
  have he := ofReal_integral_eq_lintegral_ofReal
    (integrable_rootInformation_nonneg d hij μ hA ht)
    (ae_rootInformation_nonneg d hij μ hA ht)
  change ENNReal.ofReal (∫ x, rootInformation hij μ t x ∂μ) = rootInformationMean hij μ t at he
  rw [rootInformationMean_eq_coefficient d μ hA i j hij ht] at he
  have hi := integral_nonneg_of_ae (ae_rootInformation_nonneg d hij μ hA ht)
  have hh := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal hi,
    ENNReal.toReal_ofReal (mul_nonneg ht (canonicalRootCoefficient_nonneg d μ i j))] using hh

lemma ae_rootInformation_time_reversal (t : ℝ) :
    ∀ᵐ x ∂μ, rootInformation hij μ t x =
      -rootInformation hij μ (-t) (rightAction x (rootCanonicalFlow d j t)) := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  filter_upwards [ae_rootInformation_cocycle d hij μ hA (-t) t,
    ae_intrinsicRootLeaf_spec hij μ hfree] with x hc hs
  have hz : rootInformation hij μ 0 x = 0 := by simp [rootInformation, hs.2]
  rw [neg_add_cancel, hz] at hc
  linarith

/-- Root information is integrable even for negative times. -/
theorem integrable_rootInformation (t : ℝ) : Integrable (rootInformation hij μ t) μ := by
  by_cases ht : 0 ≤ t
  · exact integrable_rootInformation_nonneg d hij μ hA ht
  have hm := integrable_rootInformation_nonneg d hij μ hA (neg_nonneg.mpr (le_of_not_ge ht))
  have hT := rootCanonicalFlow_preserving d j t μ hA
  apply (hT.integrable_comp_of_integrable hm).neg.congr
  filter_upwards [ae_rootInformation_time_reversal d hij μ hA t] with x hx
  exact hx.symm

/-- The signed integral is exactly linear at every real time. -/
theorem integral_rootInformation (t : ℝ) :
    (∫ x, rootInformation hij μ t x ∂μ) = t * canonicalRootCoefficient d μ i j := by
  by_cases ht : 0 ≤ t
  · exact integral_rootInformation_nonneg d hij μ hA ht
  have hT := rootCanonicalFlow_preserving d j t μ hA
  rw [integral_congr_ae (ae_rootInformation_time_reversal d hij μ hA t), integral_neg]
  have hmap : (∫ x, rootInformation hij μ (-t)
      (rightAction x (rootCanonicalFlow d j t)) ∂μ) =
      ∫ x, rootInformation hij μ (-t) x ∂μ := by
    have hf : AEStronglyMeasurable (rootInformation hij μ (-t))
        (μ.map (fun x => rightAction x (rootCanonicalFlow d j t))) := by
      rw [hT.map_eq]
      exact (aemeasurable_rootInformation d hij μ hA (-t)).aestronglyMeasurable
    exact (integral_map hT.measurable.aemeasurable hf).symm.trans (by rw [hT.map_eq])
  rw [hmap, integral_rootInformation_nonneg d hij μ hA (by linarith)]
  ring

end DukePrimeDegree

end

end OAI

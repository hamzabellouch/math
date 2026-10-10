import OAI.Analysis.CircleDomains.Rigidity.ConductivityContraction

namespace OAI

/-! Convert the actual conjugate Beltrami equation to a bounded standard
coefficient after constructing its L2 solution. No nonvanishing assumption
on the complex derivative is needed for this algebraic reduction. -/
open MeasureTheory Filter Set
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

 def realBeltramiStandardCoefficient (q : ℝ) (a : ℂ) : ℂ := (q : ℂ) * star a / a

lemma realBeltramiStandardCoefficient_norm_le (q : ℝ) (a : ℂ) :
    ‖realBeltramiStandardCoefficient q a‖ ≤ ‖q‖ := by
  by_cases ha : a = 0
  · simp [realBeltramiStandardCoefficient, ha]
  · simp [realBeltramiStandardCoefficient, norm_ne_zero_iff.mpr ha]

lemma realBeltramiStandardCoefficient_mul (q : ℝ) (a : ℂ) :
    realBeltramiStandardCoefficient q a * a = (q : ℂ) * star a := by
  by_cases ha : a = 0
  · simp [realBeltramiStandardCoefficient, ha]
  · exact div_mul_cancel₀ _ ha

lemma realBeltramiStandardCoefficient_aeStronglyMeasurable
    (q : EuclideanPlane → ℝ) (a : EuclideanPlane → ℂ)
    (hq : AEStronglyMeasurable q volume) (ha : AEStronglyMeasurable a volume) :
    AEStronglyMeasurable (fun z => realBeltramiStandardCoefficient (q z) (a z)) volume := by
  exact ((Complex.continuous_ofReal.comp_aestronglyMeasurable hq).mul ha.star).div₀ ha

lemma realBeltramiStandardCoefficient_zero (a : ℂ) :
    realBeltramiStandardCoefficient 0 a = 0 := by
  simp [realBeltramiStandardCoefficient]

lemma exists_compact_coefficient_representative (μ : EuclideanPlane → ℂ)
    (hm : AEStronglyMeasurable μ volume) {K : Set EuclideanPlane}
    (hK : IsCompact K) (hzero : ∀ x ∉ K, μ x = 0)
    (k : ℝ≥0) (hb : ∀ᵐ x ∂volume, ‖μ x‖ ≤ k) :
    ∃ ν : EuclideanPlane → ℂ, Measurable ν ∧ (∀ x, ‖ν x‖ ≤ k) ∧
      (∀ x ∉ K, ν x = 0) ∧ μ =ᵐ[volume] ν := by
  classical
  let ν : EuclideanPlane → ℂ := fun x =>
    if x ∈ K ∧ ‖hm.mk μ x‖ ≤ k then hm.mk μ x else 0
  have hm' : Measurable (hm.mk μ) := hm.measurable_mk
  refine ⟨ν, Measurable.ite (hK.measurableSet.inter (measurableSet_le hm'.norm measurable_const))
    hm' measurable_const, ?_, ?_, ?_⟩
  · intro x
    dsimp only [ν]
    split_ifs with hx
    · exact hx.2
    · exact_mod_cast k.2
  · intro x hx
    exact ite_eq_right (fun h => hx h.1)
  · filter_upwards [hm.ae_eq_mk, hb] with x hx hb'
    by_cases hxK : x ∈ K
    · dsimp only [ν]
      rw [← hx, ite_eq_left ⟨hxK, hb'⟩]
    · dsimp only [ν]
      rw [ite_eq_right (fun h => hxK h.1)]
      exact hzero x hxK

end CircleDomainRigidity

end

end OAI

import OAI.Probability.SLE.Loewner.InitialChartIdentities
import OAI.Probability.SLE.Loewner.RadiusHullInverse

namespace OAI

/-! Normalization and height of the initial chart family, including its
identity chart at time zero. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

lemma initialForwardChart_differentiableOn_current (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (s : unitInterval) :
    DifferentiableOn ℂ (initialForwardChart p hi h0 hH s)
      (upperHalfPlane \ range (initialSubarc p s)) := by
  by_cases hs : s=0
  · simp only [hs,initialForwardChart_zero]
    exact differentiableOn_id
  · simpa only [initialForwardChart,dite_eq_right hs] using
      (initialSlitChart p hi h0 hH s hs).forward_differentiable

lemma initialForwardChart_coefficient (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (s : unitInterval) :
    Tendsto (fun z : ℂ => z*(initialForwardChart p hi h0 hH s z-z)) (cocompact ℂ)
      (𝓝 (initialCapacity p hi h0 hH s:ℂ)) := by
  by_cases hs : s=0
  · simp only [hs,initialForwardChart_zero,id_eq,sub_self,mul_zero,initialCapacity_zero,ofReal_zero]
    exact tendsto_const_nhds
  · simpa only [initialForwardChart,initialCapacity,dite_eq_right hs] using
      (initialSlitChart p hi h0 hH s hs).coefficient

lemma initialInverseChart_normalized (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (s : unitInterval) :
    Tendsto (fun z : ℂ => initialInverseChart p hi h0 hH s z/z)
      (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 1) := by
  by_cases hs : s=0
  · apply ratio_one_of_bounded_displacement (R := 0)
    intro z _
    simp only [hs,initialInverseChart_zero,id_eq,sub_self,norm_zero,le_refl]
  · simpa only [initialInverseChart,dite_eq_right hs] using
      (initialSlitChart p hi h0 hH s hs).inverse_normalized

lemma initialForwardChart_height_le (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (s : unitInterval) {z : ℂ} (hz : z∈upperHalfPlane \ range (initialSubarc p s)) :
    (initialForwardChart p hi h0 hH s z).im≤z.im := by
  by_cases hs : s=0
  · simp only [hs,initialForwardChart_zero,id_eq,le_refl]
  · simpa only [initialForwardChart,dite_eq_right hs] using
      (initialSlitChart p hi h0 hH s hs).height_le z hz

end SLEExactGauge

end

end OAI

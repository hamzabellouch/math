import OAI.Probability.ContinuumTransition.UniformMin

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

def moderateBox : Set Parameter := {x | 1/4 ≤ x.1 ∧ x.1 ≤ 2 ∧ x.2 ≤ 10}

lemma initial_ball_moderate : closedBall initialPoint (1/2) ⊆ moderateBox := by
  intro x hx
  have hh : |x.1-1| ≤ 1/2 ∧ |x.2-(-3/4)| ≤ 1/2 := by
    simpa only [mem_closedBall,dist_eq_norm_sub,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,
      Real.norm_eq_abs,max_le_iff,initialPoint] using hx
  obtain ⟨h1,h2⟩ := hh
  obtain ⟨h1,h1'⟩ := abs_le.mp h1
  obtain ⟨h2,h2'⟩ := abs_le.mp h2
  exact ⟨by linarith,by linarith,by linarith⟩

lemma moderateBox_subset : moderateBox ⊆ pressureDomain := by
  intro x hx
  change 0 < x.1
  linarith only [hx.1]

lemma physicalProfile_zero (t : ℝ) (R : ℕ → ℝ) :
    physicalProfile t (fun _ => 0) R = coreProfile t := by
  funext r
  simp [physicalProfile,attraction]

lemma physical_convex_bounded {t : ℝ} (ht : 1 < t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hm : 17576*kernelHeight*(∑' n, σ n) ≤ t) :
    ConvexOn ℝ pressureDomain (physicalPressure (physicalProfile t σ R) t) := by
  have ht0 := lt_trans zero_lt_one ht
  exact convexOn_physicalPressure (measurable_radialPotential (measurable_physicalProfile t hσ hR hs)) ht
    (physicalProfile_stable ht0.le hσ hR hs (strengthened_smallness ht0 hm).1)
    (fun r _ => physicalProfile_le_core ht0.le hσ hR r)

lemma physical_meanField_bounded {t a : ℝ} (ht : 1 < t) (ha : 0 < a) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hm : 17576*kernelHeight*(∑' n, σ n) ≤ t) (hat : 1024*a < t) :
    IsMeanField (physicalPressure (physicalProfile t σ R) t) a
      (meanField (physicalPressure (physicalProfile t σ R) t) a) ∧
    (∀ x ∈ pressureDomain, ∃ d, quadraticCost (physicalPressure (physicalProfile t σ R) t) a x d =
      meanField (physicalPressure (physicalProfile t σ R) t) a x) := by
  have ht0 := lt_trans zero_lt_one ht
  have hsmall := (strengthened_smallness ht0 hm).1
  have hgap := strengthened_gap ht0 hm hat
  exact ⟨isMeanField_meanField (physical_meanField ht ha.le hσ hR hs hsmall hgap.le),
    fun _ hx => physical_meanField_attained ht ha hσ hR hs hsmall hgap hx⟩

lemma physical_meanField_bounded_attainment {t a : ℝ} (ht : 1 < t) (ha : 0 < a) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hm : 17576*kernelHeight*(∑' n, σ n) ≤ t) (hat : 1024*a < t)
    {x : Parameter} (hx : x ∈ moderateBox) :
    ∃ d ∈ Icc (0:ℝ) 1048576, quadraticCost (physicalPressure (physicalProfile t σ R) t) a x d =
      meanField (physicalPressure (physicalProfile t σ R) t) a x := by
  have hh := physical_meanField_bounded ht ha hσ hR hs hm hat
  obtain ⟨w,hw⟩ := activeLifts_nonempty ha (physical_convex_bounded ht hσ hR hs hm) hh.1
    (moderateBox_subset hx) (hh.2 _ (moderateBox_subset hx))
  exact ⟨w.2,physical_transform_active_bound ht ha hσ hR hs hm hat hx.1 hx.2.1 hx.2.2 hw,hw.1⟩

lemma strong_smallness {t m : ℝ} (ht : 0 < t)
    (hm : 140608*kernelHeight*m ≤ t) : 2197*t*kernelHeight*m ≤ (t^2/8)/8 := by
  have h := mul_le_mul_of_nonneg_left hm ht.le
  nlinarith only [h]

end ContinuumTemperature
end
end

end OAI

import OAI.Probability.SLE.Loewner.SlitRealBoundaryFlow
import OAI.Probability.SLE.Loewner.SlitPhysicalEvolution

namespace OAI

/-! On surviving interior points the reflected coordinates obey the
exact physical-time Loewner equation and its integral identity. -/
noncomputable section
open Set Filter Function Complex MeasureTheory
open scoped Topology NNReal

namespace SLEExactGauge

lemma slitReflectedFlow_eq_forward (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) {z : ℂ} (hz : z∈upperHalfPlane \ range p) (t : ℝ) :
    slitReflectedFlow p hi h0 hH T z t=slitCapacityForward p hi h0 hH T t.toNNReal z :=
  initialReflectedForward_eq p hi h0 hH _
    ⟨hz.1,fun he => hz.2 (initialSubarc_range_subset p _ he)⟩

lemma slitReflectedFlow_interior_continuous (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) {z : ℂ} (hz : z∈upperHalfPlane \ range p) :
    Continuous (slitReflectedFlow p hi h0 hH T z) := by
  have hzD (s : unitInterval) : z∈upperHalfPlane \ range (initialSubarc p s) :=
    ⟨hz.1,fun he => hz.2 (initialSubarc_range_subset p s he)⟩
  have hc : Continuous (fun s => initialForwardChart p hi h0 hH s z) := by
    apply SeqContinuous.continuous
    intro s t hs
    exact initialForwardChart_tendsto p hi h0 hH hs tendsto_const_nhds (hzD t) (fun n => hzD (s n))
  have he : slitReflectedFlow p hi h0 hH T z=
      fun t => initialForwardChart p hi h0 hH (slitCapacityTime p hi h0 hH T t.toNNReal) z :=
    funext (slitReflectedFlow_eq_forward p hi h0 hH T hz)
  rw [he]
  exact hc.comp ((slitCapacityTime_continuous p hi h0 hH T).comp continuous_real_toNNReal)

lemma slitReflectedFlow_interior_separated (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) {z : ℂ} (hz : z∈upperHalfPlane \ range p) (t : ℝ) :
    slitReflectedFlow p hi h0 hH T z t-(slitCapacityDriver p hi h0 hH hT t.toNNReal:ℂ)≠0 := by
  have hp := initialForwardChart_mem_upper p hi h0 hH (slitCapacityTime p hi h0 hH T t.toNNReal)
    ⟨hz.1,fun he => hz.2 (initialSubarc_range_subset p _ he)⟩
  rw [slitReflectedFlow_eq_forward p hi h0 hH T hz]
  intro he
  have hh := congrArg Complex.im he
  simp only [sub_im,ofReal_im,sub_zero,zero_im] at hh
  exact (show 0<(slitCapacityForward p hi h0 hH T t.toNNReal z).im from hp).ne' hh

lemma slitReflectedFlow_interior_kernel_continuous (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) {z : ℂ} (hz : z∈upperHalfPlane \ range p) :
    Continuous (fun t : ℝ => 2/(slitReflectedFlow p hi h0 hH T z t-
      (slitCapacityDriver p hi h0 hH hT t.toNNReal:ℂ))) :=
  continuous_const.div ((slitReflectedFlow_interior_continuous p hi h0 hH T hz).sub
    (Complex.continuous_ofReal.comp
      ((slitCapacityDriver p hi h0 hH hT).continuous.comp continuous_real_toNNReal)))
    (slitReflectedFlow_interior_separated p hi h0 hH hT hz)

theorem slitReflectedFlow_interior_derivative (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) {z : ℂ} (hz : z∈upperHalfPlane \ range p)
    {t : ℝ} (ht : t∈Icc 0 (slitCapacityHorizon p hi h0 hH T:ℝ)) :
    HasDerivWithinAt (slitReflectedFlow p hi h0 hH T z)
      (2/(slitReflectedFlow p hi h0 hH T z t-
        (slitCapacityDriver p hi h0 hH hT t.toNNReal:ℂ)))
      (Icc 0 (slitCapacityHorizon p hi h0 hH T:ℝ)) t := by
  have hu : t.toNNReal ≤ slitCapacityHorizon p hi h0 hH T := Real.toNNReal_le_iff_le_coe.mpr ht.2
  have hh := slitCapacityForward_prefix_derivative p hi h0 hH hT
    ⟨hz.1,fun he => hz.2 (initialSubarc_range_subset p T he)⟩ hu
  rw [Real.coe_toNNReal t ht.1] at hh
  have he : slitReflectedFlow p hi h0 hH T z=
      fun u => slitCapacityForward p hi h0 hH T u.toNNReal z :=
    funext (slitReflectedFlow_eq_forward p hi h0 hH T hz)
  simpa only [he] using hh

theorem slitReflectedFlow_interior_integral (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) {z : ℂ} (hz : z∈upperHalfPlane \ range p)
    {t : ℝ} (ht : t∈Icc 0 (slitCapacityHorizon p hi h0 hH T:ℝ)) :
    (∫ u in 0..t, 2/(slitReflectedFlow p hi h0 hH T z u-
      (slitCapacityDriver p hi h0 hH hT u.toNNReal:ℂ)))=
      slitReflectedFlow p hi h0 hH T z t-z := by
  have hz0 : slitReflectedFlow p hi h0 hH T z 0=z := by
    rw [slitReflectedFlow_eq_forward p hi h0 hH T hz]
    simp only [slitCapacityForward,Real.toNNReal_zero,slitCapacityTime_zero,initialForwardChart_zero,id_eq]
  have hi' : (∫ u in 0..t, 2/(slitReflectedFlow p hi h0 hH T z u-
      (slitCapacityDriver p hi h0 hH hT u.toNNReal:ℂ)))=
      slitReflectedFlow p hi h0 hH T z t-slitReflectedFlow p hi h0 hH T z 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
      (slitReflectedFlow_interior_continuous p hi h0 hH T hz).continuousOn
    · intro u hu
      exact (slitReflectedFlow_interior_derivative p hi h0 hH hT hz
        ⟨hu.1.le,hu.2.le.trans ht.2⟩).hasDerivAt
        (Icc_mem_nhds hu.1 (hu.2.trans_le ht.2))
    · exact (slitReflectedFlow_interior_kernel_continuous p hi h0 hH hT hz).intervalIntegrable 0 t
  simpa only [hz0] using hi'

end SLEExactGauge

end

end OAI

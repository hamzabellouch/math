import OAI.Probability.SLE.Loewner.SlitPhysicalClock
import OAI.Probability.SLE.Geometry.FiniteSimpleSlit

namespace OAI

/-! The capacity-two curve has exactly the prescribed initial ranges
and no additional swallowed points. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology NNReal

namespace SLEExactGauge

noncomputable def slitCapacityCurve (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) (t : ℝ≥0) : ℂ := p (slitCapacityTime p hi h0 hH T t)

lemma slitCapacityCurve_continuous (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) : Continuous (slitCapacityCurve p hi h0 hH T) :=
  p.continuous.comp (slitCapacityTime_continuous p hi h0 hH T)

@[simp] lemma slitCapacityCurve_zero (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) : slitCapacityCurve p hi h0 hH T 0=0 := by
  simp only [slitCapacityCurve,slitCapacityTime_zero,h0]

lemma slitCapacityCurve_initial_range (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) {t : ℝ≥0} (ht : t ≤ slitCapacityHorizon p hi h0 hH T) :
    slitCapacityCurve p hi h0 hH T '' Icc 0 t=
      range (initialSubarc p (slitCapacityTime p hi h0 hH T t)) := by
  rw [initialSubarc_range]
  change (p ∘ slitCapacityTime p hi h0 hH T) '' Icc 0 t=p '' _
  rw [image_comp,slitCapacityTime_image p hi h0 hH T ht]

lemma slitCapacityCurve_injOn (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) :
    InjOn (slitCapacityCurve p hi h0 hH T) (Icc 0 (slitCapacityHorizon p hi h0 hH T)) := by
  intro s hs t ht he
  have hc := congrArg (initialCapacity p hi h0 hH) (hi he)
  rw [slitCapacityTime_capacity p hi h0 hH T hs.2,
    slitCapacityTime_capacity p hi h0 hH T ht.2] at hc
  apply NNReal.coe_injective
  linarith

lemma slitCapacityCurve_positive (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) {t : ℝ≥0} (ht : t∈Ioc 0 (slitCapacityHorizon p hi h0 hH T)) :
    slitCapacityCurve p hi h0 hH T t∈upperHalfPlane := by
  apply hH
  intro he
  have hh := slitCapacityTime_capacity p hi h0 hH T ht.2
  rw [he,initialCapacity_zero] at hh
  have hp : (0:ℝ)<t := ht.1
  linarith

theorem slitCapacityCurve_free_complement (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (T : unitInterval) {t : ℝ≥0} (ht : t ≤ slitCapacityHorizon p hi h0 hH T)
    (ht0 : 0<t) :
    upperHalfPlane \ (slitCapacityCurve p hi h0 hH T '' Icc 0 t) ⊆
      survivingDomain (slitCapacityCurve p hi h0 hH T) t :=
  finite_simple_slit_free _ (slitCapacityCurve_continuous p hi h0 hH T)
    (slitCapacityCurve_zero p hi h0 hH T) t ht0
    ((slitCapacityCurve_injOn p hi h0 hH T).mono (Icc_subset_Icc_right ht))
    (fun _u hu => slitCapacityCurve_positive p hi h0 hH T ⟨hu.1,hu.2.trans ht⟩)

end SLEExactGauge

end

end OAI

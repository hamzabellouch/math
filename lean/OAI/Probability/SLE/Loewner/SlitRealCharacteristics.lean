import OAI.Probability.SLE.Loewner.SlitBoundaryIntegralLimit
import OAI.Probability.SLE.Geometry.RegularSlitTube

namespace OAI

/-! The exact driver of a prescribed simple slit has noncolliding real
Loewner characteristics throughout every finite capacity prefix. -/
noncomputable section
open Set Filter Function Complex _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped Topology NNReal

namespace SLEExactGauge

theorem slit_regularRealCharacteristics (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) :
    RegularRealCharacteristics (slitCapacityDriver p hi h0 hH hT)
      (slitCapacityHorizon p hi h0 hH T) := by
  intro x hx
  let X := slitReflectedFlow p hi h0 hH T (x:ℂ)
  let q := fun t : ℝ => (X t).re
  let b := slitCapacityDriver p hi h0 hH hT
  let A := slitCapacityHorizon p hi h0 hH T
  have hX (t : ℝ) : X t=(q t:ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [ofReal_im] using slitReflectedFlow_real p hi h0 hH T hx t
  have hX0 : X 0=(x:ℂ) := by
    dsimp [X,slitReflectedFlow]
    simp [slitCapacityTime_zero,initialReflectedForward]
  have hqgap (t : ℝ) : q t-b t.toNNReal≠0 := by
    intro he
    have hh := slitReflectedFlow_separated p hi h0 hH hT hx t
    change X t-(b t.toNNReal:ℂ)≠0 at hh
    rw [hX] at hh
    apply hh
    exact_mod_cast he
  refine ⟨q,?_,?_,fun t _ => hqgap t⟩
  · change (X 0).re=x
    rw [hX0,ofReal_re]
  · intro t ht
    let k := fun u : ℝ => 2/(X u-(b u.toNNReal:ℂ))
    have hk : Continuous k := slitReflectedFlow_real_kernel_continuous p hi h0 hH hT hx
    have hI : HasDerivAt (fun u => (x:ℂ)+∫ v in 0..u, k v) (k t) t := by
      simpa only [zero_add] using (intervalIntegral.integral_hasDerivAt_right
        (hk.intervalIntegrable 0 t) hk.aestronglyMeasurable.stronglyMeasurableAtFilter
        hk.continuousAt).const_add (x:ℂ)
    have hXd : HasDerivWithinAt X (k t) (Icc 0 (A:ℝ)) t := by
      apply hI.hasDerivWithinAt.congr_of_mem (fun u hu => ?_) ht
      rw [slitReflectedFlow_boundary_integral p hi h0 hH hT hx hu]
      dsimp only [X]
      abel
    have hqd := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t hXd
    change HasDerivWithinAt q (k t).re (Icc 0 (A:ℝ)) t at hqd
    have he : (k t).re=2/(q t-b t.toNNReal) := by
      dsimp only [k]
      rw [hX]
      norm_cast
    rwa [he] at hqd

end SLEExactGauge

end

end OAI

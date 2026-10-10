import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.BoundedSpatialJetIntegral
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Model
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

/-! Lift the pointwise scalar equation to the finite spatial-jet Banach space by FTC. -/

noncomputable section
namespace ForcedComputation.BoundedSpatialJets
open ShearFlows Set MeasureTheory
open scoped Topology Interval

variable (k : ℕ)

theorem integral_eq_sub_of_pointwise_derivative {T : ℝ}
    (u r : ℝ → Space Plane ℝ k) (hu : Continuous u) (hr : Continuous r)
    (hd : ∀ s ∈ Ioo (0 : ℝ) T, ∀ x : Plane,
      HasDerivAt (fun t => function Plane ℝ k (u t) x) (function Plane ℝ k (r s) x) s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (∫ s in 0..t, r s) = u t - u 0 := by
  apply function_injective Plane ℝ k
  apply BoundedContinuousFunction.ext
  intro x
  let L : Space Plane ℝ k →L[ℝ] ℝ :=
    (BoundedContinuousFunction.evalCLM ℝ x).comp (functionMap Plane ℝ k)
  change L (∫ s in 0..t, r s) = L (u t-u 0)
  rw [← L.intervalIntegral_comp_comm (hr.intervalIntegrable 0 t)]
  have hc : Continuous (fun s => L (u s)) := L.continuous.comp hu
  have hr' : Continuous (fun s => L (r s)) := L.continuous.comp hr
  have hd' (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) t) :
      HasDerivAt (fun v => L (u v)) (L (r s)) s :=
    hd s ⟨hs.1, hs.2.trans_le ht.2⟩ x
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    hc.continuousOn hd'
    (hr'.intervalIntegrable 0 t)
  simpa only [map_sub] using he

theorem hasDerivWithinAt_of_pointwise_derivative {T : ℝ}
    (u r : ℝ → Space Plane ℝ k) (hu : Continuous u) (hr : Continuous r)
    (hd : ∀ s ∈ Ioo (0 : ℝ) T, ∀ x : Plane,
      HasDerivAt (fun t => function Plane ℝ k (u t) x) (function Plane ℝ k (r s) x) s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt u (r t) (Icc (0 : ℝ) T) t := by
  let : SecondCountableTopologyEither ℝ (Space Plane ℝ k) :=
    secondCountableTopologyEither_of_left _ _
  have he (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) : u s = u 0 + ∫ v in 0..s, r v := by
    rw [integral_eq_sub_of_pointwise_derivative k u r hu hr hd hs]
    abel
  have hi := (intervalIntegral.integral_hasDerivAt_right (hr.intervalIntegrable 0 t)
    hr.aestronglyMeasurable.stronglyMeasurableAtFilter hr.continuousAt).const_add (u 0)
  exact hi.hasDerivWithinAt.congr he (he t ht)

end ForcedComputation.BoundedSpatialJets

end

end OAI

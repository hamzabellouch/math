import OAI.MathematicalPhysics.Boltzmann.Branching.PublishedInputs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace OAI

/-! # The causal resolvent is a finite characteristic integral -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.TransportPrimitive

theorem causal_convolution {r : ℝ → ℝ} (hr : ∀ s < 0, r s = 0) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in Ici (0:ℝ), Real.exp (-s)*r (t-s)) =
      ∫ s in 0..t, Real.exp (-(t-s))*r s := by
  have he : (∫ s in Ici (0:ℝ), Real.exp (-s)*r (t-s)) =
      ∫ s in Ici (0:ℝ), (Icc 0 t).indicator (fun s => Real.exp (-s)*r (t-s)) s := by
    apply setIntegral_congr_fun measurableSet_Ici
    intro s hs
    by_cases hst : s ≤ t
    · rw [indicator_of_mem (show s ∈ Icc 0 t from ⟨hs,hst⟩)]
    · rw [indicator_of_notMem (show s ∉ Icc 0 t from fun h => hst h.2)]
      change Real.exp (-s)*r (t-s) = 0
      rw [hr (t-s) (by linarith),mul_zero]
  rw [he,integral_indicator measurableSet_Icc,Measure.restrict_restrict measurableSet_Icc]
  have hset : Icc 0 t ∩ Ici 0 = Icc (0:ℝ) t := inter_eq_left.mpr (fun _ h => h.1)
  rw [hset,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le ht]
  have hsub := intervalIntegral.integral_comp_sub_left
    (fun s => Real.exp (-(t-s))*r s) t (a := 0) (b := t)
  simp only [sub_self,sub_zero] at hsub
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [sub_sub_cancel]

/-- Finite-time formula for exactly the Euclidean resolvent appearing in the
published GLPS hypothesis. No time differentiability is used here. -/
theorem transportResolvent_eq {r : Published.KineticPhase → ℝ}
    (hr : ∀ z, z.1.1 < 0 → r z = 0) (z : Published.KineticPhase) (ht : 0 ≤ z.1.1) :
    Published.transportResolvent r z =
      ∫ t in 0..z.1.1, Real.exp (-(z.1.1-t))*r ((t,z.1.2-(z.1.1-t) • z.2),z.2) := by
  have H := causal_convolution
    (r := fun t => r ((t,z.1.2-(z.1.1-t) • z.2),z.2))
    (fun s hs => hr _ hs) ht
  have he : Published.transportResolvent r z =
      ∫ s in Ici (0:ℝ), Real.exp (-s)*r ((z.1.1-s,z.1.2-(z.1.1-(z.1.1-s)) • z.2),z.2) := by
    unfold Published.transportResolvent
    simp only [sub_sub_cancel]
  exact he.trans H

end BoltzmannNonuniqueness.TransportPrimitive

end

end OAI

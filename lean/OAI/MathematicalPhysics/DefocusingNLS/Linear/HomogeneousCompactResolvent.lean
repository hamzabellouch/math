import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousResolventCircle
import Mathlib.Analysis.Normed.Operator.Compact.Basic

namespace OAI

/-! # Compactness of the resolvent-contour perturbation

The compact-operator subspace is closed. Integrating a continuous curve in
that subspace therefore still gives a compact operator. The second resolvent
identity applies this fact to the exact compact perturbation of the time step.
-/

open Complex Set

namespace DefocusingNLS

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem isCompactOperator_circleIntegral {f : ℂ → E →L[ℂ] E} {c : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hf : ContinuousOn f (Metric.sphere c r))
    (hc : ∀ z, IsCompactOperator (f z)) :
    IsCompactOperator (show E →L[ℂ] E from ∮ z in C(c, r), f z) := by
  let K := compactOperator (RingHom.id ℂ) E E
  have hclosed : IsClosed (K : Set (E →L[ℂ] E)) :=
    isClosed_setOfPred_isCompactOperator
  let : CompleteSpace K := hclosed.completeSpace_coe
  let g : ℂ → K := fun z => ⟨f z, hc z⟩
  have hg : ContinuousOn g (Metric.sphere c r) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (continuousOn_iff_continuous_domRestrict.mp hf).subtype_mk
      (fun z => hc z)
  have hi := hg.circleIntegrable hr
  have he := circleIntegral_map_clm K.subtypeL hi
  change (∮ z in C(c, r), f z) =
    ((∮ z in C(c, r), g z : K) : E →L[ℂ] E) at he
  rw [he]
  exact (∮ z in C(c, r), g z : K).property

theorem circleResolventOperator_sub_isCompact (T B : E →L[ℂ] E)
    (hc : IsCompactOperator (T - B)) {r : ℝ} (hr : 0 ≤ r)
    (hT : ∀ z : ℂ, ‖z‖ = r → z ∈ resolventSet ℂ T)
    (hB : ∀ z : ℂ, ‖z‖ = r → z ∈ resolventSet ℂ B) :
    IsCompactOperator (circleResolventOperator T r - circleResolventOperator B r) := by
  let f : ℂ → E →L[ℂ] E := fun z => resolvent T z * (T - B) * resolvent B z
  have hct : ContinuousOn (resolvent T) (Metric.sphere (0 : ℂ) r) := by
    intro z hz
    exact ((spectrum.hasDerivAt_resolvent_const_left (hT z
      (by simpa only [Metric.mem_sphere, dist_zero_right] using hz))).continuousAt).continuousWithinAt
  have hcb : ContinuousOn (resolvent B) (Metric.sphere (0 : ℂ) r) := by
    intro z hz
    exact ((spectrum.hasDerivAt_resolvent_const_left (hB z
      (by simpa only [Metric.mem_sphere, dist_zero_right] using hz))).continuousAt).continuousWithinAt
  have hcf : ContinuousOn f (Metric.sphere (0 : ℂ) r) :=
    (hct.mul continuousOn_const).mul hcb
  have hcompact (z : ℂ) : IsCompactOperator (f z) := by
    exact (hc.clm_comp (resolvent T z)).comp_clm (resolvent B z)
  have hi := isCompactOperator_circleIntegral hr hcf hcompact
  have he : (∮ z in C(0, r), f z) =
      (∮ z in C(0, r), resolvent T z) - ∮ z in C(0, r), resolvent B z := by
    rw [← circleIntegral.integral_sub
      (circleIntegrable_resolvent T hr hT) (circleIntegrable_resolvent B hr hB)]
    apply circleIntegral.integral_congr hr
    intro z hz
    have hzr : ‖z‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
    exact (spectrum.resolvent_sub_resolvent (hT z hzr) (hB z hzr)).symm
  rw [he] at hi
  simpa only [circleResolventOperator, ← smul_sub, ← FunLike.coe_smul] using
    hi.smul (2 * Real.pi * I : ℂ)⁻¹

end

end DefocusingNLS

end OAI

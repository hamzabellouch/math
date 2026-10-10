import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalVertex

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital

def datumCollisionBound (t r h R C : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (9/10:ℝ)*(ENNReal.ofReal (99/100:ℝ)*midpointLower t 13))⁻¹ *
    (2*ENNReal.ofReal (hitConstant*(4*C*(2*t)*r+8*r*(1+R)^3/Real.sqrt (h/2))))

theorem datum_reference_collision {N K M G m : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (h50 : 50 < L.val) (hm : 0 < m)
    (g : Fin G) (t r R C S h : ℝ) (u : Time)
    (ht : 0<t) (hr : 0<r) (hr1 : r≤1) (hR : 0≤R) (hC : 0≤C) (hh : 0<h)
    (hu : (u:ℝ)=h/(2*t)) (hsmall : r*R≤1)
    (hτr : (2*t)/(m:ℝ)≤r^2) (hmscale : (m:ℝ)*r^2≤2*(2*t))
    (hwindow : 2*((2*t)/(m:ℝ))≤h) (hlarge : 8*(2*t)≤(m:ℝ)*h) (hdrift : 26/(m:ℝ)≤r)
    (d : PhysicalDatum N K M G L) (i j : Fin N)
    (hi : datumAccessible hL g m t r R C S u i d)
    (hy : ‖datumStart hL d i-anchorPoint (datumHome hL d i)‖≤3)
    (hz : ‖datumEnd hL d i-anchorPoint (datumHome hL d i)‖≤3)
    (hsep0 : r+2*S<torusDistance L (projectPoint L (datumStart hL d i)) (projectPoint L (datumStart hL d j)))
    (hsep1 : r+2*S<torusDistance L (projectPoint L (datumEnd hL d i)) (projectPoint L (datumEnd hL d j)))
    (f : Prod.mk d ⁻¹' datumPermitted hL g m r R C S u j) :
    referenceOn t (datumStart hL d i) (datumEnd hL d i)
      (Prod.mk d ⁻¹' datumPermitted hL g m r R C S u i)
      {p | TrialCollision r (projectCurve L f.val) p.val}≤datumCollisionBound t r h R C := by
  let A := Prod.mk d ⁻¹' datumTarget hL g m t r R C S u i 0
  let E := Prod.mk d ⁻¹' datumPermitted hL g m r R C S u i
  have hA : MeasurableSet A := (datumTarget_measurable hL g m t r R C S u i 0).preimage measurable_prodMk_left
  have hE : MeasurableSet E := (datumPermitted_measurable hL g m r R C S u i).preimage measurable_prodMk_left
  have hvol : ENNReal.ofReal (99/100:ℝ)≤volume A := hi 0
  have hA0 : volume A≠0 :=
    ((by norm_num : (0:ℝ≥0∞)<ENNReal.ofReal (99/100:ℝ)).trans_le hvol).ne'
  have hAf : volume A≠⊤ := ne_top_of_le_ne_top (by rw [unitTarget_volume]; exact ENNReal.one_ne_top)
    (measure_mono (show A⊆unitTarget (anchorPoint (datumHome hL d i)+targetStep 0) from fun _ h ↦ h.1))
  have hmem : ∀ᵐU ∂targetUniform A,U∈A := Measure.ae_smul_measure (ae_restrict_mem hA) _
  have hs : ∀ᵐU ∂targetUniform A,ENNReal.ofReal (9/10:ℝ)≤
      trialKernel t (datumStart hL d i) (datumEnd hL d i) U E := hmem.mono (fun _ h ↦ h.2)
  rw [referenceOn_collision t r _ _ hE]
  have H := individual_collision_bound hm (datumStart hL d i) (datumEnd hL d i)
    (anchorPoint (datumHome hL d i)) (projectCurve L f.val) u h50 ht hr hr1 hR hC hh hu
    hy hz f.property.1 hsmall hτr hmscale hwindow hlarge hdrift
    (by simpa only [projectCurve,ContinuousMap.coe_mk,f.property.2.2.1.1] using hsep0)
    (by simpa only [projectCurve,ContinuousMap.coe_mk,f.property.2.2.1.2] using hsep1)
    hA hA0 hAf (by norm_num : (0:ℝ)≤13)
    (fun U hU ↦ midpoint_bound _ _ _ U (hy.trans (by norm_num)) (hz.trans (by norm_num))
      (targetCell_radius _ 0 U hU.1)) E hE (fun _ h ↦ ⟨h.1,h.2.1⟩) hs
  refine H.trans ?_
  refine mul_le_mul' ?_ le_rfl
  apply ENNReal.inv_le_inv.mpr
  exact mul_le_mul' le_rfl (mul_le_mul' hvol le_rfl)

end HardSphere.Groups
end
end

end OAI

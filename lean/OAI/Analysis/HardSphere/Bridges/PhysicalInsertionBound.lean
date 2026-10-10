import Mathlib
import OAI.Analysis.HardSphere.Bridges.ReferenceHit

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff Comparison

lemma individual_collision_bound {L : Length} {n : ℕ} (hn : 0<n)
    (y z v : Point) (ω : ConfigurationPath 1 L) (w : Time) {t r S h R Creg C : ℝ}
    (hL : 50<L.val) (ht : 0<t) (hr : 0<r) (hr1 : r≤1) (hR : 0≤R)
    (hCreg : 0≤Creg) (hh : 0<h) (hw : (w:ℝ)=h/(2*t))
    (hy : ‖y-v‖≤3) (hz : ‖z-v‖≤3)
    (hreg : Regular n r R Creg w S ω) (hsmall : r*R≤1)
    (hτr : (2*t)/(n:ℝ)≤r^2) (hnscale : (n:ℝ)*r^2≤2*(2*t))
    (hwindow : 2*((2*t)/(n:ℝ))≤h) (hlarge : 8*(2*t)≤(n:ℝ)*h) (hdrift : 26/(n:ℝ)≤r)
    (hsep0 : r+2*S<torusDistance L (projectPoint L y) (ω 0 0))
    (hsep1 : r+2*S<torusDistance L (projectPoint L z) (ω 1 0))
    {A : Set Point} (hA : MeasurableSet A) (hA0 : volume A≠0) (hAfinite : volume A≠⊤)
    (hC : 0≤C) (hbound : ∀u∈A,‖u-(fun j ↦ (y j+z j)/2)‖≤C)
    (E : Set C(Time,Point)) (hE : MeasurableSet E)
    (hcut : ∀f∈E,Regular n r R Creg w S (projectCurve L f) ∧ TrialConfined L v f)
    {c : ℝ≥0∞} (hc : ∀ᵐu ∂targetUniform A,c≤trialKernel t y z u E) :
    individualReference t y z E {f | TrialCollision r ω f}≤
      (c*(volume A*midpointLower t C))⁻¹*
      (2*ENNReal.ofReal (hitConstant*(4*Creg*(2*t)*r+8*r*(1+R)^3/Real.sqrt (h/2)))) := by
  apply normalized_collision_le _ E {f | TrialCollision r ω f}
    {f | Regular n r R Creg w S (projectCurve L f) ∧ TrialConfined L v f ∧ TrialCollision r ω f}
    (trialCollision_closed r ω).measurableSet
  · intro f hf
    exact ⟨(hcut f hf.2).1,(hcut f hf.2).2,hf.1⟩
  · exact individual_normalizer_lower ht hC y z hA hA0 hAfinite hbound E hE hc
  · exact reference_collision hn y z v ω w hL (mul_pos (by norm_num) ht) hr hr1 hR hCreg hh hw
      hy hz hreg hsmall hτr hnscale hwindow hlarge hdrift hsep0 hsep1

end HardSphere.Bridge

end
end

end

end OAI

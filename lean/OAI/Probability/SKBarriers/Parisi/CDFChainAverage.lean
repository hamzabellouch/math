import Mathlib
import OAI.Probability.SKBarriers.Gaussian.BoundedPrimitive
import OAI.Probability.SKBarriers.Hierarchy.TimeChainRepresentation

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def scalarTimeChainAverage (β : ℝ) (l : List (ℝ × ℝ≥0)) (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  scalarHierarchyAverage l.length (fun i => (l.get i).1)
    (fun i => β*Real.sqrt ((l.get i).2:ℝ)) f g x

theorem scalarCDFAverage_eq_chainAverage {f g dg : ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : ∀ y, HasDerivAt g (dg y) y) (hdg : Continuous dg)
    {K B C : ℝ≥0} (hfK : LipschitzWith K f)
    (hB : ∀ y, |g y| ≤ B) (hC : ∀ y, |dg y| ≤ C)
    (β : ℝ) {α : ℝ → ℝ} (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    (l : List (ℝ × ℝ≥0)) (hm : ∀ p∈l, p.1∈Icc (0:ℝ) 1)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (hdur : chainDuration l=t)
    (hmodel : TimeChainModels α s l) (x : ℝ) :
    scalarCDFAverage β α s t f g x=scalarTimeChainAverage β l f g x := by
  let G := boundedPrimitive g
  have hc : Continuous g := continuous_iff_continuousAt.mpr (fun y => (hg y).continuousAt)
  have hG : BoundedDerivs G := boundedPrimitive_regular hg hdg hB hC
  have hGd : ∀ y, HasDerivAt G (g y) y := boundedPrimitive_hasDerivAt hc
  have hGB : LipschitzWith B G := boundedPrimitive_lipschitz hc hB
  have he : (fun a => scalarCDFOperator β α s t (primitivePerturbation f G a) x)=
      fun a => scalarTimeChain β l (primitivePerturbation f G a) x := by
    funext a
    exact scalarCDFOperator_eq_chain (primitivePerturbation_regular hf hG a)
      (primitivePerturbation_lipschitz hfK hGB a) β hα hmono l hm s t ht hdur hmodel x
  rw [scalarCDFAverage_eq_terminalDerivative β α s t hf hG hGd]
  have hd := (scalarCDFOperator_terminal_hasDerivAt β hα hmono hf hG hGd hg hfK hGB hB hC s t ht x 0).deriv
  rw [he] at hd
  rw [← hd]
  simp only [scalarTimeChain_eq_hierarchy]
  rw [scalarHierarchy_primitive_derivative _ _ _ hf hG hGd,
    primitivePerturbation_zero]
  simp only [add_zero,scalarTimeChainAverage]

end SK.Analytic

end
end

end OAI

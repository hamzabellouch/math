import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.HessianUpperTransfer

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section HessianSequentialUpper
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

lemma sequential_quadratic_upper_transfer
    {Aj:ℕ → E →L[ℝ] E} {A:E →L[ℝ] E}
    (hA:Function.Injective A) (hAlim:Tendsto Aj atTop (𝓝 A))
    {Hj Bj Ej:ℕ → E →L[ℝ] E →L[ℝ] ℝ}
    {Qj:ℕ → E →L[ℝ] E →L[ℝ] E} {pj:ℕ → E →L[ℝ] ℝ}
    {E0:E →L[ℝ] E →L[ℝ] ℝ} {Q:E →L[ℝ] E →L[ℝ] E}
    (hElim:Tendsto Ej atTop (𝓝 E0)) (hQlim:Tendsto Qj atTop (𝓝 Q))
    (he:∀ᶠ i in atTop,∀d,Bj i d d=Ej i d d+Hj i (Aj i d) (Aj i d)+pj i (Qj i d d))
    {P C:ℝ} (hP:0 ≤ P) (hC:0 ≤ C)
    (hp:∀ᶠ i in atTop,‖pj i‖ ≤ P)
    (hB:∀ᶠ i in atTop,∀d,Bj i d d ≤ C*‖d‖^2) :
    ∃K≥0,∀ᶠ i in atTop,∀d,Hj i d d ≤ K*‖d‖^2 := by
  obtain ⟨R,hR,HR⟩:=eventually_bounded_right_inverse hA hAlim
  have HE : ∀ᶠ i in atTop, ‖Ej i‖ < ‖E0‖+1 := ((continuous_norm.tendsto E0).comp hElim).eventually (gt_mem_nhds (lt_add_one ‖E0‖))
  have HQ : ∀ᶠ i in atTop, ‖Qj i‖ < ‖Q‖+1 := ((continuous_norm.tendsto Q).comp hQlim).eventually (gt_mem_nhds (lt_add_one ‖Q‖))
  refine ⟨(C+(‖E0‖+1)+P*(‖Q‖+1))*R^2,by positivity,?_⟩
  filter_upwards [HR,HE,HQ,he,hp,hB] with i hi hei hqi heqi hpi hbi
  obtain ⟨r,hr,hri⟩:=hi
  intro w
  apply (quadratic_upper_transfer hr heqi hC hbi w).trans
  gcongr

end HessianSequentialUpper
end WeakMTWTransport

end
end

end OAI

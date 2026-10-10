import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowLocalEquation
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowSliceBound

namespace OAI

/-! The first variational estimate from the joint norm hypothesis. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace ContinuumCoulomb

theorem flow_actual_first_bound {U : Set (ℝ × Position)} (hU : IsOpen U)
    (hslab : Icc (0:ℝ) 1 ×ˢ (univ : Set Position) ⊆ U)
    (v : ℝ → Position → Position)
    (hv : ContDiffOn ℝ 4 (fun p : ℝ × Position => v p.1 p.2) U)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow v G)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, ∀ z,
      ‖iteratedFDeriv ℝ 1 (fun p : ℝ × Position => v p.1 p.2) (t,z)‖ ≤ B)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : Position) :
    ‖iteratedFDeriv ℝ 1 (fun y => G y t) x‖ ≤ Real.exp B := by
  rw [norm_iteratedFDeriv_one]
  apply flow_first_derivative_bound_along hU hslab v hv G hG B hB x
  · obtain ⟨_H,W,_O,_hH,hW,_hO,_hx,_hEq,_hODE,hWv⟩ :=
      flow_local_equation hU hslab v hv G hG x
    intro s hs
    have heq : (fun z => W (s,z)) =ᶠ[𝓝 (G x s)] v s :=
      (hWv s hs).comp_tendsto (continuousAt_const.prodMk continuousAt_id)
    have hslice := flow_slice_derivative_bound W hW 1 (by norm_num) s (G x s)
    rw [norm_iteratedFDeriv_one,heq.fderiv_eq] at hslice
    apply hslice.trans
    rw [(hWv s hs).iteratedFDeriv ℝ 1 |>.eq_of_nhds]
    exact hb s hs (G x s)
  · exact ht

end ContinuumCoulomb

end

end OAI

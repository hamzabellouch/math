import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowLocalModel
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowVariational

namespace OAI

/-! The actual closed-interval flow satisfies its first variational equation.
The proof transfers the equation from a smooth local representative. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace ContinuumCoulomb

theorem flow_spatial_variational {U : Set (ℝ × Position)} (hU : IsOpen U)
    (hslab : Icc (0:ℝ) 1 ×ˢ (univ : Set Position) ⊆ U)
    (v : ℝ → Position → Position)
    (hv : ContDiffOn ℝ 4 (fun p : ℝ × Position => v p.1 p.2) U)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow v G)
    (x e : Position) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun s => fderiv ℝ (fun y => G y s) x e)
      (fderiv ℝ (v t) (G x t) (fderiv ℝ (fun y => G y t) x e))
      (Icc (0:ℝ) 1) t := by
  obtain ⟨H,hH,hEq⟩ := flow_local_model hU hslab v hv G hG x
  obtain ⟨O,hOsub,hO,hx⟩ := mem_nhds_iff.mp hEq
  have hODE (y : Position) (hy : y ∈ O) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      HasDerivWithinAt (fun r => H (r,y)) (v s (H (s,y))) (Icc (0:ℝ) 1) s := by
    have hd := hG.2 y s hs
    rw [hOsub hy s hs] at hd
    exact hd.congr_of_mem (fun r hr => (hOsub hy r hr).symm) hs
  have hJ (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      fderiv ℝ (fun y => G y s) x = fderiv ℝ (fun y => H (s,y)) x := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hO.mem_nhds hx] with y hy
    exact hOsub hy s hs
  have hv' : DifferentiableAt ℝ (v t) (H (t,x)) := by
    have hh := (hv.contDiffAt (hU.mem_nhds (hslab ⟨ht,mem_univ (H (t,x))⟩))).comp
      (H (t,x)) (contDiffAt_const.prodMk contDiffAt_id)
    exact hh.differentiableAt (by norm_num)
  have hd := flow_model_variational H hH v O hO x hx hODE t ht hv' e
  rw [←hOsub hx t ht,←hJ t ht] at hd
  exact hd.congr_of_mem (fun s hs => congrArg (fun L => L e) (hJ s hs)) ht

end ContinuumCoulomb

end

end OAI

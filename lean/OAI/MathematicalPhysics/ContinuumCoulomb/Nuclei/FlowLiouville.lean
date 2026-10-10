import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowJacobianVariation
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowMatrix

namespace OAI

/-! Liouville's equation for the actual spatial Jacobian, on the closed time
interval and without an invertibility assumption. -/

noncomputable section
open Set
open scoped ContDiff
namespace ContinuumCoulomb

theorem flow_liouville {U : Set (ℝ × Position)} (hU : IsOpen U)
    (hslab : Icc (0:ℝ) 1 ×ˢ (univ : Set Position) ⊆ U)
    (v : ℝ → Position → Position)
    (hv : ContDiffOn ℝ 4 (fun p : ℝ × Position => v p.1 p.2) U)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow v G)
    (x : Position) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun s => flowJacobian G s x)
      (fieldDivergence (v t) (G x t) * flowJacobian G t x) (Icc (0:ℝ) 1) t := by
  let J : ℝ → Matrix (Fin 3) (Fin 3) ℝ :=
    fun s => flowMatrix (fderiv ℝ (fun y => G y s) x)
  let A : Matrix (Fin 3) (Fin 3) ℝ := flowMatrix (fderiv ℝ (v t) (G x t))
  have hv' : DifferentiableAt ℝ (v t) (G x t) := by
    have hh := (hv.contDiffAt (hU.mem_nhds (hslab ⟨ht,mem_univ (G x t)⟩))).comp
      (G x t) (contDiffAt_const.prodMk contDiffAt_id)
    exact hh.differentiableAt (by norm_num)
  have hJ (a b : Fin 3) :
      HasDerivWithinAt (fun s => J s a b) ((A * J t) a b) (Icc (0:ℝ) 1) t := by
    have hd := (flowCoordinate a).hasFDerivAt.comp_hasDerivWithinAt t
      (flow_spatial_variational hU hslab v hv G hG x (NeutralAtom.axis b) t ht)
    have hvalue : flowCoordinate a
        (fderiv ℝ (v t) (G x t) (fderiv ℝ (fun y => G y t) x (NeutralAtom.axis b))) =
        (A * J t) a b := by
      change _ = (flowMatrix (fderiv ℝ (v t) (G x t)) *
        flowMatrix (fderiv ℝ (fun y => G y t) x)) a b
      rw [←flowMatrix_comp,flowMatrix_apply]
      rfl
    rw [hvalue] at hd
    apply hd.congr_of_mem
    · intro s _
      exact flowMatrix_apply _ a b
    · exact ht
  have hd := flow_matrix_det_derivative J A (Icc (0:ℝ) 1) t hJ
  have hvalue : A.trace * (J t).det =
      fieldDivergence (v t) (G x t) * flowJacobian G t x := by
    rw [show A.trace = fieldDivergence (v t) (G x t) from flowMatrix_trace (v t) (G x t) hv']
    rw [show (J t).det = flowJacobian G t x from flowMatrix_det _]
  rw [hvalue] at hd
  exact hd.congr_of_mem (fun s _ => (flowMatrix_det _).symm) ht

theorem flow_regularity {U : Set (ℝ × Position)} (hU : IsOpen U)
    (hslab : Icc (0:ℝ) 1 ×ˢ (univ : Set Position) ⊆ U)
    (v : ℝ → Position → Position)
    (hv : ContDiffOn ℝ 4 (fun p : ℝ × Position => v p.1 p.2) U)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow v G) :
    (∀ t ∈ Icc (0:ℝ) 1, ContDiff ℝ 4 (fun x => G x t)) ∧
    (∀ x t, t ∈ Icc (0:ℝ) 1 →
      HasDerivWithinAt (fun s => flowJacobian G s x)
        (fieldDivergence (v t) (G x t) * flowJacobian G t x) (Icc (0:ℝ) 1) t) :=
  ⟨flow_spatial_C4 hU hslab v hv G hG,flow_liouville hU hslab v hv G hG⟩

end ContinuumCoulomb

end

end OAI

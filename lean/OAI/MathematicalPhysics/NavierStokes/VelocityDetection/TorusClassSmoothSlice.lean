import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TorusClassContinuousOnEnergy

namespace OAI

noncomputable section
namespace VelocityDetection.TorusClass
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators

theorem smooth_slice {F : ScalarField 3} (hf : ContDiff ℝ ∞ (uncurry F)) (t : ℝ) :
    ContDiff ℝ ∞ (F t) := hf.comp (contDiff_const.prodMk contDiff_id)

theorem D_joint {F : ScalarField 3} (hf : ContDiff ℝ ∞ (uncurry F)) (i : Fin 3) :
    (fun q : ℝ × Space => D i (F q.1) q.2) =
      JointCalculus.dAlong (0,Pi.single i 1) (uncurry F) := by
  funext q
  rw [← spatialD_eq ((smooth_slice hf q.1).differentiable (by simp)),
    JointCalculus.spatialD_eq hf]

@[fun_prop] theorem contDiff_joint_D {F : ScalarField 3}
    (hf : ContDiff ℝ ∞ (uncurry F)) (i : Fin 3) :
    ContDiff ℝ ∞ (fun q : ℝ × Space => D i (F q.1) q.2) := by
  rw [D_joint hf i]
  exact JointCalculus.contDiff_dAlong _ hf

theorem ComparisonClass.of_smooth {u : VectorField 3} {p : ScalarField 3}
    (hu : ContDiff ℝ ∞ (uncurry u)) (hp : ContDiff ℝ ∞ (uncurry p))
    (hup : ∀ t ≥ 0, FactorsThrough (u t) PeriodicSpace.cover)
    (hpp : ∀ t ≥ 0, periodic (p t))
    (hm : ∀ t ≥ 0, (∫ x, p t x ∂measure) = 0) : ComparisonClass u p := by
  have hs (i : Fin 3) : ContDiff ℝ ∞ (uncurry (fun t X => u t X i)) :=
    (contDiff_apply ℝ ℝ i).comp hu
  refine ⟨?_,?_,hup,hpp,hm,?_,?_,?_,?_,?_,?_,?_⟩
  · intro t _ i
    exact (smooth_slice (hs i) t).of_le (by exact WithTop.coe_le_coe.mpr le_top)
  · intro t _
    exact (smooth_slice hp t).of_le (by exact WithTop.coe_le_coe.mpr le_top)
  · intro t ht X i
    have hh : ContDiff ℝ ∞ (fun s : ℝ => u s X i) :=
      (hs i).comp (contDiff_id.prodMk contDiff_const)
    exact (hh.differentiable (by simp) t).differentiableWithinAt.hasDerivWithinAt
  · intro T _ i
    exact (hs i).continuous.continuousOn
  · intro T _ i
    apply (JointCalculus.contDiff_dAlong (1,0) (hs i)).continuous.continuousOn.congr
    intro q hq
    exact JointCalculus.timeD_eq (hs i) hq.1.1 q.2
  · intro T _ i k
    exact (contDiff_joint_D (hs i) k).continuous.continuousOn
  · intro T _ i k l
    exact (contDiff_joint_D (F := fun t X => D k (fun y => u t y i) X)
      (contDiff_joint_D (hs i) k) l).continuous.continuousOn
  · intro T _
    exact hp.continuous.continuousOn
  · intro T _ i
    exact (contDiff_joint_D hp i).continuous.continuousOn

end VelocityDetection.TorusClass
end

end OAI

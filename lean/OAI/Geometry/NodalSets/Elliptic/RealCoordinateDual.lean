import Mathlib.Topology.UniformSpace.UniformConvergence
import OAI.Geometry.NodalSets.Elliptic.RealPartialJetLipschitz

namespace OAI

namespace Yau.Geometry
open Yau.Analysis Set Metric Filter
open scoped Topology ContDiff
noncomputable section

def realCoordinateDual : Yau.Jets.Coord →L[ℝ] (Yau.Jets.Coord →L[ℝ] ℝ) :=
  ∑ i : Fin 4, (ContinuousLinearMap.proj i).smulRight (ContinuousLinearMap.proj i)

lemma realCoordinateDual_apply (a v : Yau.Jets.Coord) :
    realCoordinateDual a v = ∑ i, a i*v i := by
  simp [realCoordinateDual]

lemma realCoordinateDual_single (a : Yau.Jets.Coord) (i : Fin 4) :
    realCoordinateDual a (Pi.single i 1) = a i := by
  simp [realCoordinateDual_apply,Pi.single_apply]

lemma real_fderiv_coordinateDual (F : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) :
    fderiv ℝ F x = realCoordinateDual (fun i ↦ fderiv ℝ F x (Pi.single i 1)) := by
  ext v
  have he : v = ∑ i : Fin 4, v i • (Pi.single i 1 : Yau.Jets.Coord) := by
    ext i
    simp [Finset.sum_apply,Pi.single_apply]
  conv_lhs => rw [he]
  simp [realCoordinateDual_apply,mul_comm]

theorem real_uniform_coordinate_dual {F : Fin 4 → ℕ → Yau.Jets.Coord → ℝ}
    {g : Fin 4 → Yau.Jets.Coord → ℝ} {Q : Set Yau.Jets.Coord}
    (h : ∀ i, TendstoUniformlyOn (F i) (g i) atTop Q) :
    TendstoUniformlyOn (fun j x ↦ realCoordinateDual (fun i ↦ F i j x))
      (fun x ↦ realCoordinateDual (fun i ↦ g i x)) atTop Q := by
  apply realCoordinateDual.uniformContinuous.comp_tendstoUniformlyOn
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hh (i : Fin 4) := Metric.tendstoUniformlyOn_iff.mp (h i) ε hε
  filter_upwards [Filter.eventually_all.mpr hh] with j hj x hx
  exact (dist_pi_lt_iff hε).mpr (fun i ↦ hj i x hx)

end
end Yau.Geometry

end OAI

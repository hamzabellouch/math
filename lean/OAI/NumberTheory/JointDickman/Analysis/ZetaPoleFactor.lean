import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace OAI

/-! # Removing the simple pole of zeta at one -/
namespace JointDickman
open Filter
open scoped Topology

noncomputable def zetaPoleFactor (s : ℂ) : ℂ :=
  if s = 1 then 1 else (s-1)*riemannZeta s

@[simp] theorem zetaPoleFactor_one : zetaPoleFactor 1 = 1 := by simp [zetaPoleFactor]

 theorem zetaPoleFactor_eq {s : ℂ} (hs : s ≠ 1) : zetaPoleFactor s = (s-1)*riemannZeta s := by
  simp only [zetaPoleFactor,hs,ite_false]

 theorem zetaPoleFactor_continuousAt_one : ContinuousAt zetaPoleFactor 1 := by
  rw [← continuousWithinAt_compl_self,ContinuousWithinAt,zetaPoleFactor_one]
  apply riemannZeta_residue_one.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (zetaPoleFactor_eq hs).symm

 theorem zetaPoleFactor_differentiableAt {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ zetaPoleFactor s := by
  have heq : zetaPoleFactor =ᶠ[𝓝 s] (fun t => (t-1)*riemannZeta t) := by
    filter_upwards [eventually_ne_nhds hs] with t ht
    exact zetaPoleFactor_eq ht
  exact ((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hs)).congr_of_eventuallyEq heq

 theorem zetaPoleFactor_analyticAt_one : AnalyticAt ℂ zetaPoleFactor 1 := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ zetaPoleFactor_continuousAt_one
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact zetaPoleFactor_differentiableAt hs

end JointDickman

end OAI

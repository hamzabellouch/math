import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Topology.MetricSpace.Antilipschitz

namespace OAI

/-! Actual Schwartz restrictions to affine reference lines. This applies
to general two-variable packets, with no tensor factorization. -/

noncomputable section
open scoped NNReal
namespace LipschitzHilbert

theorem affineLine_antilipschitz (b s : ℝ) :
    AntilipschitzWith 1 (fun x : ℝ => (x,b+s*x)) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  simp only [NNReal.coe_one,one_mul,Prod.dist_eq]
  exact le_max_left _ _

theorem affineLine_temperate (b s : ℝ) :
    Function.HasTemperateGrowth (fun x : ℝ => (x,b+s*x)) := by
  let A : ℝ →L[ℝ] (ℝ × ℝ) := (ContinuousLinearMap.id ℝ ℝ).prod
    (s • ContinuousLinearMap.id ℝ ℝ)
  have h := (Function.HasTemperateGrowth.const (E := ℝ) (0,b)).add A.hasTemperateGrowth
  change Function.HasTemperateGrowth (fun x => (0,b)+A x) at h
  simpa only [A,ContinuousLinearMap.prod_apply,smul_apply,
    ContinuousLinearMap.id_apply,Prod.mk_add_mk,zero_add,smul_eq_mul] using h

def planarSchwartzSlice (f : SchwartzMap (ℝ × ℝ) ℂ) (b s : ℝ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (g := fun x : ℝ => (x,b+s*x))
    (affineLine_temperate b s) (affineLine_antilipschitz b s) f

@[simp] theorem planarSchwartzSlice_apply (f : SchwartzMap (ℝ × ℝ) ℂ) (b s x : ℝ) :
    planarSchwartzSlice f b s x = f (x,b+s*x) := rfl

theorem planarSchwartzSlice_hasDerivAt (f : SchwartzMap (ℝ × ℝ) ℂ) (b s x : ℝ) :
    HasDerivAt (planarSchwartzSlice f b s)
      (fderiv ℝ f (x,b+s*x) (1,s)) x := by
  have hline : HasDerivAt (fun t : ℝ => (t,b+s*t)) (1,s) x := by
    simpa only [mul_one,zero_add,Pi.add_apply,id_eq] using (hasDerivAt_id x).prodMk
      ((hasDerivAt_const x b).add ((hasDerivAt_id x).const_mul s))
  exact (f.hasFDerivAt (x,b+s*x)).comp_hasDerivAt x hline

theorem planarSchwartzSlice_vertical_hasDerivAt (f : SchwartzMap (ℝ × ℝ) ℂ) (b s x : ℝ) :
    HasDerivAt (fun y => planarSchwartzSlice f y s x)
      (fderiv ℝ f (x,b+s*x) (0,1)) b := by
  have hline : HasDerivAt (fun y : ℝ => (x,y+s*x)) (0,1) b := by
    simpa only [add_zero,id_eq] using (hasDerivAt_const b x).prodMk
      ((hasDerivAt_id b).add_const (s*x))
  exact (f.hasFDerivAt (x,b+s*x)).comp_hasDerivAt b hline

theorem planarSchwartzSlice_jointContinuous (f : SchwartzMap (ℝ × ℝ) ℂ) (s : ℝ) :
    Continuous (fun z : ℝ × ℝ => planarSchwartzSlice f z.1 s z.2) := by
  change Continuous (fun z : ℝ × ℝ => f (z.2,z.1+s*z.2))
  exact f.continuous.comp (by fun_prop)

end LipschitzHilbert

end

end OAI

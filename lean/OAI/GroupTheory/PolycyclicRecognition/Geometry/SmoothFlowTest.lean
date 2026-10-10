import OAI.GroupTheory.PolycyclicRecognition.Geometry.FlowIntegrationByParts
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialCoordinateTopology
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace OAI

/-! # The derivative of a smooth test function along a coordinate flow -/

noncomputable section

namespace PolycyclicRecognition

open Set
open scoped ContDiff

theorem exists_smooth_flow_test_derivative
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : V → V → V) (hm : ContDiff ℝ ∞ (fun z : V × V => m z.1 z.2))
    (hm0 : ∀ g, m g 0 = g)
    (φ : V → ℝ) (hφ : ContDiff ℝ ∞ φ) (v : V) :
    ∃ dφ : ℝ → V → ℝ, Continuous dφ.uncurry ∧
      (∀ t g, HasDerivAt (fun s : ℝ => φ (m g ((-s) • v))) (dφ t g) t) ∧
      ∀ g, dφ 0 g = -(fderiv ℝ φ g ((fderiv ℝ (m g) 0) v)) := by
  let ψ : ℝ × V → ℝ := fun z => φ (m z.2 ((-z.1) • v))
  have hψ : ContDiff ℝ ∞ ψ :=
    hφ.comp (hm.comp (contDiff_snd.prodMk (contDiff_fst.neg.smul contDiff_const)))
  let dφ : ℝ → V → ℝ := fun t g => (fderiv ℝ ψ (t, g)) (1, 0)
  have hd (t : ℝ) (g : V) :
      HasDerivAt (fun s : ℝ => φ (m g ((-s) • v))) (dφ t g) t := by
    exact (hψ.differentiable (by simp) (t, g)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t g))
  refine ⟨dφ, ?_, hd, ?_⟩
  · exact (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  · intro g
    have hmg : DifferentiableAt ℝ (m g) 0 :=
      ((hm.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)) 0
    have hin : HasDerivAt (fun s : ℝ => (-s) • v) (-v) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).neg.smul_const v)
    have hpath : HasDerivAt (fun s : ℝ => m g ((-s) • v))
        ((fderiv ℝ (m g) 0) (-v)) 0 := by
      have hh : HasFDerivAt (m g) (fderiv ℝ (m g) 0) ((- (0 : ℝ)) • v) := by
        simpa only [neg_zero, zero_smul] using hmg.hasFDerivAt
      exact hh.comp_hasDerivAt 0 hin
    have houter := ((hφ.differentiable (by simp)) (m g ((-(0 : ℝ)) • v))).hasFDerivAt.comp_hasDerivAt 0 hpath
    have heq : dφ 0 g = -(fderiv ℝ φ g ((fderiv ℝ (m g) 0) v)) := by
      apply (hd 0 g).unique
      simpa only [neg_zero, zero_smul, hm0, map_neg, Function.comp_def] using houter
    exact heq

end PolycyclicRecognition

end

end OAI

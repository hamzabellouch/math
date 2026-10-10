import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.QuadraticBound
import OAI.Geometry.TamingCompatibility.DifferentialForms.MetricTensor

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalJets
open scoped RealInnerProductSpace ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (V →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (V →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (MetricTensor (V := V)) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (MetricTensor (V := V)) := ContinuousLinearMap.toNormedSpace

omit [FiniteDimensional ℝ V] in

lemma metricDerivative_symmetric (g : V → MetricTensor (V := V))
    (G : MetricDerivative (V := V)) (hg : HasFDerivAt g G 0)
    (hsym : ∀ z v w, g z v w = g z w v) :
    ∀ u v w, G u v w = G u w v := by
  intro u v w
  have hvw := (hg.clm_apply (hasFDerivAt_const v (0 : V))).clm_apply
    (hasFDerivAt_const w (0 : V))
  have hwv := (hg.clm_apply (hasFDerivAt_const w (0 : V))).clm_apply
    (hasFDerivAt_const v (0 : V))
  have heq : (fun z => g z v w) = (fun z => g z w v) := funext fun z => hsym z v w
  rw [heq] at hvw
  have he := congrArg (fun L : V →L[ℝ] ℝ => L u) (hvw.unique hwv)
  simpa using he

def normalChart (G : MetricDerivative (V := V)) : OpenPartialHomeomorph V V :=
  HasStrictFDerivAt.toOpenPartialHomeomorph (coordinateJet G)
    (f' := ContinuousLinearEquiv.refl ℝ V) (coordinateJet_hasStrictFDerivAt_zero G)

lemma normalChart_apply (G : MetricDerivative (V := V)) (z : V) :
    normalChart G z = coordinateJet G z := rfl

lemma normalChart_mem_source (G : MetricDerivative (V := V)) :
    (0 : V) ∈ (normalChart G).source :=
  HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source
    (f' := ContinuousLinearEquiv.refl ℝ V) (coordinateJet_hasStrictFDerivAt_zero G)

lemma normalChart_contDiff (G : MetricDerivative (V := V)) :
    ContDiff ℝ ∞ (normalChart G) := coordinateJet_contDiff G

lemma normal_metric_quadratic (g : V → MetricTensor (V := V))
    (hg : ContDiffAt ℝ ∞ g 0) (hg0 : g 0 = innerSL ℝ)
    (hsym : ∀ z v w, g z v w = g z w v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 < r ∧ ∀ z : V, ‖z‖ ≤ r →
      ‖pullbackMetric g (fderiv ℝ g 0) z - (show MetricTensor (V := V) from innerSL ℝ (E := V))‖ ≤ C*‖z‖^2 ∧
      ‖fderiv ℝ (pullbackMetric g (fderiv ℝ g 0)) z‖ ≤ C*‖z‖ := by
  have hd := (hg.differentiableAt (by simp)).hasFDerivAt
  have hG := metricDerivative_symmetric g (fderiv ℝ g 0) hd hsym
  obtain ⟨C,hC,r,hr,h⟩ := LocalTaylor.quadratic_bound
    ((pullbackMetric_contDiffAt g (fderiv ℝ g 0) hg).of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
    (pullbackMetric_fderiv_zero g (fderiv ℝ g 0) hg hd hg0 hG)
  refine ⟨C,hC,r,hr,?_⟩
  simpa only [pullbackMetric_zero, hg0] using h

end TamingCompatibility.GeometricHilbert.NormalJets

end

end OAI

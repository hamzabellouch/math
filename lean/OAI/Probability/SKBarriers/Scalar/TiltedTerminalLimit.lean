import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.RootGeneralCurvature
import OAI.Probability.SKBarriers.Scalar.DyadicSpin
import OAI.Probability.SKBarriers.Scalar.ScalarGeneralTerminal
import OAI.Probability.SKBarriers.Scalar.TerminalPerturbation

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyPressure_rootGradient_lipschitz (n : ℕ) (m : Fin n → ℝ)
    {B C : ℝ≥0} (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (hmono : Monotone m)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f)
    (hB : ∀ z, |rootGradient n f z| ≤ B) (hC : ∀ z, |rootHessian n f z| ≤ C) :
    LipschitzWith (C+2*B^2) (rootGradient 0 (hierarchyPressure n m f)) := by
  have hf' := hierarchyPressure_boundedDerivs n m f hf
  have hd (x : ℝ) : HasDerivAt (rootGradient 0 (hierarchyPressure n m f))
      (rootHessian 0 (hierarchyPressure n m f) x) x := by
    simpa only [parameterAxis,smul_eq_mul,mul_one,zero_add] using
      rootGradientLine_hasDerivAt 0 hf' 0 x
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hd x).differentiableAt)
  intro x
  rw [(hd x).deriv]
  have H := hierarchyPressure_rootHessian_bound n m (u := 1) (by norm_num) B.coe_nonneg
    (fun i => (hm i).1) (fun i => (hm i).2) hmono hf hB hC x
  norm_num only [mul_one] at H
  exact_mod_cast H

theorem scalarHierarchy_primitive_regular (n : ℕ) (m v : Fin n → ℝ)
    {f G : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G) (x : ℝ) :
    BoundedDerivs (fun a => scalarHierarchy n m v (primitivePerturbation f G a) x) := by
  have he := funext (hierarchyPressure_scalarParameterTerminal n m v (primitivePerturbation f G) x)
  rw [← he]
  exact hierarchyPressure_boundedDerivs n m _ (primitiveParameterTerminal_regular n v hf hG x)

theorem scalarHierarchy_primitive_derivative_lipschitz (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (hmono : Monotone m)
    {f G g dg : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G)
    (hg : ∀ y, HasDerivAt G (g y) y) (hdg : ∀ y, HasDerivAt g (dg y) y)
    {B C : ℝ≥0} (hB : ∀ y, |g y| ≤ B) (hC : ∀ y, |dg y| ≤ C) (x : ℝ) :
    LipschitzWith (C+2*B^2) (deriv (fun a => scalarHierarchy n m v (primitivePerturbation f G a) x)) := by
  rw [← funext (hierarchyPressure_scalarParameterTerminal n m v (primitivePerturbation f G) x)]
  change LipschitzWith (C+2*B^2) (rootGradient 0 _)
  apply hierarchyPressure_rootGradient_lipschitz n m hm hmono
    (primitiveParameterTerminal_regular n v hf hG x)
  · intro z
    rw [primitiveParameterTerminal_rootGradient n v hf hG hg]
    exact hB _
  · intro z
    rw [primitiveParameterTerminal_rootHessian n v hf hG hg hdg]
    exact hC _

theorem dyadicScalar_primitive_regular (β : ℝ) (α : ℝ → ℝ) (n : ℕ) (s : ℝ) (t : ℝ≥0)
    {f G : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G) (x : ℝ) :
    BoundedDerivs (fun a => dyadicScalar β α n s t (primitivePerturbation f G a) x) := by
  simp only [dyadicScalar,scalarTimeChain_eq_hierarchy]
  exact scalarHierarchy_primitive_regular _ _ _ hf hG x

theorem dyadicScalar_primitive_derivative_lipschitz (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hmono : Monotone α) (n : ℕ) (s : ℝ) (t : ℝ≥0)
    {f G g dg : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G)
    (hg : ∀ y, HasDerivAt G (g y) y) (hdg : ∀ y, HasDerivAt g (dg y) y)
    {B C : ℝ≥0} (hB : ∀ y, |g y| ≤ B) (hC : ∀ y, |dg y| ≤ C) (x : ℝ) :
    LipschitzWith (C+2*B^2) (deriv (fun a => dyadicScalar β α n s t (primitivePerturbation f G a) x)) := by
  simp only [dyadicScalar,scalarTimeChain_eq_hierarchy]
  apply scalarHierarchy_primitive_derivative_lipschitz _ _ _ _ _ hf hG hg hdg hB hC x
  · intro i
    exact dyadicIntervals_mass_bounds hα n s t (List.get_mem _ i)
  · exact scalarTimeChain_mass_monotone _ (dyadicIntervals_pairwise hmono n s t)

def scalarCDFTerminalDerivative (β : ℝ) (α : ℝ → ℝ) (s : ℝ) (t : ℝ≥0)
    (f G : ℝ → ℝ) (x a : ℝ) : ℝ :=
  limUnder atTop (fun n => deriv (fun b => dyadicScalar β α n s t (primitivePerturbation f G b) x) a)

theorem dyadicScalar_primitive_uniform (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    {f G : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G)
    {K B : ℝ≥0} (hfK : LipschitzWith K f) (hGB : LipschitzWith B G)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    TendstoUniformly (fun n a => dyadicScalar β α n s t (primitivePerturbation f G a) x)
      (fun a => scalarCDFOperator β α s t (primitivePerturbation f G a) x) atTop :=
  (geometric_uniform_limit (fun n a => dyadicScalar β α n s t (primitivePerturbation f G a) x)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)<1)
    (fun n a => dyadicScalar_successive_geometric_general (primitivePerturbation_regular hf hG a)
      (primitivePerturbation_lipschitz hfK hGB a) β hα hmono n s t ht x)).1

theorem dyadicScalar_terminal_derivative_uniform (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    {f G g dg : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G)
    (hg : ∀ y, HasDerivAt G (g y) y) (hdg : ∀ y, HasDerivAt g (dg y) y)
    {K B C : ℝ≥0} (hfK : LipschitzWith K f) (hGB : LipschitzWith B G)
    (hB : ∀ y, |g y| ≤ B) (hC : ∀ y, |dg y| ≤ C)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    TendstoUniformly (fun n => deriv (fun a => dyadicScalar β α n s t (primitivePerturbation f G a) x))
      (scalarCDFTerminalDerivative β α s t f G x) atTop := by
  apply uniformCauchySeq_limUnder
  apply uniformCauchySeq_derivative (C+2*B^2)
    (fun n a => (dyadicScalar_primitive_regular β α n s t hf hG x).1.differentiable (by decide) a |>.hasDerivAt)
    (fun n => dyadicScalar_primitive_derivative_lipschitz β hα hmono n s t hf hG hg hdg hB hC x)
  exact (dyadicScalar_primitive_uniform β hα hmono hf hG hfK hGB s t ht x).tendstoUniformlyOn.uniformCauchySeqOn

theorem scalarCDFOperator_terminal_hasDerivAt (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    {f G g dg : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G)
    (hg : ∀ y, HasDerivAt G (g y) y) (hdg : ∀ y, HasDerivAt g (dg y) y)
    {K B C : ℝ≥0} (hfK : LipschitzWith K f) (hGB : LipschitzWith B G)
    (hB : ∀ y, |g y| ≤ B) (hC : ∀ y, |dg y| ≤ C)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x a : ℝ) :
    HasDerivAt (fun b => scalarCDFOperator β α s t (primitivePerturbation f G b) x)
      (scalarCDFTerminalDerivative β α s t f G x a) a := by
  apply hasDerivAt_of_tendstoUniformly
    (dyadicScalar_terminal_derivative_uniform β hα hmono hf hG hg hdg hfK hGB hB hC s t ht x)
    (Eventually.of_forall (fun n b =>
      (dyadicScalar_primitive_regular β α n s t hf hG x).1.differentiable (by decide) b |>.hasDerivAt))
    (fun b => (dyadicScalar_primitive_uniform β hα hmono hf hG hfK hGB s t ht x).tendsto_at b) a

end SK.Analytic

end
end

end OAI

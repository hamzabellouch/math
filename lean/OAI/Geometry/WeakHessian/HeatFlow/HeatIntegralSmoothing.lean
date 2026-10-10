import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.HeatSmoothingCoefficient
import OAI.Geometry.WeakHessian.Sobolev.LipschitzBochnerIntegral
import OAI.Geometry.WeakHessian.Calculus.InverseSqrtIntegral

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile146
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [CompleteSpace X] in
lemma RCD.cheegerHeat_integral_bounded_lipschitz {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) (u : Lp ℝ 2 m)
    {B : ℝ} (hB : 0 ≤ B) (hu : ∀ᵐ x ∂m,|u x| ≤ B) {b : ℝ} (hb : 0 < b) :
    ∃ g : X → ℝ,LipschitzWith (Real.toNNReal (2*B*Real.exp (|K| *b)*Real.sqrt b)) g ∧
      g =ᵐ[m] ((∫ s in (0:ℝ)..b,cheegerHeat h s u) : Lp ℝ 2 m) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  let : IsUnifLocDoublingMeasure m := hrcd.1.uniform_local_doubling hN hfull hfin
  let cs (s : ℝ) := Real.toNNReal (B*Real.exp (|K| *b)/Real.sqrt s)
  have hcs (s : ℝ) : (cs s:ℝ) = (B*Real.exp (|K| *b))*(Real.sqrt s)⁻¹ := by
    rw [show (cs s:ℝ)=↑(Real.toNNReal (B*Real.exp (|K| *b)/Real.sqrt s)) from rfl,
      Real.coe_toNNReal _ (by positivity),div_eq_mul_inv]
  have hci : Integrable (fun s => (cs s:ℝ)) (volume.restrict (Ioc 0 b)) := by
    simp_rw [hcs]
    exact (integrableOn_inv_sqrt hb.le).const_mul _
  have hui : Integrable (fun s => cheegerHeat h s u) (volume.restrict (Ioc 0 b)) :=
    ((cheegerHeat_continuousOn hfin h u).mono (by rw [uIcc_of_le hb.le]; exact Icc_subset_Ici_self)).intervalIntegrable.1
  have hLip : ∀ᵐ s ∂volume.restrict (Ioc (0:ℝ) b),∃ g : X → ℝ,LipschitzWith (cs s) g ∧ g =ᵐ[m] cheegerHeat h s u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    obtain ⟨g,hg,he⟩ := hrcd.cheegerHeat_bounded_lipschitz hN hfull hfin h o u hB hu hs.1
    refine ⟨g,hg.weaken ?_,he⟩
    apply Real.toNNReal_mono
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 (abs_nonneg K))) hB) (Real.sqrt_nonneg _)
  obtain ⟨g,hg,he⟩ := exists_lipschitz_integral hfull hfin hui hci hLip
  have hi : (∫ s in Ioc (0:ℝ) b,(cs s:ℝ)) = 2*B*Real.exp (|K| *b)*Real.sqrt b := by
    simp_rw [hcs]
    rw [integral_const_mul,integral_inv_sqrt hb.le]
    ring
  rw [hi] at hg
  refine ⟨g,hg,?_⟩
  rwa [intervalIntegral.integral_of_le hb.le]
end WeakHessian

end
end InlinedFile146

end OAI

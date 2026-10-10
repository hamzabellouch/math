import Mathlib
import OAI.Analysis.CoulombRadii.Packets.PacketDensity
import OAI.Analysis.CoulombRadii.FieldAnalysis.MeridianMap

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
namespace Coulomb

lemma schwartz_square_integrable (g : 𝓢(Space,ℝ)) : Integrable (fun x : Space => g x^2) := by
  exact (g.memLp 2 volume).integrable_sq

lemma window_shift_integrable (g : 𝓢(Space,ℝ)) (a : Space) :
    Integrable (fun x : Space => g (x-a)^2) := (schwartz_square_integrable g).comp_sub_right a

lemma window_shift_coulomb_integral (g : 𝓢(Space,ℝ)) (a x : Space) :
    (∫ y, coulombKernel (x-y)*g (y-a)^2) = ∫ y, coulombKernel ((x-a)-y)*g y^2 := by
  rw [← integral_sub_right_eq_self (fun y => coulombKernel ((x-a)-y)*g y^2) a]
  congr 1
  funext y
  congr 2
  abel

lemma window_coulomb_le (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hrad : ∀ y, g y = g (EuclideanSpace.single 0 ‖y‖)) {x : Space} (hx : x ≠ 0) :
    (∫ y : Space, coulombKernel (x-y)*g y^2) ≤ coulombKernel x := by
  simpa only [hg,mul_one] using radial_coulomb_integral_le (schwartz_square_integrable g)
    (g.continuous.measurable.pow_const 2) (fun y => sq_nonneg (g y)) (schwartz_square_le g)
    (fun y => congrArg (fun t : ℝ => t^2) (hrad y)) hx

lemma window_shape_pair_le (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hrad : ∀ y, g y = g (EuclideanSpace.single 0 ‖y‖)) {a c : Space} (hac : a ≠ c) :
    (∫ xy : Space × Space, g (xy.1-a)^2*g (xy.2-c)^2*coulombKernel (xy.1-xy.2)) ≤
      coulombKernel (a-c) := by
  have hi := window_shift_integrable g
  have hm (v : Space) : Measurable (fun x => g (x-v)^2) :=
    (g.continuous.measurable.comp (measurable_id.sub measurable_const)).pow_const 2
  have hbnd (v x : Space) : ‖g (x-v)^2‖ ≤ (SchwartzMap.seminorm ℝ 0 0 g)^2 := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact schwartz_square_le g _
  have hpair := coulomb_pair_integrable (hi a) (hm a) (hi c) (hm c) (hbnd c)
  change (∫ xy : Space × Space, g (xy.1-a)^2*g (xy.2-c)^2*coulombKernel (xy.1-xy.2) ∂volume.prod volume) ≤ _
  rw [integral_prod _ hpair]
  have hip : Integrable (fun x => g (x-a)^2*(∫ y, coulombKernel ((x-c)-y)*g y^2)) := by
    apply hpair.integral_prod_left.congr
    filter_upwards [] with x
    rw [← window_shift_coulomb_integral g c x,← integral_const_mul]
    congr 1
    funext y
    ring
  have hik : Integrable (fun x => g (x-a)^2*coulombKernel (x-c)) := by
    have H := coulomb_convolution_integrable (hi a) (hm a) (fun y => sq_nonneg (g (y-a)))
      (fun y => schwartz_square_le g (y-a)) (by norm_num : (0:ℝ)<1) c
    apply H.congr
    filter_upwards [] with x
    rw [coulombKernel_sub_comm c x]
    ring
  calc
    _ = ∫ x, g (x-a)^2*(∫ y, coulombKernel ((x-c)-y)*g y^2) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← window_shift_coulomb_integral g c x,← integral_const_mul]
      congr 1
      funext y
      ring
    _ ≤ ∫ x, g (x-a)^2*coulombKernel (x-c) := by
      apply integral_mono_ae hip hik
      have hc : ∀ᵐ x : Space, x ≠ c := by rw [ae_iff]; simp
      filter_upwards [hc] with x hx
      exact mul_le_mul_of_nonneg_left (window_coulomb_le g hg hrad (sub_ne_zero.mpr hx)) (sq_nonneg _)
    _ = ∫ x, coulombKernel ((c-a)-x)*g x^2 := by
      rw [← window_shift_coulomb_integral]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [coulombKernel_sub_comm c x]
      ring
    _ ≤ coulombKernel (c-a) := window_coulomb_le g hg hrad (sub_ne_zero.mpr hac.symm)
    _ = _ := coulombKernel_sub_comm c a
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise

end

end OAI

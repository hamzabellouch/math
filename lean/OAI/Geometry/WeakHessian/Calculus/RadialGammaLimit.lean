import Mathlib
import OAI.Geometry.WeakHessian.Measure.RadialCutoffLp
import OAI.Geometry.WeakHessian.LocalBounds.GraphReuse

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile175
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma radialCutoff_gamma_toLp_tendsto_zero (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) (o : X) {q : X → ℝ} (hq : Sobolev m q) :
    Tendsto (fun n => (memLp_gamma_of_lipschitz hfin hpar (radialCutoff_lipschitz o n) hq).toLp
      (gamma m (radialCutoff o n) q)) atTop (𝓝 0) := by
  apply squeeze_zero_norm
  · intro n
    simpa only [NNReal.coe_inv,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one,one_div] using
      norm_gamma_toLp_le hfin hpar (radialCutoff_lipschitz o n) hq
  · simpa only [one_div,zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const ‖hq.2.2.toLp (weakGradient m q)‖

lemma integral_gamma_radialCutoff_tendsto (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) (o : X) {ξ q b : X → ℝ}
    (hξ : LocalSobolev m ξ) (hq : Sobolev m q)
    (hi : Integrable (fun x => b x*gamma m ξ q x) m)
    (hbξ : MemLp (fun x => b x*ξ x) 2 m) :
    Tendsto (fun n => ∫ x,b x*gamma m (fun y => ξ y*radialCutoff o n y) q x ∂m)
      atTop (𝓝 (∫ x,b x*gamma m ξ q x ∂m)) := by
  have hcB (n : ℕ) : ∀ᵐ x ∂m, |radialCutoff o n x| ≤ 1 := ae_of_all _ fun x => by
    rw [abs_of_nonneg (radialCutoff_nonneg o n x)]; exact radialCutoff_le_one o n x
  have hDcB (n : ℕ) : ∀ᵐ x ∂m, |weakGradient m (radialCutoff o n) x| ≤ ((n:ℝ)+1)⁻¹ := by
    filter_upwards [weakGradient_nonneg (m := m) (radialCutoff o n),
      weakGradient_le_lipschitz hfin (radialCutoff_lipschitz o n)] with x hn hb
    rwa [abs_of_nonneg hn]
  have hγ (n : ℕ) := memLp_gamma_of_lipschitz hfin hpar (radialCutoff_lipschitz o n) hq
  have he (n : ℕ) : (∫ x,b x*gamma m (fun y => ξ y*radialCutoff o n y) q x ∂m) =
      (∫ x,(b x*ξ x)*gamma m (radialCutoff o n) q x ∂m)+
      (∫ x,(b x*gamma m ξ q x)*radialCutoff o n x ∂m) := by
    have hi0 : Integrable (fun x => (b x*ξ x)*gamma m (radialCutoff o n) q x) m :=
      hbξ.integrable_mul (hγ n)
    rw [← integral_add hi0
      (hi.mul_bdd (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable
        (by simpa only [Real.norm_eq_abs] using hcB n))]
    apply integral_congr_ae
    filter_upwards [gamma_mul_left hfin hpar hξ
      (localSobolev_of_lipschitz hfin (radialCutoff_lipschitz o n)) hq.2.1 (hcB n) (hDcB n)] with x hx
    rw [hx]; ring
  have ht : Tendsto (fun n => ∫ x,(b x*ξ x)*gamma m (radialCutoff o n) q x ∂m) atTop (𝓝 0) := by
    simpa only [integral_mul_eq_inner hbξ (hγ _),inner_zero_left] using
      (radialCutoff_gamma_toLp_tendsto_zero hfin hpar o hq).inner
        (tendsto_const_nhds (x := hbξ.toLp _))
  simpa only [he,zero_add] using ht.add (integral_radialCutoff_tendsto o hi)
end WeakHessian

end
end InlinedFile175

end OAI

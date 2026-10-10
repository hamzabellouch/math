import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.GlobalCheegerEnergyReal
import OAI.Geometry.WeakHessian.HeatFlow.HeatEnergyContinuity

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile106
noncomputable section
namespace WeakHessianFunctional
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma ClosedQuadraticEnergy.form_tendsto_of_energy_sub {Q : E → ℝ≥0∞}
    (hQ : ClosedQuadraticEnergy Q) {ι : Type*} {l : Filter ι}
    {f : ι → hQ.domain} {u : hQ.domain} (q : hQ.domain)
    (he : Tendsto (fun i => hQ.realEnergy (f i-u)) l (𝓝 0)) :
    Tendsto (fun i => hQ.form (f i) q) l (𝓝 (hQ.form u q)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hh : Tendsto (fun i => hQ.realEnergy (f i-u)*hQ.realEnergy q) l (𝓝 0) := by
    simpa using he.mul_const (hQ.realEnergy q)
  filter_upwards [hh.eventually_lt_const (sq_pos_of_pos hε)] with i hi
  have hcs := hQ.realEnergy_quadratic.polar_cauchySchwarz (f i-u) q
  change (hQ.form (f i-u) q)^2 ≤ _ at hcs
  rw [map_sub,LinearMap.sub_apply] at hcs
  rw [Real.dist_eq,abs_lt]
  constructor <;> nlinarith
end WeakHessianFunctional

namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
omit [CompleteSpace X] in
lemma CurvatureDimension.cheegerHeat_integral_gamma_zero {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) {u q : Lp ℝ 2 m}
    (hu : Sobolev m (u : X → ℝ)) (hq : Sobolev m (q : X → ℝ)) :
    Tendsto (fun t => ∫ x,gamma m (cheegerHeat h t u) q x ∂m)
      (𝓝[>] 0) (𝓝 (∫ x,gamma m (u : X → ℝ) q x ∂m)) := by
  let Q := cheeger_closedQuadraticEnergy h
  have hue : cheegerEnergy m (u : X → ℝ) < ∞ := (hcd.global_sobolev_iff_cheeger_lt_top hfin o (Lp.memLp u)).mp hu
  have hqe : cheegerEnergy m (q : X → ℝ) < ∞ := (hcd.global_sobolev_iff_cheeger_lt_top hfin o (Lp.memLp q)).mp hq
  let f (t : ℝ) : Q.domain := ⟨cheegerHeat h (max t 0) u,(cheegerHeat_energy_le h (le_max_right _ _) u).trans_lt hue⟩
  have hE : Tendsto (fun t => Q.realEnergy (f t-⟨u,hue⟩)) (𝓝[>] 0) (𝓝 0) := by
    have HH := (cheegerHeat_energy_sub_zero hfin h hue).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    apply HH.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    change (cheegerEnergy m (cheegerHeat h t u-u : Lp ℝ 2 m)).toReal = (cheegerEnergy m (cheegerHeat h (max t 0) u-u : Lp ℝ 2 m)).toReal
    rw [max_eq_left ht.le]
  have HH := (Q.form_tendsto_of_energy_sub ⟨q,hqe⟩ hE).const_mul 2
  rw [hcd.global_integral_gamma_form hfin o h ⟨u,hue⟩ ⟨q,hqe⟩]
  apply HH.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  rw [hcd.global_integral_gamma_form hfin o h ⟨cheegerHeat h t u,(cheegerHeat_energy_le h ht.le u).trans_lt hue⟩ ⟨q,hqe⟩]
  have hf : f t = ⟨cheegerHeat h t u,(cheegerHeat_energy_le h ht.le u).trans_lt hue⟩ := by
    apply Subtype.ext
    simp only [f,max_eq_left ht.le]
  rw [hf]

end WeakHessian

end
end InlinedFile106

end OAI

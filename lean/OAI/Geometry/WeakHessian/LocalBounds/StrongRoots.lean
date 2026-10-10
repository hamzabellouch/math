import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.GlobalCheegerEnergyReal
import OAI.Geometry.WeakHessian.Calculus.NormLpSqIntegral
import OAI.Geometry.WeakHessian.Calculus.FormLimits

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile14
noncomputable section
namespace WeakHessianFunctional
open Set Filter
open scoped Topology ENNReal NNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Q : E → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)
omit [CompleteSpace E] in
lemma ClosedQuadraticEnergy.energy_tendsto_of_upper_bound
    {ι : Type*} {l : Filter ι} (us : ι → hQ.domain) (u : hQ.domain)
    (hu : Tendsto (fun i => (us i:E)) l (𝓝 (u:E)))
    (bs : ι → ℝ) (hb : ∀ i, hQ.realEnergy (us i) ≤ bs i)
    (hbs : Tendsto bs l (𝓝 (hQ.realEnergy u))) :
    Tendsto (fun i => hQ.realEnergy (us i)) l (𝓝 (hQ.realEnergy u)) := by
  have he (v : hQ.domain) : ENNReal.ofReal (hQ.realEnergy v) = Q v :=
    ENNReal.ofReal_toReal v.property.ne
  have hbs' : Tendsto (fun i => ENNReal.ofReal (bs i)) l (𝓝 (Q u)) := by
    rw [← he u]
    exact ENNReal.continuous_ofReal.tendsto _ |>.comp hbs
  have hQlim : Tendsto (fun i => Q (us i)) l (𝓝 (Q u)) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact hu (hQ.lowerSemicontinuous u a ha)
    · intro b hb'
      filter_upwards [hbs'.eventually_lt_const hb'] with i hi
      rw [← he (us i)]
      exact (ENNReal.ofReal_le_ofReal (hb i)).trans_lt hi
  exact ENNReal.continuousAt_toReal u.property.ne |>.tendsto.comp hQlim
end WeakHessianFunctional

namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X}

lemma CurvatureDimension.strong_root_approximation {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m)
    (hq : QuadraticCheegerEnergy m) (o : X)
    {w : X → ℝ} (hw : Sobolev m w)
    (fs Ds : ℕ → X → ℝ) (hfs : ∀ n, MemLp (fs n) 2 m) (hDs : ∀ n, MemLp (Ds n) 2 m)
    (hUG : ∀ n, IsLocalWeakUpperGradient m (fs n) (Ds n))
    (hfT : Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 (hw.1.toLp w)))
    (hDT : Tendsto (fun n => (hDs n).toLp (Ds n)) atTop
      (𝓝 (hw.2.2.toLp (weakGradient m w)))) :
    ∃ hs : ∀ n, Sobolev m (fun x => fs n x-w x),
      Tendsto (fun n => ‖(hs n).2.2.toLp (weakGradient m (fun x => fs n x-w x))‖)
        atTop (𝓝 0) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin (Metric.ball x 1) Metric.isBounded_ball⟩⟩
  let hS (n : ℕ) := Sobolev.of_upperGradient hfin (hfs n) (hUG n) (hDs n)
  let Q := cheeger_closedQuadraticEnergy hq
  let u : Q.domain := ⟨hw.1.toLp w,by
    change cheegerEnergy m (hw.1.toLp w : X → ℝ) < ∞
    rw [cheegerEnergy_congr_ae hw.1.coeFn_toLp]
    exact (hcd.global_sobolev_iff_cheeger_lt_top hfin o hw.1).mp hw⟩
  let us (n : ℕ) : Q.domain := ⟨(hfs n).toLp (fs n),by
    change cheegerEnergy m ((hfs n).toLp (fs n) : X → ℝ) < ∞
    rw [cheegerEnergy_congr_ae (hfs n).coeFn_toLp]
    exact (hcd.global_sobolev_iff_cheeger_lt_top hfin o (hfs n)).mp (hS n)⟩
  have eu : Q.realEnergy u = ‖hw.2.2.toLp (weakGradient m w)‖^2/2 := by
    change (cheegerEnergy m (hw.1.toLp w : X → ℝ)).toReal = _
    rw [cheegerEnergy_congr_ae hw.1.coeFn_toLp,hcd.global_cheegerEnergy_toReal hfin o hq hw,
      norm_toLp_sq_eq_integral hw.2.2]
  let bs (n : ℕ) := ‖(hDs n).toLp (Ds n)‖^2/2
  have hbs : Tendsto bs atTop (𝓝 (Q.realEnergy u)) := by
    rw [eu]
    exact hDT.norm.pow 2 |>.div_const 2
  have hb (n : ℕ) : Q.realEnergy (us n) ≤ bs n := by
    change (cheegerEnergy m ((hfs n).toLp (fs n) : X → ℝ)).toReal ≤ _
    rw [cheegerEnergy_congr_ae (hfs n).coeFn_toLp,hcd.global_cheegerEnergy_toReal hfin o hq (hS n)]
    dsimp [bs]
    rw [norm_toLp_sq_eq_integral (hDs n)]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply integral_mono_ae (hS n).2.2.integrable_sq (hDs n).integrable_sq
    filter_upwards [(weakGradient_isMinimal (hS n).2.1.2).2 _ (hUG n),
      weakGradient_nonneg (m := m) (fs n)] with x hx hn
    nlinarith
  obtain ⟨M,hM,hMb⟩ := (Metric.isBounded_range_of_tendsto bs hbs).exists_pos_norm_le
  have hbM (n : ℕ) : Q.realEnergy (us n) ≤ M :=
    (hb n).trans ((le_abs_self _).trans (hMb _ (mem_range_self n)))
  have hE := Q.energy_tendsto_of_upper_bound us u hfT bs hb hbs
  have hsub := Q.form_energy_sub_tendsto (cheeger_domain_dense hq) us u hfT hM.le hbM hE
  let hs (n : ℕ) := (hS n).sub hfin hw
  refine ⟨hs,?_⟩
  have he (n : ℕ) : ‖(hs n).2.2.toLp (weakGradient m (fun x => fs n x-w x))‖^2 =
      2*Q.realEnergy (us n-u) := by
    rw [norm_toLp_sq_eq_integral (hs n).2.2]
    have hae : ((us n-u : Q.domain):Lp ℝ 2 m) = (hs n).1.toLp (fun x => fs n x-w x) := by
      exact (MemLp.toLp_sub (hfs n) hw.1).symm
    change _ = 2*(cheegerEnergy m (((us n-u : Q.domain):Lp ℝ 2 m) : X → ℝ)).toReal
    rw [hae,cheegerEnergy_congr_ae (hs n).1.coeFn_toLp,hcd.global_cheegerEnergy_toReal hfin o hq (hs n)]
    ring
  have H : Tendsto (fun n => ‖(hs n).2.2.toLp (weakGradient m (fun x => fs n x-w x))‖^2)
      atTop (𝓝 0) := by simpa only [he,mul_zero] using hsub.const_mul 2
  simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using H.sqrt
end WeakHessian

end
end InlinedFile14

end OAI

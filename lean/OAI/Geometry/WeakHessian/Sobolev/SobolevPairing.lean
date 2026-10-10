import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.GlobalCheegerEnergyReal
import OAI.Geometry.WeakHessian.Calculus.NormLpSqIntegral
import OAI.Geometry.WeakHessian.Calculus.FormLimits

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile18
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X}

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X]
  [TopologicalSpace.SeparableSpace X] [ProperSpace X] in
lemma toLp_tendsto_of_domination {fs : ℕ → X → ℝ} {f D : X → ℝ}
    (hfs : ∀ n, MemLp (fs n) 2 m) (hf : MemLp f 2 m) (hD : MemLp D 2 m)
    (hb : ∀ n, ∀ᵐ x ∂m, ‖fs n x‖ ≤ ‖D x‖)
    (hT : ∀ᵐ x ∂m, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 (hf.toLp f)) := by
  have hi : UnifIntegrable fs 2 m := by
    apply unifIntegrable_iff'.mpr
    intro ε hε
    obtain ⟨δ,hδ,hd⟩ := hD.eLpNorm_indicator_le (by norm_num) (by norm_num) hε
    refine ⟨δ,hδ,fun n s hs hms => ?_⟩
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict hs]
    apply le_trans (eLpNorm_mono_ae ((hfs n).aestronglyMeasurable.indicator hs) ?_) (hd s hs hms)
    filter_upwards [hb n] with x hx
    by_cases h : x ∈ s
    · simpa only [indicator_of_mem h] using hx
    · simp only [indicator_of_notMem h,le_refl]
  have ht : UnifTight fs 2 m := by
    intro ε hε
    obtain ⟨s,hsm,hs,hd⟩ :=
      (unifTight_const (ι := ℕ) (by norm_num) hD).exists_measurableSet_indicator hε.ne'
    refine ⟨s,hs.ne,fun n => ?_⟩
    apply le_trans (eLpNorm_mono_ae ((hfs n).aestronglyMeasurable.indicator hsm.compl) ?_) (hd n)
    filter_upwards [hb n] with x hx
    by_cases h : x ∈ sᶜ
    · simpa only [indicator_of_mem h] using hx
    · simp only [indicator_of_notMem h,le_refl]
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fs hfs f hf).mpr
    (tendsto_Lp_of_tendsto_ae (by norm_num : (1:ℝ≥0∞) ≤ 2)
      (by norm_num : (2:ℝ≥0∞) ≠ ∞) (fun n => (hfs n).aestronglyMeasurable) hf hi ht hT)

omit [CompleteSpace X] in
lemma CurvatureDimension.integral_gamma_tendsto {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m)
    (hq : QuadraticCheegerEnergy m) (o : X)
    {fs : ℕ → X → ℝ} {f g : X → ℝ}
    (hfs : ∀ n, Sobolev m (fs n)) (hf : Sobolev m f) (hg : Sobolev m g)
    (hT : Tendsto (fun n => (hfs n).1.toLp (fs n)) atTop (𝓝 (hf.1.toLp f)))
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ n, ‖(hfs n).2.2.toLp (weakGradient m (fs n))‖ ≤ M) :
    Tendsto (fun n => ∫ x,gamma m (fs n) g x ∂m) atTop (𝓝 (∫ x,gamma m f g x ∂m)) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin (Metric.ball x 1) Metric.isBounded_ball⟩⟩
  let Q := cheeger_closedQuadraticEnergy hq
  let mk (v : X → ℝ) (hv : Sobolev m v) : Q.domain := ⟨hv.1.toLp v,by
    change cheegerEnergy m (hv.1.toLp v : X → ℝ) < ∞
    rw [cheegerEnergy_congr_ae hv.1.coeFn_toLp]
    exact (hcd.global_sobolev_iff_cheeger_lt_top hfin o hv.1).mp hv⟩
  have he (v : X → ℝ) (hv : Sobolev m v) :
      Q.realEnergy (mk v hv) = ‖hv.2.2.toLp (weakGradient m v)‖^2/2 := by
    change (cheegerEnergy m (hv.1.toLp v : X → ℝ)).toReal = _
    rw [cheegerEnergy_congr_ae hv.1.coeFn_toLp,hcd.global_cheegerEnergy_toReal hfin o hq hv,
      norm_toLp_sq_eq_integral hv.2.2]
  have hbE (n : ℕ) : Q.realEnergy (mk (fs n) (hfs n)) ≤ M^2/2 := by
    rw [he (fs n) (hfs n)]
    gcongr
    exact hb n
  have hpair (v : X → ℝ) (hv : Sobolev m v) :
      (∫ x,gamma m v g x ∂m) = 2*Q.form (mk v hv) (mk g hg) := by
    rw [← hcd.global_integral_gamma_form hfin o hq]
    apply integral_congr_ae
    exact gamma_congr_ae hv.1.coeFn_toLp.symm hg.1.coeFn_toLp.symm
  simp_rw [hpair f hf,hpair _ (hfs _)]
  exact (Q.form_tendsto_of_bounded_energy (cheeger_domain_dense hq)
    (fun n => mk (fs n) (hfs n)) (mk f hf) (mk g hg) hT
    (div_nonneg (pow_nonneg hM 2) (by norm_num) : 0 ≤ M^2/2) hbE).const_mul 2
end WeakHessian

end
end InlinedFile18

end OAI

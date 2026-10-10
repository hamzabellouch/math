import Mathlib
import OAI.Analysis.BrownMeasure.MercatorCalculus
import OAI.Analysis.BrownMeasure.TraceDerivative

namespace OAI

noncomputable section
open Filter
open scoped Topology Ring
namespace BrownLog
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A] [Nontrivial A]
  [StarRing A] [StarModule ℝ A] [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

omit [Nontrivial A] [StarModule ℝ A] in
lemma exists_smul_close_one {b : A} (hb : IsSelfAdjoint b)
    (hp : ∀ y∈spectrum ℝ b,0<y) : ∃ c : ℝ,0<c ∧ ‖1-c•b‖<1 := by
  let c : ℝ := (‖b‖+1)⁻¹
  have hc : 0<c := inv_pos.mpr (by positivity)
  refine ⟨c,hc,?_⟩
  have he : cfc (fun y:ℝ=>1-c*y) b=1-c•b := by
    rw [cfc_sub _ _ b (by fun_prop) (by fun_prop),cfc_const 1 b hb]
    change (algebraMap ℝ A) 1-cfc (fun y:ℝ=>c•y) b=_
    rw [cfc_smul_id c b hb,map_one]
  rw [← he]
  apply norm_cfc_lt zero_lt_one
  intro y hy
  have hy0 := hp y hy
  have hyb : y≤‖b‖ := (le_abs_self y).trans (spectrum.norm_le_norm_of_mem hy)
  have hcy : c*y<1 := by
    dsimp [c]
    rw [inv_mul_lt_iff₀ (by positivity)]
    linarith
  rw [Real.norm_eq_abs,abs_lt]
  constructor <;> nlinarith [mul_pos hc hy0]

variable (τ : A →L[ℝ] ℝ) (hτ : ∀ a b,τ (a*b)=τ (b*a))
include hτ in
lemma trace_log_hasDerivAt {b d : ℝ → A} {x : ℝ}
    (hb : ∀t,IsSelfAdjoint (b t)) (hp : ∀t y,y∈spectrum ℝ (b t) → 0<y)
    (hf : ∀t,HasDerivAt b (d t) t) (hd : ContinuousAt d x) :
    HasDerivAt (fun t=>τ (CFC.log (b t))) (τ ((b x)⁻¹ʳ*d x)) x := by
  obtain ⟨c,hc,hcn⟩ := exists_smul_close_one (hb x) (hp x)
  let f : ℝ → A := fun t=>1-c•b t
  let df : ℝ → A := fun t=>-c•d t
  have hdf (t : ℝ) : HasDerivAt f (df t) t := by
    simpa [f,df,neg_smul] using ((hf t).fun_const_smul c).const_sub (1:A)
  let r : ℝ := (‖f x‖+1)/2
  let D : ℝ := ‖df x‖+1
  have hr0 : 0≤r := by dsimp [r]; positivity
  have hr1 : r<1 := by change (‖1-c•b x‖+1)/2<1; linarith
  have hDr : 0≤D := by dsimp [D]; positivity
  have hn : ∀ᶠ t in 𝓝 x,‖f t‖<r ∧ ‖df t‖<D := by
    apply Filter.Eventually.and
    · apply (hdf x).continuousAt.norm.eventually_lt continuousAt_const
      change ‖1-c•b x‖<(‖1-c•b x‖+1)/2
      linarith
    · apply (hd.const_smul (-c)).norm.eventually_lt continuousAt_const
      exact lt_add_one _
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hn
  have H := trace_mercator_deriv_of_bounds τ hτ (s:=Metric.ball x ε)
    Metric.isOpen_ball (convex_ball x ε).isPreconnected (Metric.mem_ball_self hε)
    hr0 hr1 hDr (fun t _=>hdf t) (fun t ht=>(hball ht).1.le) (fun t ht=>(hball ht).2.le)
  have he (t : ℝ) (ht : t∈Metric.ball x ε) :
      τ (mercator (f t))=τ (algebraMap ℝ A (Real.log c))+τ (CFC.log (b t)) := by
    rw [mercator_eq_cfc_log_one_sub ((IsSelfAdjoint.one A).sub ((isSelfAdjoint_iff.mpr rfl).smul (hb t))) ((hball ht).1.trans hr1)]
    have he : 1-f t=c•b t := by dsimp [f]; abel
    rw [he,CFC.log_smul (b t) (fun y hy=>(hp t y hy).ne') hc.ne' (hb t),map_add]
  have hi : IsUnit (c•b x) := by
    have hu : IsUnit (b x) := spectrum.isUnit_of_zero_notMem ℝ (fun h=>(hp x 0 h).false)
    rw [Algebra.smul_def]
    exact ((isUnit_iff_ne_zero.mpr hc.ne').map (algebraMap ℝ A)).mul hu
  have hv : (1-f x)⁻¹ʳ*df x= -((b x)⁻¹ʳ*d x) := by
    have he : 1-f x=c•b x := by dsimp [f]; abel
    rw [he,Ring.inverse_mul_eq_iff_eq_mul _ _ _ hi]
    dsimp [df]
    simp only [mul_neg,smul_mul_assoc]
    rw [Ring.mul_inverse_cancel_left _ _ (spectrum.isUnit_of_zero_notMem ℝ (fun h=>(hp x 0 h).false))]
    exact neg_smul c (d x)
  rw [hv,map_neg,neg_neg] at H
  have H' := H.sub_const (τ (algebraMap ℝ A (Real.log c)))
  apply H'.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds x hε] with t ht
  rw [he t ht]
  ring
end BrownLog
end

end OAI

import Mathlib
import OAI.Geometry.CAT0Fillings.Charts.Differentiability
import OAI.Geometry.CAT0Fillings.Differentiation.Density

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Filter MeasureTheory Set Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X]
omit [MeasurableSpace E] [BorelSpace E] in
lemma tendsto_scaled_metric_differential {s : Set E} {x v : E}
    {r : E → ℝ} {p : Seminorm ℝ E}
    (hr : (fun y => r y-p (y-x)) =o[𝓝[s] x] (fun y => y-x))
    {c : ℕ → ℝ} {d : ℕ → E} (hd : ∀ᶠ j in atTop, x+d j ∈ s)
    (hd0 : Tendsto d atTop (𝓝 0))
    (hcd : Tendsto (fun j => c j • d j) atTop (𝓝 v)) :
    Tendsto (fun j => ‖c j‖*r (x+d j)) atTop (𝓝 (p v)) := by
  have ht : Tendsto (fun j => x+d j) atTop (𝓝[s] x) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa using tendsto_const_nhds.add hd0,hd⟩
  have hsmall := (hr.comp_tendsto ht).norm_right.mul_isBigO
    (Asymptotics.isBigO_refl (fun j => ‖c j‖) atTop)
  have hnorm : Tendsto (fun j => ‖(x+d j)-x‖*‖c j‖) atTop (𝓝 ‖v‖) := by
    simpa only [norm_smul,add_sub_cancel_left,mul_comm] using hcd.norm
  have hzero := hsmall.tendsto_zero_of_tendsto hnorm
  have hp := (seminorm_continuous_finiteDimensional p).tendsto v |>.comp hcd
  convert hzero.add hp using 1
  · ext j
    simp only [Function.comp_apply,add_sub_cancel_left,map_smul_eq_mul]
    ring
  · simp

theorem radial_scalar_derivative_sq_le
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (seg : X → X → ℝ → X)
    (hcomp : ∀ o x y a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o y b)^2 ≤ (a*dist o x-b*dist o y)^2+
        a*b*(dist x y^2-(dist o x-dist o y)^2))
    {s : Set E} {x : E} (hxs : x ∈ s)
    (hx : Tendsto (fun t => μ (s ∩ closedBall x t) / μ (closedBall x t))
      (𝓝[>] 0) (𝓝 1))
    (f : E → X) (o : X) (p : Seminorm ℝ E)
    (hp : (fun y => dist (f y) (f x)-p (y-x)) =o[𝓝[s] x] (fun y => y-x))
    {lam F : E → ℝ} {α β ℓ : E →L[ℝ] ℝ}
    (hlam : ∀ y ∈ s, lam y ∈ Icc (0:ℝ) 1)
    (hα : HasFDerivWithinAt (fun y => dist o (f y)) α s x)
    (hβ : HasFDerivWithinAt lam β s x)
    (hℓ : HasFDerivWithinAt F ℓ s x)
    {u : X → ℝ} (hu : LipschitzWith 1 u)
    (hF : ∀ y ∈ s, F y = u (seg o (f y) (lam y))) (v : E) :
    (ℓ v)^2 ≤ (lam x*α v+dist o (f x)*β v)^2+
      (lam x)^2*((p v)^2-(α v)^2) := by
  have hv : v ∈ tangentConeAt ℝ s x := by
    rw [tangentConeAt_eq_univ_of_density_one μ s x hx]
    exact mem_univ v
  obtain ⟨c,d,hc,hd,hcd⟩ := mem_tangentConeAt_iff_exists_seq_norm_tendsto_atTop.mp hv
  have hd0 := tangentConeAt.lim_zero atTop hc hcd
  have ht : Tendsto (fun j => x+d j) atTop (𝓝[s] x) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa using tendsto_const_nhds.add hd0,hd⟩
  have hmetric := tendsto_scaled_metric_differential hp hd hd0 hcd
  have hflim : Tendsto (fun j => c j*(F (x+d j)-F x)) atTop (𝓝 (ℓ v)) := by
    simpa only [smul_eq_mul] using hℓ.lim hd0 hd hcd
  have hrlim : Tendsto (fun j => c j*(dist o (f (x+d j))-dist o (f x)))
      atTop (𝓝 (α v)) := by simpa only [smul_eq_mul] using hα.lim hd0 hd hcd
  have hplim : Tendsto (fun j => c j*(lam (x+d j)*dist o (f (x+d j))-lam x*dist o (f x)))
      atTop (𝓝 (lam x*α v+dist o (f x)*β v)) := by
    simpa only [Pi.mul_apply,smul_eq_mul,_root_.add_apply,_root_.smul_apply]
      using (hβ.mul hα).lim hd0 hd hcd
  have hllim := hβ.continuousWithinAt.tendsto.comp ht
  have hrhs := (hplim.pow 2).add
    ((hllim.mul (tendsto_const_nhds (x := lam x))).mul ((hmetric.pow 2).sub (hrlim.pow 2)))
  apply le_of_tendsto_of_tendsto (hflim.pow 2) (by simpa only [←pow_two] using hrhs)
  filter_upwards [hd] with j hj
  have hb : |F (x+d j)-F x| ≤ dist (seg o (f (x+d j)) (lam (x+d j))) (seg o (f x) (lam x)) := by
    simpa only [Real.dist_eq,NNReal.coe_one,one_mul,←hF (x+d j) hj,←hF x hxs]
      using hu.dist_le_mul (seg o (f (x+d j)) (lam (x+d j))) (seg o (f x) (lam x))
  have hb2 := (sq_le_sq₀ (abs_nonneg _) dist_nonneg).2 hb
  rw [sq_abs] at hb2
  have hh := hb2.trans (hcomp o (f (x+d j)) (f x) (lam (x+d j)) (lam x) (hlam _ hj) (hlam _ hxs))
  have hmul := mul_le_mul_of_nonneg_left hh (sq_nonneg (c j))
  convert hmul using 1 <;> simp only [Function.comp_apply,mul_pow,Real.norm_eq_abs,sq_abs]
  ring

end CAT0Fillings

end
end

end OAI

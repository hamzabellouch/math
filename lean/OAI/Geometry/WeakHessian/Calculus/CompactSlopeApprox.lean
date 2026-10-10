import Mathlib
import OAI.Geometry.WeakHessian.Measure.RadialCutoff
import OAI.Geometry.WeakHessian.LocalBounds.BoundedMulLpTendsto
import OAI.Geometry.WeakHessian.Sobolev.UpperGradientNormTendsto

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile95
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X]

omit [MeasurableSpace X] [BorelSpace X] [ProperSpace X] in
lemma localSlope_cutoff_le (o : X) (n : ℕ) {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (x : X) :
    (localSlope (fun y => radialCutoff o n y * f y) x).toReal ≤
      (localSlope f x).toReal + (1/((n:ℝ)+1))*|f x| := by
  have hs := localSlope_product_le (radialCutoff_lipschitz o n) hf x
  have hc := localSlope_le_lipschitz (radialCutoff_lipschitz o n) x
  have hsf := localSlope_le_lipschitz hf x
  have hct : localSlope (radialCutoff o n) x ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top hc
  have hft : localSlope f x ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top hsf
  have H := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hft, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hct⟩) hs
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hft)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hct), ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal (abs_nonneg _),
    abs_of_nonneg (radialCutoff_nonneg o n x)] at H
  have hc' := ENNReal.toReal_mono ENNReal.coe_ne_top hc
  simp only [ENNReal.coe_toReal,NNReal.coe_inv,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] at hc'
  calc
    _ ≤ _ := H
    _ ≤ 1*(localSlope f x).toReal+|f x| * ((n:ℝ)+1)⁻¹ :=
      add_le_add (mul_le_mul_of_nonneg_right (radialCutoff_le_one o n x) ENNReal.toReal_nonneg)
        (mul_le_mul_of_nonneg_left hc' (abs_nonneg _))
    _ = _ := by ring

lemma exists_compact_cutoff_approx (o : X) {f : X → ℝ}
    (hf : GloballyLipschitz f) (hf2 : MemLp f 2 m)
    (hs2 : MemLp (fun x => (localSlope f x).toReal) 2 m) :
    ∃ fs : ℕ → X → ℝ, (∀ n, GloballyLipschitz (fs n)) ∧
      (∀ n,HasCompactSupport (fs n)) ∧ ∃ hfs : ∀ n,MemLp (fs n) 2 m,
      ∃ Ds : ℕ → Lp ℝ 2 m,
      (∀ n,∀ᵐ x ∂m,0 ≤ Ds n x ∧ (localSlope (fs n) x).toReal ≤ Ds n x) ∧
      Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 (hf2.toLp f)) ∧
      Tendsto Ds atTop (𝓝 (hs2.toLp (fun x => (localSlope f x).toReal))) := by
  let fs := fun n x => radialCutoff o n x*f x
  have hLip (n : ℕ) : GloballyLipschitz (fs n) :=
    lipschitz_mul_compact ⟨_,radialCutoff_lipschitz o n⟩ hf (radialCutoff_compact o n)
  have hc (n : ℕ) : HasCompactSupport (fs n) := (radialCutoff_compact o n).mul_right
  have hm (n : ℕ) := (radialCutoff_lipschitz o n).continuous.measurable.aestronglyMeasurable (μ := m)
  have hb (n : ℕ) : ∀ᵐ x ∂m,|radialCutoff o n x| ≤ 1 := ae_of_all _ fun x => by
    rw [abs_of_nonneg (radialCutoff_nonneg o n x)]; exact radialCutoff_le_one o n x
  have hfs (n : ℕ) : MemLp (fs n) 2 m := by
    simpa only [fs,mul_comm] using memLp_mul_bounded hf2 (hm n) (hb n)
  let S := hs2.toLp (fun x => (localSlope f x).toReal)
  let A := hf2.norm.toLp (fun x => ‖f x‖)
  let Ds := fun n : ℕ => S+(1/((n:ℝ)+1)) • A
  have hD (n : ℕ) : ∀ᵐ x ∂m,Ds n x = (localSlope f x).toReal+(1/((n:ℝ)+1))*|f x| := by
    filter_upwards [Lp.coeFn_add S ((1/((n:ℝ)+1)) • A),Lp.coeFn_smul (1/((n:ℝ)+1)) A,
      hs2.coeFn_toLp,hf2.norm.coeFn_toLp] with x h1 h2 h3 h4
    change (S+(1/((n:ℝ)+1)) • A) x = _
    rw [h1]
    change S x+((1/((n:ℝ)+1)) • A) x = _
    rw [h2]
    change S x+(1/((n:ℝ)+1))*A x = _
    rw [h3,h4,Real.norm_eq_abs]
  refine ⟨fs,hLip,hc,hfs,Ds,fun n => ?_,?_,?_⟩
  · filter_upwards [hD n] with x hx
    rw [hx]
    exact ⟨by positivity,localSlope_cutoff_le o n hf.choose_spec x⟩
  · have H := boundedMulLp_tendsto hm hb (ae_of_all _ (radialCutoff_tendsto o)) (hf2.toLp f)
    convert H using 1
    funext n
    apply Lp.ext
    filter_upwards [(hfs n).coeFn_toLp,boundedMulLp_ae (hm n) (hb n) (hf2.toLp f),hf2.coeFn_toLp] with x h1 h2 h3
    calc
      _ = fs n x := h1
      _ = f x*radialCutoff o n x := mul_comm _ _
      _ = _ := by rw [h2,h3]
  · simpa only [Ds,zero_smul,add_zero,S] using (tendsto_const_nhds (x := S)).add
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const A)

lemma exists_compact_strong_slope_majorants (hfinite : FiniteOnBoundedSets m) (o : X)
    {f D : Lp ℝ 2 m} (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D)
    (henergy : cheegerEnergy m (f : X → ℝ) = ENNReal.ofReal (‖D‖^2/2)) :
    ∃ fs : ℕ → X → ℝ, (∀ n, GloballyLipschitz (fs n)) ∧
      (∀ n,HasCompactSupport (fs n)) ∧ ∃ hfs : ∀ n,MemLp (fs n) 2 m,
      ∃ Ds : ℕ → Lp ℝ 2 m,
      (∀ n,∀ᵐ x ∂m,0 ≤ Ds n x ∧ (localSlope (fs n) x).toReal ≤ Ds n x) ∧
      Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 f) ∧
      Tendsto Ds atTop (𝓝 D) := by
  obtain ⟨gs,hg,hg2,hs2,hgt,hst⟩ := exists_lipschitz_strong_slopes hfinite hD henergy
  choose fs hfs hfc hf2 Ds hDs hft hDt using fun n => exists_compact_cutoff_approx o (hg n) (hg2 n) (hs2 n)
  have hex (n : ℕ) : ∃ k : ℕ,
      dist ((hf2 n k).toLp (fs n k)) ((hg2 n).toLp (gs n)) < 1/((n:ℝ)+1) ∧
      dist (Ds n k) ((hs2 n).toLp (fun x => (localSlope (gs n) x).toReal)) < 1/((n:ℝ)+1) := by
    have H1 := (hft n).eventually (Metric.ball_mem_nhds _ (by positivity : 0 < 1/((n:ℝ)+1)))
    have H2 := (hDt n).eventually (Metric.ball_mem_nhds _ (by positivity : 0 < 1/((n:ℝ)+1)))
    exact (H1.and H2).exists
  choose k hk using hex
  refine ⟨fun n => fs n (k n),fun n => hfs n (k n),fun n => hfc n (k n),
    fun n => hf2 n (k n),fun n => Ds n (k n),fun n => hDs n (k n),?_,?_⟩
  · apply tendsto_of_tendsto_of_dist hgt
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => by simpa only [dist_comm] using (hk n).1.le) tendsto_one_div_add_atTop_nhds_zero_nat
  · apply tendsto_of_tendsto_of_dist hst
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => by simpa only [dist_comm] using (hk n).2.le) tendsto_one_div_add_atTop_nhds_zero_nat
end WeakHessian

end
end InlinedFile95

end OAI

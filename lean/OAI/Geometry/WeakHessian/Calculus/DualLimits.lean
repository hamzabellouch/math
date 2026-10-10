import Mathlib
import OAI.Geometry.WeakHessian.Calculus.CompactCost
import OAI.Geometry.WeakHessian.Calculus.PotentialCompactness

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile21
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma lipschitz_integral_tendsto_supported {μ : Measure X} [IsFiniteMeasure μ]
    (o : X) (R : ℝ≥0) (hs : ∀ᵐ x ∂μ, x ∈ Metric.closedBall o R)
    {fs : ℕ → X → ℝ} {f : X → ℝ} {L : ℝ≥0}
    (hfs : ∀ n, LipschitzWith L (fs n)) {B : ℝ} (hb : ∀ n, |fs n o| ≤ B)
    (ht : ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => ∫ x,fs n x ∂μ) atTop (𝓝 (∫ x,f x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => B+(L:ℝ)*R)
    (fun n => (hfs n).continuous.aestronglyMeasurable) (integrable_const _)
  · intro n
    filter_upwards [hs] with x hx
    rw [Real.norm_eq_abs]
    have H : |fs n x| ≤ |fs n o|+|fs n x-fs n o| := by
      simpa only [Real.norm_eq_abs,abs_sub_comm] using norm_le_norm_add_norm_sub (fs n o) (fs n x)
    apply H.trans (add_le_add (hb n) _)
    rw [← Real.dist_eq]
    exact (hfs n).dist_le_mul x o |>.trans (mul_le_mul_of_nonneg_left hx L.coe_nonneg)
  · exact ae_of_all _ ht

lemma squareDensity_varying_pairing_tendsto {m : Measure X}
    {vs : ℕ → X → ℝ} {w : X → ℝ}
    (hvm : ∀ n, Measurable (vs n)) (hwm : Measurable w)
    (hv : ∀ n, MemLp (vs n) 2 m) (hw : MemLp w 2 m)
    (hvp : ∀ n, IsProbabilityMeasure (squareDensityMeasure m (vs n)))
    [IsProbabilityMeasure (squareDensityMeasure m w)]
    (hV : Tendsto (fun n => (hv n).toLp (vs n)) atTop (𝓝 (hw.toLp w)))
    (o : X) (R : ℝ≥0)
    (hvs : ∀ n, ∀ᵐ x ∂squareDensityMeasure m (vs n), x ∈ Metric.closedBall o R)
    (hws : ∀ᵐ x ∂squareDensityMeasure m w, x ∈ Metric.closedBall o R)
    {fs : ℕ → X → ℝ} {f : X → ℝ} {L : ℝ≥0}
    (hfs : ∀ n, LipschitzWith L (fs n)) {B : ℝ} (hb : ∀ n, |fs n o| ≤ B)
    (ht : ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => ∫ x,fs n x ∂squareDensityMeasure m (vs n)) atTop
      (𝓝 (∫ x,f x ∂squareDensityMeasure m w)) := by
  let (n : ℕ) : IsProbabilityMeasure (squareDensityMeasure m (vs n)) := hvp n
  have hTV := squareDensity_L1_tendsto hv hw hV
  have hbound := hTV.const_mul ((L:ℝ)*R)
  simp only [mul_zero] at hbound
  have hdiff : Tendsto (fun n => (∫ x,fs n x ∂squareDensityMeasure m (vs n))-
      (∫ x,fs n x ∂squareDensityMeasure m w)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) _ hbound
    intro n
    exact squareDensity_pairing_bound_supported (hvm n) hwm (hv n) hw (hfs n) o R (hvs n) hws
  have H := hdiff.add (lipschitz_integral_tendsto_supported o R hws hfs hb ht)
  simpa only [zero_add,sub_add_cancel] using H

lemma contact_integral_eq {π : Measure (Curve X)} [IsProbabilityMeasure π]
    (hb : BoundedTracks π) {φ ψ : X → ℝ} {L T : ℝ≥0}
    (hφ : LipschitzWith L φ) (hψ : LipschitzWith T ψ)
    (hc : ∀ᵐ γ ∂π, φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2) :
    (∫ x,φ x ∂interpolation π timeZero)+(∫ y,ψ y ∂interpolation π timeOne) = planEnergy π/2 := by
  have he (f : X → ℝ) (hf : Continuous f) (s : Time) :
      (∫ x,f x ∂interpolation π s) = ∫ γ,f (γ s) ∂π :=
    integral_map (continuous_eval_const s).measurable.aemeasurable hf.aestronglyMeasurable
  rw [he φ hφ.continuous,he ψ hψ.continuous,← integral_add
    (hb.integrable_lipschitz_eval hφ timeZero) (hb.integrable_lipschitz_eval hψ timeOne)]
  rw [integral_congr_ae hc]
  exact integral_div _ _

lemma contact_of_integral_eq {π : Measure (Curve X)} [IsProbabilityMeasure π]
    (hb : BoundedTracks π)
    (hi : Integrable (fun γ : Curve X => dist (γ timeZero) (γ timeOne)^2) π)
    {φ ψ : X → ℝ} {L T : ℝ≥0} (hφ : LipschitzWith L φ) (hψ : LipschitzWith T ψ)
    (hd : ∀ x y,φ x+ψ y ≤ dist x y^2/2)
    (he : (∫ x,φ x ∂interpolation π timeZero)+(∫ y,ψ y ∂interpolation π timeOne) = planEnergy π/2) :
    ∀ᵐ γ ∂π, φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2 := by
  have hmap (f : X → ℝ) (hf : Continuous f) (s : Time) :
      (∫ x,f x ∂interpolation π s) = ∫ γ,f (γ s) ∂π :=
    integral_map (continuous_eval_const s).measurable.aemeasurable hf.aestronglyMeasurable
  rw [hmap φ hφ.continuous,hmap ψ hψ.continuous,← integral_add
    (hb.integrable_lipschitz_eval hφ timeZero) (hb.integrable_lipschitz_eval hψ timeOne),
    show planEnergy π/2 = ∫ γ,dist (γ timeZero) (γ timeOne)^2/2 ∂π from (integral_div _ _).symm] at he
  exact (integral_eq_iff_of_ae_le
    ((hb.integrable_lipschitz_eval hφ timeZero).add (hb.integrable_lipschitz_eval hψ timeOne))
    (hi.div_const 2) (ae_of_all _ fun γ => hd _ _)).mp he

omit [MeasurableSpace X] [BorelSpace X] in
lemma centered_dual_bound {π : Measure (Curve X)} [IsProbabilityMeasure π]
    {φ ψ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) (hψ : LipschitzWith L ψ)
    (o : X) (R : ℝ≥0) (hz : φ o = 0)
    (hd : ∀ x y,φ x+ψ y ≤ dist x y^2/2)
    (hc : ∀ᵐ γ ∂π, φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2)
    (hs : ∀ᵐ γ ∂π, γ timeZero ∈ Metric.closedBall o R ∧ γ timeOne ∈ Metric.closedBall o R) :
    |ψ o| ≤ 2*(L:ℝ)*R := by
  have hu : ψ o ≤ 0 := by simpa [hz] using hd o o
  obtain ⟨γ,hc,hs⟩ := (hc.and hs).exists
  have h1 : φ (γ timeZero) ≤ (L:ℝ)*R := by
    have H := (hφ.dist_le_mul (γ timeZero) o).trans (mul_le_mul_of_nonneg_left hs.1 L.coe_nonneg)
    rw [Real.dist_eq,hz,sub_zero] at H
    exact (le_abs_self _).trans H
  have h2 : ψ (γ timeOne) ≤ ψ o+(L:ℝ)*R := by
    have H := (hψ.dist_le_mul (γ timeOne) o).trans (mul_le_mul_of_nonneg_left hs.2 L.coe_nonneg)
    rw [Real.dist_eq] at H
    linarith [le_abs_self (ψ (γ timeOne)-ψ o)]
  rw [abs_of_nonpos hu]
  nlinarith [sq_nonneg (dist (γ timeZero) (γ timeOne))]

omit [MeasurableSpace X] [BorelSpace X] in
lemma exists_dual_subsequence [ProperSpace X]
    (o : X) {L : ℝ≥0} (fs gs : ℕ → X → ℝ)
    (hf : ∀ n, LipschitzWith L (fs n)) (hg : ∀ n, LipschitzWith L (gs n))
    {B : ℝ} (hB : 0 ≤ B) (hbf : ∀ n, |fs n o| ≤ B) (hbg : ∀ n, |gs n o| ≤ B)
    (hd : ∀ n x y,fs n x+gs n y ≤ dist x y^2/2) :
    ∃ f g : X → ℝ, ∃ s : ℕ → ℕ, StrictMono s ∧
      LipschitzWith L f ∧ LipschitzWith L g ∧
      |f o| ≤ B ∧ |g o| ≤ B ∧
      (∀ x, Tendsto (fun n => fs (s n) x) atTop (𝓝 (f x))) ∧
      (∀ x, Tendsto (fun n => gs (s n) x) atTop (𝓝 (g x))) ∧
      ∀ x y,f x+g y ≤ dist x y^2/2 := by
  obtain ⟨f,s,hs,hfL,hfT,_⟩ := exists_lipschitz_locally_uniform_subsequence o L fs hf hB hbf
  obtain ⟨g,t,ht,hgL,hgT,_⟩ := exists_lipschitz_locally_uniform_subsequence o L (fun n => gs (s n))
    (fun n => hg (s n)) hB (fun n => hbg (s n))
  have hfT' (x : X) := (hfT x).comp ht.tendsto_atTop
  refine ⟨f,g,fun n => s (t n),hs.comp ht,hfL,hgL,?_,?_,hfT',hgT,?_⟩
  · exact le_of_tendsto (hfT' o |>.abs) (Eventually.of_forall fun n => hbf _)
  · exact le_of_tendsto (hgT o |>.abs) (Eventually.of_forall fun n => hbg _)
  · intro x y
    exact le_of_tendsto ((hfT' x).add (hgT y)) (Eventually.of_forall fun n => hd _ x y)
end WeakHessian

end
end InlinedFile21

end OAI

import OAI.Geometry.RCD.Harmonic.WeightedAffineComposition

namespace OAI

/-! # L² continuity of a bounded scalar coefficient times a density -/

open Filter MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def boundedScalarProduct (f g : Lp ℝ 2 μ) {b : ℝ → ℝ} {D : ℝ≥0}
    (hb : LipschitzWith D b) (E : ℝ≥0) (hE : ∀ a, |b a|≤E) : Lp ℝ 2 μ :=
  let hm : MemLp (fun x => b (f x)) ∞ μ :=
    memLp_top_of_bound (hb.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)) E
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hE (f x))
  lpMultiplier μ (hm.toLp _) g

theorem boundedScalarProduct_coe (f g : Lp ℝ 2 μ) {b : ℝ → ℝ} {D : ℝ≥0}
    (hb : LipschitzWith D b) (E : ℝ≥0) (hE : ∀ a, |b a|≤E) :
    boundedScalarProduct μ f g hb E hE =ᵐ[μ] fun x => b (f x)*g x := by
  let hm : MemLp (fun x => b (f x)) ∞ μ :=
    memLp_top_of_bound (hb.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)) E
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hE (f x))
  change lpMultiplier μ (hm.toLp _) g =ᵐ[μ] _
  filter_upwards [lpMultiplier_coe μ (hm.toLp _) g,hm.coeFn_toLp] with x hx hy
  exact hx.trans (by rw [hy])

theorem boundedScalarProduct_sub_norm_le (f f' g g' : Lp ℝ 2 μ)
    {b : ℝ → ℝ} {D : ℝ≥0} (hb : LipschitzWith D b) (E N : ℝ≥0)
    (hE : ∀ a, |b a|≤E) (hN : ∀ᵐ x ∂μ, |g' x|≤N) :
    ‖boundedScalarProduct μ f g hb E hE-boundedScalarProduct μ f' g' hb E hE‖ ≤
      E*‖g-g'‖+(N:ℝ)*D*‖f-f'‖ := by
  let Q := boundedScalarProduct μ f g hb E hE
  let R := boundedScalarProduct μ f g' hb E hE
  let S := boundedScalarProduct μ f' g' hb E hE
  have hQR : ‖Q-R‖≤(E:ℝ)*‖g-g'‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [boundedScalarProduct_coe μ f g hb E hE,
      boundedScalarProduct_coe μ f g' hb E hE,Lp.coeFn_sub Q R,Lp.coeFn_sub g g']
      with x hq hr hd he
    change Q x = _ at hq
    change R x = _ at hr
    rw [hd,he]
    simp only [Pi.sub_apply,hq,hr,←mul_sub,norm_mul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hE _) (abs_nonneg _)
  have hRS : ‖R-S‖≤((N:ℝ)*D)*‖f-f'‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [boundedScalarProduct_coe μ f g' hb E hE,
      boundedScalarProduct_coe μ f' g' hb E hE,Lp.coeFn_sub R S,Lp.coeFn_sub f f',hN]
      with x hr hs hd he hn
    change R x = _ at hr
    change S x = _ at hs
    rw [hd,he]
    simp only [Pi.sub_apply,hr,hs,←sub_mul,norm_mul,Real.norm_eq_abs]
    have hbd := hb.dist_le_mul (f x) (f' x)
    simp only [Real.dist_eq] at hbd
    calc
      _ ≤ ((D:ℝ)*|f x-f' x|)*(N:ℝ) := mul_le_mul hbd hn (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have ht : ‖Q-S‖≤‖Q-R‖+‖R-S‖ := by
    calc
      _ = ‖(Q-R)+(R-S)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  exact ht.trans (add_le_add hQR hRS)

theorem boundedScalarProduct_continuousAt {F G : ℝ → Lp ℝ 2 μ} {t : ℝ}
    {b : ℝ → ℝ} {D : ℝ≥0} (hb : LipschitzWith D b) (E N : ℝ≥0)
    (hE : ∀ a, |b a|≤E) (hN : ∀ᵐ x ∂μ, |G t x|≤N)
    (hF : ContinuousAt F t) (hG : ContinuousAt G t) :
    ContinuousAt (fun s => boundedScalarProduct μ (F s) (G s) hb E hE) t := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun s =>
    boundedScalarProduct_sub_norm_le μ (F s) (F t) (G s) (G t) hb E N hE hN)
  simpa only [sub_self,norm_zero,mul_zero,add_zero] using
    ((hG.tendsto.sub_const (G t)).norm.const_mul (E:ℝ)).add
      ((hF.tendsto.sub_const (F t)).norm.const_mul ((N:ℝ)*D))

end RegularPointCoordinates

end

end OAI

import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.SpeedApprox

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable
namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma IsTestPlan.map_evalReal_le {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {C : ℝ≥0} (hC : ∀ t : Time, Measure.map (fun γ : Curve X => γ t) π ≤ (C : ℝ≥0∞) • m) :
    Measure.map (fun z : Curve X × ℝ => evalReal z.1 z.2)
      (π.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) ≤ (C : ℝ≥0∞) • m := by
  let : IsProbabilityMeasure π := hπ.1
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.map_apply continuous_evalReal.measurable hS,
    Measure.prod_apply_symm (hS.preimage continuous_evalReal.measurable)]
  calc
    _ ≤ ∫⁻ _t in Set.Icc (0 : ℝ) 1, ((C : ℝ≥0∞) • m) S := by
      apply lintegral_mono
      intro t
      simpa only [Measure.map_apply (continuous_eval_const (clampTime t)).measurable hS,
        preimage_preimage, Function.comp_def, evalReal] using
        (hC (clampTime t)) S
    _ = _ := by simp

lemma IsTestPlan.lintegral_abs_eval_le {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {C : ℝ≥0} (hC : ∀ t : Time, Measure.map (fun γ : Curve X => γ t) π ≤ (C : ℝ≥0∞) • m)
    {D : X → ℝ} (hD : AEStronglyMeasurable D m) (t : Time) :
    (∫⁻ γ, ENNReal.ofReal |D (γ t)| ∂π) ≤ (C : ℝ≥0∞) ^ (1 / (2 : ℝ)) * eLpNorm D 2 m := by
  let : IsProbabilityMeasure π := hπ.1
  have hm := hD.mono_ac (Measure.absolutelyContinuous_of_le_smul (hC t))
  have hcomp : AEStronglyMeasurable (fun γ : Curve X => D (γ t)) π :=
    hm.comp_measurable (continuous_eval_const t).measurable
  calc
    _ = eLpNorm (fun γ : Curve X => D (γ t)) 1 π := by
      rw [eLpNorm_one_eq_lintegral_enorm hcomp]
      simp only [Real.enorm_eq_ofReal_abs]
    _ ≤ eLpNorm (fun γ : Curve X => D (γ t)) 2 π :=
      eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
    _ = eLpNorm D 2 (Measure.map (fun γ : Curve X => γ t) π) :=
      (eLpNorm_map_measure hm (continuous_eval_const t).measurable.aemeasurable).symm
    _ ≤ eLpNorm D 2 ((C : ℝ≥0∞) • m) := eLpNorm_mono_measure _ (hC t)
    _ = _ := by
      rw [eLpNorm_smul_measure_of_ne_top (by norm_num) D _ hD]
      norm_num

lemma IsTestPlan.lintegral_abs_action_le {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {C : ℝ≥0} (hC : ∀ t : Time, Measure.map (fun γ : Curve X => γ t) π ≤ (C : ℝ≥0∞) • m)
    {D : X → ℝ} (hD : AEStronglyMeasurable D m) :
    (∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal |D (evalReal γ t)| * metricSpeed γ t ∂volume ∂π) ≤
    ((C : ℝ≥0∞) ^ (1 / (2 : ℝ)) * eLpNorm D 2 m) *
      (∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1, metricSpeed γ t ^ 2 ∂volume ∂π) ^ (1/(2 : ℝ)) := by
  let : IsProbabilityMeasure π := hπ.1
  let ν := π.prod (volume.restrict (Set.Icc (0 : ℝ) 1))
  have hmap := hπ.map_evalReal_le hC
  have hm := hD.mono_ac (Measure.absolutelyContinuous_of_le_smul hmap)
  have hcomp : AEStronglyMeasurable (fun point : Curve X × ℝ =>
      D (evalReal point.1 point.2)) ν := hm.comp_measurable continuous_evalReal.measurable
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq ν
    (show Real.HolderConjugate 2 2 from Real.holderConjugate_iff.mpr (by norm_num))
    hcomp.aemeasurable.abs.ennreal_ofReal measurable_metricSpeed.aemeasurable
  have hnorm : eLpNorm (fun z : Curve X × ℝ => D (evalReal z.1 z.2)) 2 ν ≤
      (C : ℝ≥0∞) ^ (1 / (2 : ℝ)) * eLpNorm D 2 m := by
    calc
      _ = eLpNorm D 2 (Measure.map (fun z : Curve X × ℝ => evalReal z.1 z.2) ν) :=
        (eLpNorm_map_measure hm continuous_evalReal.measurable.aemeasurable).symm
      _ ≤ _ := by
        refine (eLpNorm_mono_measure _ hmap).trans_eq ?_
        rw [eLpNorm_smul_measure_of_ne_top (by norm_num) D _ hD]
        norm_num
  have ham : AEMeasurable (fun z : Curve X × ℝ =>
      ENNReal.ofReal |D (evalReal z.1 z.2)| * metricSpeed z.1 z.2) ν :=
    hcomp.aemeasurable.abs.ennreal_ofReal.mul measurable_metricSpeed.aemeasurable
  rw [← lintegral_prod _ ham]
  calc
    _ ≤ eLpNorm (fun z : Curve X × ℝ => D (evalReal z.1 z.2)) 2 ν *
        (∫⁻ z : Curve X × ℝ, metricSpeed z.1 z.2 ^ 2 ∂ν) ^ (1 / (2 : ℝ)) := by
      simpa only [Pi.mul_apply, Function.comp_apply, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hcomp, ENNReal.toReal_ofNat, Real.enorm_eq_ofReal_abs,
        ENNReal.rpow_two] using hh
    _ ≤ _ := by
      rw [lintegral_prod _ (measurable_metricSpeed.pow_const 2).aemeasurable]
      exact mul_le_mul_left hnorm _

lemma IsTestPlan.endpoint_mean_le_add {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {C : ℝ≥0} (hC : ∀ t : Time, Measure.map (fun γ : Curve X => γ t) π ≤ (C : ℝ≥0∞) • m)
    {f g : X → ℝ} (hf : AEStronglyMeasurable f m) (hg : AEStronglyMeasurable g m) :
    (∫⁻ γ, ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)| ∂π) ≤
    (∫⁻ γ, ENNReal.ofReal |g (γ timeOne) - g (γ timeZero)| ∂π) +
      (C : ℝ≥0∞) ^ (1 / (2 : ℝ)) * eLpNorm (fun x => g x - f x) 2 m +
      (C : ℝ≥0∞) ^ (1 / (2 : ℝ)) * eLpNorm (fun x => g x - f x) 2 m := by
  have hgmean : AEMeasurable (fun γ : Curve X =>
      ENNReal.ofReal |g (γ timeOne) - g (γ timeZero)|) π :=
    ((hπ.aemeasurable_eval hg.aemeasurable timeOne).sub
    (hπ.aemeasurable_eval hg.aemeasurable timeZero)).abs.ennreal_ofReal
  have hdiff : AEMeasurable (fun γ : Curve X =>
      ENNReal.ofReal |g (γ timeOne) - f (γ timeOne)|) π :=
    (hπ.aemeasurable_eval (hg.sub hf).aemeasurable timeOne).abs.ennreal_ofReal
  have hsum : AEMeasurable (fun γ : Curve X =>
      ENNReal.ofReal |g (γ timeOne) - g (γ timeZero)| +
        ENNReal.ofReal |g (γ timeOne) - f (γ timeOne)|) π := hgmean.add hdiff
  have hpt : ∀ γ : Curve X,
      ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)| ≤
      ENNReal.ofReal |g (γ timeOne) - g (γ timeZero)| +
        ENNReal.ofReal |g (γ timeOne) - f (γ timeOne)| +
        ENNReal.ofReal |g (γ timeZero) - f (γ timeZero)| := by
    intro γ
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _),
      ← ENNReal.ofReal_add (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have h1 := abs_sub_le (f (γ timeOne)) (g (γ timeOne)) (f (γ timeZero))
    have h2 := abs_sub_le (g (γ timeOne)) (g (γ timeZero)) (f (γ timeZero))
    rw [abs_sub_comm (f (γ timeOne)) (g (γ timeOne))] at h1
    linarith
  calc
    _ ≤ ∫⁻ γ, ENNReal.ofReal |g (γ timeOne) - g (γ timeZero)| +
      ENNReal.ofReal |g (γ timeOne) - f (γ timeOne)| +
      ENNReal.ofReal |g (γ timeZero) - f (γ timeZero)| ∂π := lintegral_mono hpt
    _ = (∫⁻ γ, ENNReal.ofReal |g (γ timeOne) - g (γ timeZero)| ∂π) +
      (∫⁻ γ, ENNReal.ofReal |g (γ timeOne) - f (γ timeOne)| ∂π) +
      (∫⁻ γ, ENNReal.ofReal |g (γ timeZero) - f (γ timeZero)| ∂π) := by
        rw [lintegral_add_left' hsum,
          lintegral_add_left' hgmean]
    _ ≤ _ := add_le_add (add_le_add_right (hπ.lintegral_abs_eval_le hC (hg.sub hf) timeOne) _)
      (hπ.lintegral_abs_eval_le hC (hg.sub hf) timeZero)

lemma IsTestPlan.action_le_add {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {D E : X → ℝ} (hD : LocallyL2 m D) (hE : LocallyL2 m E) :
    (∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal (E (evalReal γ t)) * metricSpeed γ t ∂volume ∂π) ≤
    (∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t ∂volume ∂π) +
    (∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal |E (evalReal γ t) - D (evalReal γ t)| * metricSpeed γ t ∂volume ∂π) := by
  let : IsProbabilityMeasure π := hπ.1
  have hdiff : LocallyL2 m (fun x => |E x - D x|) := fun o R hR =>
    ((hE o R hR).sub (hD o R hR)).norm
  rw [← lintegral_prod _ (hπ.aemeasurable_action hE),
    ← lintegral_prod _ (hπ.aemeasurable_action hD),
    ← lintegral_prod _ (hπ.aemeasurable_action hdiff),
    ← lintegral_add_left' (hπ.aemeasurable_action hD)]
  apply lintegral_mono
  intro z
  calc
    _ ≤ (ENNReal.ofReal (D (evalReal z.1 z.2)) +
        ENNReal.ofReal |E (evalReal z.1 z.2) - D (evalReal z.1 z.2)|) * metricSpeed z.1 z.2 := by
      apply mul_le_mul_left
      exact (ENNReal.ofReal_le_ofReal (by linarith [le_abs_self (E (evalReal z.1 z.2) -
        D (evalReal z.1 z.2))])).trans ENNReal.ofReal_add_le
    _ = _ := add_mul _ _ _

lemma IsLocalWeakUpperGradient.of_l2_tendsto {fn Dn : ℕ → X → ℝ} {f D : X → ℝ}
    (hn : ∀ n, IsLocalWeakUpperGradient m (fn n) (Dn n))
    (hfn : ∀ n, MemLp (fn n) 2 m) (hDn : ∀ n, MemLp (Dn n) 2 m)
    (hf : MemLp f 2 m) (hD : MemLp D 2 m)
    (hfconv : Tendsto (fun n => eLpNorm (fun x => fn n x - f x) 2 m) atTop (𝓝 0))
    (hDconv : Tendsto (fun n => eLpNorm (fun x => Dn n x - D x) 2 m) atTop (𝓝 0)) :
    IsLocalWeakUpperGradient m f D := by
  have hDl : LocallyL2 m D := fun _ _ _ => hD.restrict _
  refine ⟨hDl, ?_, ?_⟩
  · obtain ⟨ns, _hns, hlim⟩ :=
      (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        hDconv).exists_seq_tendsto_ae
    filter_upwards [hlim, ae_all_iff.mpr fun n => (hn n).2.1] with x hx hpos
    exact ge_of_tendsto hx (Eventually.of_forall fun n => hpos (ns n))
  · intro π hπ hb
    obtain ⟨C, hC⟩ := hπ.2.1
    let c : ℝ≥0∞ := (C : ℝ≥0∞) ^ (1 / (2 : ℝ))
    let k : ℝ≥0∞ := (∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1,
      metricSpeed γ t ^ 2 ∂volume ∂π) ^ (1/(2 : ℝ))
    let A : ℝ≥0∞ := ∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t ∂volume ∂π
    have hc : c ≠ ∞ := (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.coe_ne_top).ne
    have hk : k ≠ ∞ := (ENNReal.rpow_lt_top_of_nonneg (by positivity) hπ.2.2.2.ne).ne
    have hcf : Tendsto (fun n => c * eLpNorm (fun x => fn n x - f x) 2 m) atTop (𝓝 0) := by
      simpa only [Function.comp_def, mul_zero] using (ENNReal.continuous_const_mul hc).continuousAt.tendsto.comp hfconv
    have hcd : Tendsto (fun n => (c * eLpNorm (fun x => Dn n x - D x) 2 m) * k)
        atTop (𝓝 0) := by
      have hh := (ENNReal.continuous_const_mul hc).continuousAt.tendsto.comp hDconv
      simpa only [Function.comp_def, mul_zero, zero_mul] using (ENNReal.continuous_mul_const hk).continuousAt.tendsto.comp hh
    have hbound : ∀ n,
        (∫⁻ γ, ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)| ∂π) ≤
          A + (c * eLpNorm (fun x => Dn n x - D x) 2 m) * k +
          c * eLpNorm (fun x => fn n x - f x) 2 m +
          c * eLpNorm (fun x => fn n x - f x) 2 m := by
      intro n
      refine (hπ.endpoint_mean_le_add hC hf.aestronglyMeasurable
        (hfn n).aestronglyMeasurable).trans ?_
      apply add_le_add_left
      apply add_le_add_left
      refine ((hn n).2.2 π hπ hb).trans ?_
      exact (hπ.action_le_add hDl (hn n).1).trans
        (add_le_add_right (hπ.lintegral_abs_action_le hC
          ((hDn n).aestronglyMeasurable.sub hD.aestronglyMeasurable)) _)
    have hconst : Tendsto (fun _ : ℕ => A) atTop (𝓝 A) := tendsto_const_nhds
    have hlim := ((hconst.add hcd).add hcf).add hcf
    simpa only [add_zero] using ge_of_tendsto hlim (Eventually.of_forall hbound)

end WeakHessian

open Set Filter Topology Bornology
open scoped InnerProductSpace

end
end InlinedFile0

end OAI

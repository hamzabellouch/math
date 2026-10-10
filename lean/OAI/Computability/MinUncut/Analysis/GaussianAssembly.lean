import Mathlib
import OAI.Computability.MinUncut.Estimates.ExpectResampleRow

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.BoxGaussian
open MeasureTheory ProbabilityTheory GaussianHermite
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def singletonEmbed (x : ι) : Unit → ι := fun _ => x
omit [Fintype ι] [DecidableEq ι] in
lemma singletonEmbed_injective (x : ι) : Function.Injective (singletonEmbed x) := by
  intro a b _
  exact Subsingleton.elim a b

omit [Fintype ι] in
lemma update_join_singleton (x : ι) (C : Unit → ℝ) (D : Outside (singletonEmbed x) → ℝ) (t : ℝ) :
    Function.update (join (singletonEmbed x) (singletonEmbed_injective x) C D) x t =
      join (singletonEmbed x) (singletonEmbed_injective x) (fun _ => t) D := by
  funext y
  by_cases hy : y=x
  · subst y
    simpa only [Function.update_self, singletonEmbed] using
      (join_at (singletonEmbed x) (singletonEmbed_injective x) (fun _ => t) D Unit.unit).symm
  · rw [Function.update_of_ne hy]
    have hout : y∉Set.range (singletonEmbed x) := by
      rintro ⟨a,ha⟩
      exact hy ha.symm
    rw [join_other _ _ _ _ ⟨y,hout⟩,join_other _ _ _ _ ⟨y,hout⟩]

lemma integral_singleton (v : ℝ → ℝ) :
    (∫ C : Unit → ℝ, v (C Unit.unit) ∂γpi Unit) = ∫ t, v t ∂γ := by
  exact (measurePreserving_funUnique γ Unit).integral_comp
    (MeasurableEquiv.funUnique Unit ℝ).measurableEmbedding v

lemma centered_resample_memLp (x : ι) (u : (ι → ℝ) → ℝ) (hu : Measurable u)
    {A : ℝ} (hA : 0≤A) :
    MemLp (fun C => Slice.centeredClip γ A (fun t => u (Function.update C x t)) (C x)) 2 (γpi ι) := by
  have hupdate : Measurable (fun p : (ι → ℝ) × ℝ => Function.update p.1 x p.2) := by
    apply Measurable.of_eval
    intro y
    by_cases hy : y=x
    · subst y
      simpa only [Function.update_self, singletonEmbed] using measurable_snd
    · simp only [Function.update_of_ne hy]
      exact (measurable_pi_apply y).comp measurable_fst
  have hm : Measurable (fun p : (ι → ℝ) × ℝ => Slice.clip A (u (Function.update p.1 x p.2))) :=
    (measurable_const.max ((hu.comp hupdate).min measurable_const))
  have hmean : Measurable (fun C => ∫ t, Slice.clip A (u (Function.update C x t)) ∂γ) :=
    hm.stronglyMeasurable.integral_prod_right.measurable
  have hd : Measurable (fun C => Slice.centeredClip γ A (fun t => u (Function.update C x t)) (C x)) := by
    unfold Slice.centeredClip
    simp only [Function.update_eq_self]
    exact (measurable_const.max (hu.min measurable_const)).sub hmean
  apply MemLp.of_bound hd.aestronglyMeasurable (2*A)
  filter_upwards [] with C
  rw [Real.norm_eq_abs]
  unfold Slice.centeredClip
  exact (abs_sub _ _).trans (by
    have hc := Slice.clip_abs_le hA (u (Function.update C x (C x)))
    have hm : |∫ t, Slice.clip A (u (Function.update C x t)) ∂γ|≤A := by
      refine (abs_integral_le_integral_abs).trans ?_
      exact (integral_mono_of_nonneg (ae_of_all _ (fun _ => abs_nonneg _))
        (integrable_const A) (ae_of_all _ (fun t => Slice.clip_abs_le hA _))).trans_eq
          (by simp)
    linarith)

omit [DecidableEq ι] in
lemma integral_split_le {κ : Type*} [Fintype κ] (μ : Measure ℝ) [SigmaFinite μ]
    (e : κ → ι) (he : Function.Injective e) (u v : (ι → ℝ) → ℝ)
    (hu : Integrable u (Measure.pi (fun _ : ι => μ)))
    (hv : Integrable v (Measure.pi (fun _ : ι => μ))) {a : ℝ}
    (h : ∀ D : Outside e → ℝ,
      (∫ C : κ → ℝ, u (join e he C D) ∂Measure.pi (fun _ : κ => μ)) ≤
      a*(∫ C : κ → ℝ, v (join e he C D) ∂Measure.pi (fun _ : κ => μ))) :
    (∫ C, u C ∂Measure.pi (fun _ : ι => μ)) ≤ a*(∫ C, v C ∂Measure.pi (fun _ : ι => μ)) := by
  have hup := ((join_preserves μ e he).integrable_comp_emb (joinEquiv e he).measurableEmbedding).mpr hu
  have hvp := ((join_preserves μ e he).integrable_comp_emb (joinEquiv e he).measurableEmbedding).mpr hv
  rw [integral_split μ e he u hu,integral_split μ e he v hv, ← integral_const_mul]
  exact integral_mono hup.integral_prod_right (hvp.integral_prod_right.const_mul a) h

attribute [local irreducible] Finset.univ Fintype.piFinset

lemma centered_resample_loss (x : ι) (u : (ι → ℝ) → ℝ) (hum : Measurable u)
    (hu : MemLp u 2 (γpi ι))
    (hv : ∀ C, MemLp (fun t => u (Function.update C x t)) 2 γ)
    (hz : ∀ C, (∫ t, u (Function.update C x t) ∂γ)=0)
    {A : ℝ} (hA : 0<A) :
    (∫ C, |u C-Slice.centeredClip γ A (fun t => u (Function.update C x t)) (C x)| ∂γpi ι) ≤
      2*(∫ C, (u C)^2 ∂γpi ι)/A := by
  let e := singletonEmbed x
  let he := singletonEmbed_injective x
  let w := fun C => Slice.centeredClip γ A (fun t => u (Function.update C x t)) (C x)
  have hw : MemLp w 2 (γpi ι) := centered_resample_memLp x u hum hA.le
  have hl : Integrable (fun C => |u C-w C|) (γpi ι) := (hu.sub hw).integrable (by norm_num) |>.abs
  have hq : Integrable (fun C => (u C)^2) (γpi ι) := hu.integrable_sq
  have hs D : (∫ C : Unit → ℝ, |u (join e he C D)-w (join e he C D)| ∂γpi Unit) ≤
      2*(∫ C : Unit → ℝ, (u (join e he C D))^2 ∂γpi Unit)/A := by
    let C₀ := join e he (fun _ => 0) D
    let v := fun t => u (Function.update C₀ x t)
    have huC (C : Unit → ℝ) : u (join e he C D)=v (C Unit.unit) := by
      dsimp only [v,C₀,e,he]
      rw [update_join_singleton]

    have hwC (C : Unit → ℝ) : w (join e he C D)=Slice.centeredClip γ A v (C Unit.unit) := by
      dsimp only [w]
      have hh : (fun t => u (Function.update (join e he C D) x t))=v := by
        funext t
        dsimp only [v,C₀,e,he]
        rw [update_join_singleton,update_join_singleton]
      rw [hh]
      congr 1
      exact join_at e he C D Unit.unit
    simp_rw [huC,hwC]
    rw [integral_singleton (fun t => |v t-Slice.centeredClip γ A v t|),
      integral_singleton (fun t => (v t)^2)]
    exact Slice.centeredClip_loss hA (hv C₀) (hz C₀)
  change (∫ C, |u C-w C| ∂γpi ι) ≤ _
  rw [← div_mul_eq_mul_div]
  apply integral_split_le γ e he _ _ hl hq
  intro D
  simpa only [div_mul_eq_mul_div] using hs D
end MinUncut.BoxGaussian

end
end

end OAI

import OAI.MeasureTheory.Falconer.Estimates.SamplingScales
import OAI.MeasureTheory.Falconer.Geometry.ProjectionRows
import Mathlib.Probability.Distributions.Uniform

namespace OAI

/-! A finite weighted projection contains an actual separated Frostman
set. Sampling uses only the original finite labels, so every selected
projected point has an original witness. -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

theorem finite_weighted_projection_sample {δ s C c : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : 0 ≤ s) (hC : 0 ≤ C) (hc : |c| ≤ 1)
    (S : Finset (Space 2)) (hS : S.Nonempty) (hchart : InBoundedLineChart S)
    (hball : ∀ u r : ℝ, δ ≤ r →
      ((S.filter fun x => |lineParameterProjection c x-u| ≤ r).card:ℝ) ≤
        C*r^s*(S.card:ℝ)) :
    let γ := δ/4
    let B := 1-10*Real.log γ
    ∃ Q : Finset (Space 2), Q.Nonempty ∧
      Q ⊆ S.image (fun x => rowPoint 0 (lineParameterProjection c x/4)) ∧
      FiniteSeparatedAt γ Q ∧
      NormalizedFiniteBallBound γ s
        (2*(2*(((Real.exp 1-1)*(C*(4:ℝ)^s)+B)*(8:ℝ)^s))^2) Q ∧
      Q.card ≤ Nat.ceil (γ^(-s)) := by
  dsimp only
  let γ := δ/4
  let B := 1-10*Real.log γ
  let μ : ProbabilityMeasure (Space 2) := ⟨(PMF.uniformOfFinset S hS).toMeasure,inferInstance⟩
  let p : Space 2 → Space 2 := fun x =>
    if x ∈ S then rowPoint 0 (lineParameterProjection c x/4) else 0
  have hSc : 0 < (S.card:ℝ) := Nat.cast_pos.mpr hS.card_pos
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hγsmall : γ ≤ 1/4 := by dsimp [γ]; linarith only [hδ1]
  have hγ1 : γ ≤ 1 := hγsmall.trans (by norm_num)
  have hB : 1 ≤ B := by
    have hh := Real.log_nonpos hγ.le hγ1
    dsimp [B]
    linarith only [hh]
  have hSmeas : MeasurableSet (S : Set (Space 2)) := S.finite_toSet.measurableSet
  have hp : Measurable p := by
    apply Measurable.ite hSmeas
    · dsimp [rowPoint,lineParameterProjection]
      fun_prop
    · exact measurable_const
  have hpbound : ∀ x i, |p x i| ≤ 1 := by
    intro x i
    by_cases hx : x ∈ S
    · have hproj : |lineParameterProjection c x| ≤ 2 := by
        unfold lineParameterProjection
        have hm := mul_le_mul hc (hchart x hx).1 (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
        rw [← abs_mul] at hm
        exact (abs_add_le _ _).trans (by linarith only [hm,(hchart x hx).2])
      fin_cases i
      · change |(if x ∈ S then rowPoint 0 (lineParameterProjection c x/4) else 0) 0| ≤ 1
        simp only [ite_eq_left hx,rowPoint_zero,abs_zero]
        norm_num
      · change |(if x ∈ S then rowPoint 0 (lineParameterProjection c x/4) else 0) 1| ≤ 1
        simp only [ite_eq_left hx,rowPoint_one,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 4)]
        linarith only [hproj]
    · simp only [p,ite_eq_right hx,PiLp.zero_apply,abs_zero]; norm_num
  have hreal (A : Set (Space 2)) (hA : MeasurableSet A) :
      (μ : Measure (Space 2)).real A = ((S.filter fun x => x ∈ A).card:ℝ)/(S.card:ℝ) := by
    change ((PMF.uniformOfFinset S hS).toMeasure A).toReal = _
    rw [PMF.toMeasure_uniformOfFinset_apply hS A hA,ENNReal.toReal_div,
      ENNReal.toReal_natCast,ENNReal.toReal_natCast]
  have hGmass : 1 ≤ (μ : Measure (Space 2)).real (S:Set (Space 2)) := by
    rw [hreal _ hSmeas]
    apply (le_div_iff₀ hSc).2
    simp only [one_mul]
    exact_mod_cast Finset.card_le_card (show S ⊆ _ from fun x hx =>
      Finset.mem_filter.mpr ⟨hx,hx⟩)
  have hprob : ∀ z : Space 2, ∀ r : ℝ, γ ≤ r →
      (μ : Measure (Space 2)).real {x | dist (p x) z ≤ r} ≤ (C*(4:ℝ)^s)*r^s := by
    intro z r hr
    have hr0 : 0 < r := hγ.trans_le hr
    rw [hreal _ (measurableSet_le (hp.dist measurable_const) measurable_const)]
    apply (div_le_iff₀ hSc).2
    have hsub : S.filter (fun x => dist (p x) z ≤ r) ⊆
        S.filter (fun x => |lineParameterProjection c x-4*z 1| ≤ 4*r) := by
      intro x hx
      obtain ⟨hxS,hxz⟩ := Finset.mem_filter.mp hx
      refine Finset.mem_filter.mpr ⟨hxS,?_⟩
      have he : p x = rowPoint 0 (lineParameterProjection c x/4) := by simp only [p,ite_eq_left hxS]
      have hh := (PiLp.dist_apply_le (p x) z 1).trans hxz
      rw [he] at hh
      simp only [rowPoint_one,Real.dist_eq] at hh
      have hid : |lineParameterProjection c x-4*z 1| = 4*|lineParameterProjection c x/4-z 1| := by
        rw [← abs_of_pos (by norm_num : (0:ℝ) < 4),← abs_mul]
        congr 1
        ring
      rw [hid]
      linarith only [hh]
    calc
      _ ≤ ((S.filter fun x => |lineParameterProjection c x-4*z 1| ≤ 4*r).card:ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hsub)
      _ ≤ C*(4*r)^s*(S.card:ℝ) := hball _ _ (by dsimp [γ] at hr; linarith only [hr])
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hr0.le]; ring
  let n := Nat.ceil (γ^(-s))
  let L := Nat.ceil (γ⁻¹+1)
  let H := Nat.ceil γ⁻¹
  obtain ⟨hn,hnlo,hnhi⟩ := sampling_ceil_size hγ hγ1 hs
  have hfail : (((2*L+1)^2*H:ℕ):ℝ)*Real.exp (-B) ≤ 1/4 := by
    have he : Real.exp (-B) ≤ Real.exp (-(-10*Real.log γ)) := by
      apply Real.exp_le_exp.mpr
      dsimp [B]
      linarith
    have hh := (mul_le_mul_of_nonneg_left he
      (Nat.cast_nonneg (α := ℝ) ((2*L+1)^2*H))).trans (sampling_failure_bound hγ hγsmall)
    exact hh.trans (by linarith only [hγ1])
  obtain ⟨ω,D,Q,hD,hDS,hQ,hQD,hsep,hreg⟩ := exists_good_separated_point_sample μ p hp hpbound
    (S:Set (Space 2)) hSmeas (by norm_num : (0:ℝ) < 1) hGmass hn hγ hs
    (by positivity : 0 ≤ C*(4:ℝ)^s) hB (Nat.le_ceil _) (Nat.le_ceil _)
    hnlo hnhi hprob hfail
  refine ⟨Q,hQ,?_,hsep,?_,?_⟩
  · intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp (hQD hx)
    have hiS : ω i ∈ S := hDS i hi
    exact Finset.mem_image.mpr ⟨ω i,hiS,by simp only [Function.comp_apply,p,ite_eq_left hiS]⟩
  · simpa only [div_one] using hreg
  · exact (Finset.card_le_card hQD).trans
      (Finset.card_image_le.trans (by simpa using Finset.card_le_univ D))

end Falconer

end OAI

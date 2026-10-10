import Mathlib
import OAI.Probability.SKRatio.Variational.CompactField
import OAI.Probability.SKRatio.Variational.ScalarCoherent

namespace OAI

noncomputable section
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar

lemma compact_coefficients_tolerance {a : ℝ} (ha : 0<a) :
    ∃ δ : ℝ, 0<δ ∧ ∀ H : ℝ → ℝ,
      (∀ x, dist (compactWeight x) (compactWeight (H x))<δ) →
      (∀ x, |v x-v (H x)|≤a) ∧
      (∀ x, |m x*v x-m (H x)*v (H x)|≤a) ∧
      (∀ x y, |v y^2/(w x+w y)-v (H y)^2/(w (H x)+w (H y))|≤a) ∧
      (∀ x y, |kernel x y-kernel (H x) (H y)|≤a) := by
  have cm : Continuous (fun u : FieldWeight => (1-(u:ℝ))*compactV u) :=
    (continuous_const.sub continuous_subtype_val).mul continuous_compactV
  obtain ⟨δv,hδv,hv⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous continuous_compactV) a ha
  obtain ⟨δm,hδm,hm⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous cm) a ha
  obtain ⟨δf,hδf,hf⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous continuous_compactF) a ha
  obtain ⟨δk,hδk,hk⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous continuous_compactK) a ha
  let δ := min (min δv δm) (min δf δk)
  have hδ : 0<δ := lt_min (lt_min hδv hδm) (lt_min hδf hδk)
  have hδv' : δ≤δv := (min_le_left _ _).trans (min_le_left _ _)
  have hδm' : δ≤δm := (min_le_left _ _).trans (min_le_right _ _)
  have hδf' : δ≤δf := (min_le_right _ _).trans (min_le_left _ _)
  have hδk' : δ≤δk := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ,hδ,fun H hH => ⟨?_,?_,?_,?_⟩⟩
  · intro x
    have he := hv ((hH x).trans_le hδv')
    simpa only [Real.dist_eq,compactV_weight] using he.le
  · intro x
    have he := hm ((hH x).trans_le hδm')
    have heq (x : ℝ) : 1-(compactWeight x:ℝ)=m x := by dsimp [compactWeight,w]; ring
    simpa only [Real.dist_eq,compactV_weight,heq] using he.le
  · intro x y
    have hd : dist (compactWeight x,compactWeight y) (compactWeight (H x),compactWeight (H y))<δf := by
      rw [Prod.dist_eq,max_lt_iff]
      exact ⟨(hH x).trans_le hδf',(hH y).trans_le hδf'⟩
    have he := hf hd
    simpa only [Real.dist_eq,compactF_weight] using he.le
  · intro x y
    have hd : dist (compactWeight x,compactWeight y) (compactWeight (H x),compactWeight (H y))<δk := by
      rw [Prod.dist_eq,max_lt_iff]
      exact ⟨(hH x).trans_le hδk',(hH y).trans_le hδk'⟩
    have he := hk hd
    simpa only [Real.dist_eq,compactK_weight] using he.le

lemma field_error_tolerance (β T : ℝ) {e : ℝ} (he : 0<e) :
    ∃ a : ℝ, 0<a ∧ a<1 ∧ 2*a+2*T*a+5*β^2*a+4*β*sqrt a<e := by
  have hc : ContinuousAt (fun a : ℝ => 2*a+2*T*a+5*β^2*a+4*β*sqrt a) 0 := by fun_prop
  simp only [ContinuousAt,mul_zero,add_zero,sqrt_zero] at hc
  have hh := hc.eventually (gt_mem_nhds he)
  have hu : ∀ᶠ a : ℝ in 𝓝 0, a<1 := gt_mem_nhds (by norm_num)
  have hp : ∀ᶠ a : ℝ in 𝓝[>] 0, 0<a := self_mem_nhdsWithin
  obtain ⟨a,ha,hua,hga⟩ := (hp.and ((hu.and hh).filter_mono nhdsWithin_le_nhds)).exists
  exact ⟨a,ha,hua,hga⟩

end SKRatio.Bins

end

end OAI

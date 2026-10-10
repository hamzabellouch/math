import OAI.MeasureTheory.SelfSimilar.EntropyBounds

namespace OAI

universe uα uβ uγ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteDistribution

attribute [local instance] Classical.propDecidable

theorem entropy_map_le {α : Type uα} {β : Type uβ} (p : FiniteDistribution α) (f : α → β) :
    (p.map f).entropy ≤ p.entropy := by
  classical
  rw [p.entropy_map_on f p.support (fun _ h => h),p.entropy_on p.support (fun _ h => h)]
  exact FiniteEntropy.observableEntropy_le _ _ _ (fun a _ => p.nonneg a)

theorem js_le_map_add {α : Type uα} {β : Type uβ} (p q : FiniteDistribution α) (f : α → β) :
    p.js q ≤ (p.map f).js (q.map f)+(p.mix q).entropy-((p.mix q).map f).entropy := by
  classical
  have he : ((p.map f).mix (q.map f)).entropy=((p.mix q).map f).entropy := by
    let s := p.support ∪ q.support
    rw [mix_map_entropy p q f s Finset.subset_union_left Finset.subset_union_right,
      (p.mix q).entropy_map_on f s (by exact fun _ h => h)]
    rfl
  have hp := p.entropy_map_le f
  have hq := q.entropy_map_le f
  unfold js
  rw [he]
  linarith

theorem tv_maps_le_disagreement {α : Type uα} {β : Type uβ} (p : FiniteDistribution α) (f g : α → β) :
    (p.map f).tv (p.map g) ≤ ∑ a ∈ p.support, if f a = g a then 0 else p.weight a := by
  classical
  let t := (p.map f).support ∪ (p.map g).support
  rw [(p.map f).tv_on (p.map g) t Finset.subset_union_left Finset.subset_union_right]
  unfold FiniteEntropy.totalVariation
  have hm (k : α → β) (b : β) : (p.map k).weight b =
      ∑ a ∈ p.support, if k a=b then p.weight a else 0 := by
    rw [map_weight_on p k p.support (fun _ h => h)]
    simp only [FiniteEntropy.mass,Finset.sum_filter]
  have hsum : ∑ b ∈ t, |(p.map f).weight b-(p.map g).weight b| ≤
      ∑ a ∈ p.support, if f a = g a then 0 else 2*p.weight a := by
    calc
      _ ≤ ∑ b ∈ t, ∑ a ∈ p.support,
          |(if f a=b then p.weight a else 0)-(if g a=b then p.weight a else 0)| := by
        apply Finset.sum_le_sum
        intro b _
        rw [hm f b,hm g b,← Finset.sum_sub_distrib]
        exact Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a ha
        by_cases h : f a=g a
        · simp [h]
        · have hf : f a ∈ t := Finset.mem_union_left _ (Finset.mem_image_of_mem f ha)
          have hg : g a ∈ t := Finset.mem_union_right _ (Finset.mem_image_of_mem g ha)
          have habs : ∀ b, |(if f a=b then p.weight a else 0)-(if g a=b then p.weight a else 0)| =
              (if f a=b then p.weight a else 0)+(if g a=b then p.weight a else 0) := by
            intro b
            by_cases hfb : f a=b <;> by_cases hgb : g a=b
            · exact (h (hfb.trans hgb.symm)).elim
            · simp [hfb,hgb,abs_of_nonneg (p.nonneg a)]
            · simp [hfb,hgb,abs_of_nonneg (p.nonneg a)]
            · simp [hfb,hgb]
          simp_rw [habs]
          rw [Finset.sum_add_distrib]
          simp only [Finset.sum_ite_eq,hf,hg,ite_true,h,ite_false]
          ring
  have he : (∑ a ∈ p.support, if f a=g a then 0 else 2*p.weight a) =
      2*∑ a ∈ p.support, if f a=g a then 0 else p.weight a := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> ring
  rw [he] at hsum
  linarith

end FiniteDistribution
namespace RandomGrid

local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
  ⟨by simp⟩

noncomputable def hit (c : AddCircle (1 : ℝ)) (r : ℝ) (u : AddCircle (1 : ℝ)) : ℝ :=
  if dist u c ≤ r then 1 else 0

theorem hit_eq_indicator (c : AddCircle (1 : ℝ)) (r : ℝ) :
    hit c r = (Metric.closedBall c r).indicator (fun _ => (1 : ℝ)) := by
  classical
  ext u
  change (if dist u c ≤ r then 1 else 0) = (if u ∈ Metric.closedBall c r then 1 else 0)
  rfl

theorem hit_integrable (c : AddCircle (1 : ℝ)) (r : ℝ) : Integrable (hit c r) := by
  rw [hit_eq_indicator]
  exact (integrable_const 1).indicator measurableSet_closedBall

theorem integral_hit (c : AddCircle (1 : ℝ)) {r : ℝ} (hr : 0 ≤ r) :
    (∫ u, hit c r u) = min 1 (2 * r) := by
  rw [hit_eq_indicator, integral_indicator_const _ measurableSet_closedBall]
  simp only [Measure.real, AddCircle.volume_closedBall, smul_eq_mul, mul_one]
  exact ENNReal.toReal_ofReal (le_min (by norm_num) (mul_nonneg (by norm_num) hr))

theorem circle_norm_le_of_floor_ne {x y : ℝ} (h : ⌊x⌋ ≠ ⌊y⌋) :
    ‖(x : AddCircle (1 : ℝ))‖ ≤ |y - x| := by
  rw [AddCircle.norm_eq]
  simp only [inv_one, one_mul, mul_one]
  rcases lt_or_gt_of_ne h with hxy | hxy
  · apply (round_le x (⌊x⌋ + 1)).trans
    have hy : (⌊x⌋ : ℝ) + 1 ≤ y := by
      have hh : ⌊x⌋ + 1 ≤ ⌊y⌋ := hxy
      have hh' : (⌊x⌋ : ℝ) + 1 ≤ (⌊y⌋ : ℝ) := by exact_mod_cast hh
      exact hh'.trans (Int.floor_le y)
    have hx := Int.lt_floor_add_one x
    rw [Int.cast_add, Int.cast_one, abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · apply (round_le x ⌊x⌋).trans
    have hy : y ≤ (⌊x⌋ : ℝ) := by
      have hh : ⌊y⌋ + 1 ≤ ⌊x⌋ := hxy
      have hh' : (⌊y⌋ : ℝ) + 1 ≤ (⌊x⌋ : ℝ) := by exact_mod_cast hh
      exact (Int.lt_floor_add_one y).le.trans hh'
    have hx := Int.floor_le x
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    linarith

end RandomGrid

namespace MeasureEntropy

theorem observationLaw_map_weight {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → β) (hf : Measurable f) (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s)
    (g : β → γ) (c : γ) :
    ((observationLaw μ f hf s hs).map g).weight c = mass μ (g ∘ f) c := by
  classical
  rw [FiniteDistribution.map_weight_on _ _ s (fun _ h => h)]
  exact (mass_comp μ f hf s hs g c).symm

theorem integral_finite_observation {α : Type uα} {β : Type uβ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → β) (hf : Measurable f) (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s)
    (F : β → ℝ) : ∫ x, F (f x) ∂μ = ∑ b ∈ s, mass μ f b*F b := by
  classical
  have he : (fun x => F (f x)) =ᵐ[μ]
      fun x => ∑ b ∈ s, ({x | f x=b} : Set α).indicator (fun _ => F b) x := by
    filter_upwards [hs] with x hx
    simp only [Set.indicator_apply,Set.mem_ofPred]
    simp [Finset.sum_ite_eq,hx]
  rw [integral_congr_ae he, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro b _
    change (∫ a, (f ⁻¹' {b}).indicator (fun _ => F b) a ∂μ) = _
    rw [integral_indicator_const _ ((measurableSet_singleton b).preimage hf)]
    rfl
  · intro b _
    exact (integrable_const _).indicator ((measurableSet_singleton b).preimage hf)

theorem entropy_binary_extra {α : Type uα} {β : Type uβ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [DecidableEq β]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → β) (g : α → ℤ)
    (hf : Measurable f) (hg : Measurable g) (s : Finset β)
    (hs : ∀ᵐ x ∂μ, f x ∈ s) (hg01 : ∀ᵐ x ∂μ, g x ∈ Finset.Icc (0 : ℤ) 1)
    (bad : β → Prop) [DecidablePred bad]
    (hgood : ∀ᵐ x ∂μ, ¬bad (f x) → g x=0) :
    entropy μ (fun x => (g x,f x))-entropy μ f ≤
      (∫ x, if bad (f x) then (1 : ℝ) else 0 ∂μ)*Real.log 2 := by
  classical
  let t := ((Finset.Icc (0 : ℤ) 1) ×ˢ s).filter (fun y => bad y.2 ∨ y.1=0)
  let F := fun x => (g x,f x)
  have hF : Measurable F := hg.prodMk hf
  have ht : ∀ᵐ x ∂μ, F x ∈ t := by
    filter_upwards [hs,hg01,hgood] with x hx hgx hgoodx
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hgx,hx⟩,or_iff_not_imp_left.mpr hgoodx⟩
  have hh := FiniteEntropy.conditionalEntropy_le_bad_mass t (mass μ F) Prod.fst Prod.snd bad
    (fun a _ => mass_nonneg μ F a) (by
      intro a ha b hb hab hbad
      have ha' := (Finset.mem_filter.mp ha).2.resolve_left hbad
      have hb' := (Finset.mem_filter.mp hb).2.resolve_left (hab ▸ hbad)
      exact ha'.trans hb'.symm)
  have hi : (fun a : ℤ × β => (a.1,a.2))=id := rfl
  unfold FiniteEntropy.conditionalEntropy at hh
  rw [hi,FiniteEntropy.observableEntropy_id,← entropy_comp μ F hF t ht Prod.snd] at hh
  change FiniteEntropy.entropy t (mass μ F)-entropy μ f ≤ _ at hh
  unfold FiniteEntropy.entropy at hh
  rw [← entropy_eq_sum μ F t ht] at hh
  have hbad0 : 0 ≤ ∑ a ∈ t, if bad a.2 then mass μ F a else 0 := by
    apply Finset.sum_nonneg
    intro a _
    split_ifs
    · exact mass_nonneg μ F a
    · exact le_rfl
  have hc : (t.image Prod.fst).card ≤ 2 := by
    have hsub : t.image Prod.fst ⊆ Finset.Icc (0 : ℤ) 1 := by
      rintro a ha
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hb).1).1
    simpa using Finset.card_le_card hsub
  have hl : Real.log (t.image Prod.fst).card ≤ Real.log 2 := by
    by_cases hz : (t.image Prod.fst).card=0
    · simp [hz,Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
    · apply Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz))
      exact_mod_cast hc
  have he : (∫ x, if bad (f x) then (1 : ℝ) else 0 ∂μ) =
      ∑ a ∈ t, if bad a.2 then mass μ F a else 0 := by
    have h := integral_finite_observation μ F hF t ht
      (fun a : ℤ × β => if bad a.2 then (1 : ℝ) else 0)
    simpa only [F, mul_ite, mul_one, mul_zero] using h

  rw [he]
  exact hh.trans (mul_le_mul_of_nonneg_left hl hbad0)

end MeasureEntropy

end EntropyRateDimension
end

end OAI

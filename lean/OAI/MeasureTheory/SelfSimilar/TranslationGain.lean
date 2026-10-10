import OAI.MeasureTheory.SelfSimilar.Boundary

namespace OAI

universe uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace MeasureEntropy

attribute [local instance] Classical.propDecidable

theorem mass_halfMix {α : Type uα} {β : Type uβ} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (f : α → β) (b : β) :
    mass ((1/2 : ℝ≥0∞) • μ+(1/2 : ℝ≥0∞) • ν) f b = (mass μ f b+mass ν f b)/2 := by
  unfold mass
  rw [Measure.real_def, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    smul_eq_mul,smul_eq_mul,ENNReal.toReal_add
      (ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _))
      (ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _))]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat]
  rw [Measure.real_def,Measure.real_def]
  ring

theorem observationLaw_map_entropy {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → β) (hf : Measurable f) (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s)
    (g : β → γ) :
    ((observationLaw μ f hf s hs).map g).entropy = entropy μ (g ∘ f) := by
  apply tsum_congr
  intro c
  rw [observationLaw_map_weight]

theorem mix_observationLaw_map_entropy {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α → β) (hf : Measurable f) (s t : Finset β)
    (hs : ∀ᵐ x ∂μ, f x ∈ s) (ht : ∀ᵐ x ∂ν, f x ∈ t) (g : β → γ) :
    (((observationLaw μ f hf s hs).map g).mix
      ((observationLaw ν f hf t ht).map g)).entropy =
      entropy ((1/2 : ℝ≥0∞) • μ+(1/2 : ℝ≥0∞) • ν) (g ∘ f) := by
  apply tsum_congr
  intro c
  congr 1
  change (((observationLaw μ f hf s hs).map g).weight c+
    ((observationLaw ν f hf t ht).map g).weight c)/2 = _
  rw [observationLaw_map_weight,observationLaw_map_weight,mass_halfMix]

noncomputable def information {α : Type uα} {β : Type uβ} [MeasurableSpace α]
    (μ ν : Measure α) (f : α → β) : ℝ :=
  entropy ((1/2 : ℝ≥0∞) • μ+(1/2 : ℝ≥0∞) • ν) f-(entropy μ f+entropy ν f)/2

theorem js_observationLaw_map {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α → β) (hf : Measurable f) (s t : Finset β)
    (hs : ∀ᵐ x ∂μ, f x ∈ s) (ht : ∀ᵐ x ∂ν, f x ∈ t) (g : β → γ) :
    ((observationLaw μ f hf s hs).map g).js ((observationLaw ν f hf t ht).map g) =
      information μ ν (g ∘ f) := by
  rw [FiniteDistribution.js,mix_observationLaw_map_entropy,
    observationLaw_map_entropy,observationLaw_map_entropy]
  rfl

theorem js_observationLaw {α : Type uα} {β : Type uβ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α → β) (hf : Measurable f) (s t : Finset β)
    (hs : ∀ᵐ x ∂μ, f x ∈ s) (ht : ∀ᵐ x ∂ν, f x ∈ t) :
    (observationLaw μ f hf s hs).js (observationLaw ν f hf t ht) = information μ ν f := by
  unfold FiniteDistribution.js information
  congr 1
  apply tsum_congr
  intro b
  congr 1
  exact (mass_halfMix μ ν f b).symm

theorem information_le_map_add {α : Type uα} {β : Type uβ} {γ : Type uγ} {δ : Type uδ} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : α → β) (hF : Measurable F) (s t : Finset β)
    (hs : ∀ᵐ x ∂μ, F x ∈ s) (ht : ∀ᵐ x ∂ν, F x ∈ t)
    (f : β → γ) (g : β → δ) :
    information μ ν (g ∘ F) ≤ information μ ν (f ∘ F)+
      entropy ((1/2 : ℝ≥0∞) • μ+(1/2 : ℝ≥0∞) • ν) F-
      entropy ((1/2 : ℝ≥0∞) • μ+(1/2 : ℝ≥0∞) • ν) (f ∘ F) := by
  classical
  let p := observationLaw μ F hF s hs
  let q := observationLaw ν F hF t ht
  have h := (p.js_map_le q g).trans (p.js_le_map_add q f)
  rw [js_observationLaw_map,js_observationLaw_map] at h
  have he : (p.mix q).entropy=entropy ((1/2 : ℝ≥0∞) • μ+(1/2 : ℝ≥0∞) • ν) F := by
    apply tsum_congr
    intro b
    congr 1
    exact (mass_halfMix μ ν F b).symm
  have hf : ((p.mix q).map f).entropy = entropy ((1/2 : ℝ≥0∞) • μ+(1/2 : ℝ≥0∞) • ν) (f ∘ F) := by
    rw [(p.mix q).entropy_map_on f (p.support ∪ q.support) (fun _ h => h)]
    change FiniteEntropy.observableEntropy (p.support ∪ q.support)
      (fun a => (p.weight a+q.weight a)/2) f = _
    rw [← FiniteDistribution.mix_map_entropy p q f (p.support ∪ q.support)
      Finset.subset_union_left Finset.subset_union_right]
    exact mix_observationLaw_map_entropy μ ν F hF s t hs ht f
  rwa [he,hf] at h

theorem information_map_le_disagreement {α : Type uα} {β : Type uβ} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure α) [IsProbabilityMeasure μ] (T : α → α) (hT : Measurable T)
    (f : α → β) (hf : Measurable f) (s t : Finset β)
    (hs : ∀ᵐ x ∂μ, f x ∈ s) (ht : ∀ᵐ x ∂μ, f (T x) ∈ t) :
    information μ (μ.map T) f ≤ (∫ x, if f x=f (T x) then (0 : ℝ) else 1 ∂μ)*Real.log 2 := by
  classical
  let : IsProbabilityMeasure (μ.map T) := (Measure.isProbabilityMeasure_map_iff hT.aemeasurable).2 inferInstance
  let F := fun x => (f x,f (T x))
  have hF : Measurable F := hf.prodMk (hf.comp hT)
  have hst : ∀ᵐ x ∂μ, F x ∈ s ×ˢ t := by
    filter_upwards [hs,ht] with x hx hy
    exact Finset.mem_product.mpr ⟨hx,hy⟩
  let p := observationLaw μ F hF (s ×ˢ t) hst
  have he1 : (p.map Prod.fst).entropy=entropy μ f :=
    observationLaw_map_entropy μ F hF _ hst Prod.fst
  have he2 : (p.map Prod.snd).entropy=entropy (μ.map T) f := by
    rw [observationLaw_map_entropy,entropy_map μ T hT f hf]
    rfl
  have hem : ((p.map Prod.fst).mix (p.map Prod.snd)).entropy=
      entropy ((1/2 : ℝ≥0∞) • μ+(1/2 : ℝ≥0∞) • μ.map T) f := by
    apply tsum_congr
    intro b
    congr 1
    change ((p.map Prod.fst).weight b+(p.map Prod.snd).weight b)/2=_
    rw [observationLaw_map_weight,observationLaw_map_weight,mass_halfMix,
      mass_map μ T hT f hf]
    rfl
  have hi : (p.map Prod.fst).js (p.map Prod.snd)=information μ (μ.map T) f := by
    rw [FiniteDistribution.js,he1,he2,hem]
    rfl
  have hh := (p.map Prod.fst).js_le_tv (p.map Prod.snd)
  have ht' := p.tv_maps_le_disagreement Prod.fst Prod.snd
  have he : (∫ x, if f x=f (T x) then (0 : ℝ) else 1 ∂μ) =
      ∑ b ∈ p.support, if b.1=b.2 then 0 else p.weight b := by
    have h := integral_finite_observation μ F hF (s ×ˢ t) hst
      (fun b : β × β => if b.1=b.2 then (0 : ℝ) else 1)
    simpa only [F,p,observationLaw,mul_ite,mul_zero,mul_one] using h
  rw [hi] at hh
  rw [he]
  exact hh.trans (mul_le_mul_of_nonneg_right ht' (Real.log_nonneg (by norm_num)))

theorem fairShift_eq_halfMix (μ : Measure ℝ) (v : ℝ) :
    fairShift μ v = (1/2 : ℝ≥0∞) • μ+(1/2 : ℝ≥0∞) • μ.map (fun x => x+v) := by
  norm_num [fairShift,Fin.sum_univ_two, ENNReal.ofReal_div_of_pos]

noncomputable def gridInformation (μ : Measure ℝ) (v s u : ℝ) : ℝ :=
  information μ (μ.map (fun x => x+v)) (label s u)

theorem gridInformation_eq (μ : Measure ℝ) (v s u : ℝ) :
    gridInformation μ v s u = grid (fairShift μ v) s u-
      (grid μ s u+grid (μ.map (fun x => x+v)) s u)/2 := by
  rw [fairShift_eq_halfMix]
  rfl

theorem gridInformation_intervalIntegrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) (v : ℝ) {s : ℝ} (hs : 0 < s) :
    IntervalIntegrable (gridInformation μ v s) volume 0 1 := by
  let := fairShift_probability μ v
  let : IsProbabilityMeasure (μ.map (fun x => x+v)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_id.add_const v).aemeasurable).2 inferInstance
  have hc : CompactlyCarried (μ.map (fun x => x+v)) := by simpa only [one_mul] using hμ.map_affine 1 v
  have he : gridInformation μ v s = fun u => grid (fairShift μ v) s u-
      (grid μ s u+grid (μ.map (fun x => x+v)) s u)/2 := funext (gridInformation_eq μ v s)
  rw [he]
  exact (grid_intervalIntegrable _ (hμ.fairShift v) hs 0 1).sub
    (((grid_intervalIntegrable μ hμ hs 0 1).add (grid_intervalIntegrable _ hc hs 0 1)).div_const 2)

theorem integral_gridInformation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) (v : ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ u in (0 : ℝ)..1, gridInformation μ v s u) = averaged (fairShift μ v) s-averaged μ s := by
  let := fairShift_probability μ v
  let : IsProbabilityMeasure (μ.map (fun x => x+v)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_id.add_const v).aemeasurable).2 inferInstance
  have hc : CompactlyCarried (μ.map (fun x => x+v)) := by simpa only [one_mul] using hμ.map_affine 1 v
  simp_rw [gridInformation_eq]
  rw [intervalIntegral.integral_sub (grid_intervalIntegrable _ (hμ.fairShift v) hs 0 1)
      (((grid_intervalIntegrable μ hμ hs 0 1).add (grid_intervalIntegrable _ hc hs 0 1)).div_const 2),
    intervalIntegral.integral_div,intervalIntegral.integral_add (grid_intervalIntegrable μ hμ hs 0 1)
      (grid_intervalIntegrable _ hc hs 0 1),← averaged_eq_intervalIntegral,← averaged_eq_intervalIntegral,
    ← averaged_eq_intervalIntegral,averaged_translate μ hμ hs v]
  ring

theorem gridInformation_le_boundary (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {v t : ℝ} (hv : 0 < v) (ht : 0 < t) (hvt : v ≤ t) (u : ℝ) :
    gridInformation μ v t u ≤ (∫ x, Boundary.increment (v/t) (u+x/t) ∂μ)*Real.log 2 := by
  classical
  obtain ⟨B,_,hB⟩ := hμ
  have h1 := label_ae_finite (u := u) μ ht hB
  have he : (fun x => label t u (x+v))=label t (u+v/t) := by
    funext x
    dsimp [label]
    congr 1
    ring
  have h2 : ∀ᵐ x ∂μ, label t u (x+v) ∈ Finset.Icc ⌊-B/t+(u+v/t)⌋ ⌊B/t+(u+v/t)⌋ := by
    filter_upwards [label_ae_finite (u := u+v/t) μ ht hB] with x hx
    rwa [congrFun he x]
  have hh := information_map_le_disagreement μ (fun x => x+v) (measurable_id.add_const v)
    (label t u) (label_measurable t u) _ _ h1 h2
  have hi : (fun x => if label t u x=label t u (x+v) then (0 : ℝ) else 1) =
      fun x => Boundary.increment (v/t) (u+x/t) := by
    funext x
    rw [Boundary.increment_eq_ite (div_nonneg hv.le ht.le) ((div_le_one ht).mpr hvt)]
    have hleft : ⌊u+x/t⌋=label t u x := by dsimp [label]; rw [add_comm]
    have hright : ⌊u+x/t+v/t⌋=label t u (x+v) := by dsimp [label]; congr 1; ring
    rw [hleft,hright]
    simp only [eq_comm]
  calc
    gridInformation μ v t u ≤ _ := hh
    _ = _ := by
      congr 1
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      by_cases hz : label t u x = label t u (x+v)
      · simpa only [ite_eq_left hz] using congrFun hi x
      · simpa only [ite_eq_right hz] using congrFun hi x

theorem averaged_fairShift_gain_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {v t : ℝ} (hv : 0 < v) (ht : 0 < t) (hvt : v ≤ t) :
    averaged (fairShift μ v) t-averaged μ t ≤ (v/t)*Real.log 2 := by
  have hi := (Boundary.increment_measure_intervalIntegrable μ (div_nonneg hv.le ht.le)
    ((div_le_one ht).mpr hvt) (fun x => x/t) (measurable_id.div_const t)).mul_const (Real.log 2)
  have hh := intervalIntegral.integral_mono zero_le_one
    (gridInformation_intervalIntegrable μ hμ v ht) hi (fun u => gridInformation_le_boundary μ hμ hv ht hvt u)
  rw [integral_gridInformation μ hμ v ht,intervalIntegral.integral_mul_const,
    Boundary.integral_increment_measure μ (div_nonneg hv.le ht.le) ((div_le_one ht).mpr hvt)
      (fun x => x/t) (measurable_id.div_const t)] at hh
  exact hh

theorem relativeLabel_zero_of_good {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (u w x : ℝ)
    (hgood : ⌊u+(s/t)*(label s w x : ℝ)-(s/t)*w+s/t⌋ =
      ⌊u+(s/t)*(label s w x : ℝ)-(s/t)*w⌋) :
    relativeLabel t s u w x=0 := by
  let b := u+(s/t)*(label s w x : ℝ)-(s/t)*w
  let z := x/s+w-(label s w x : ℝ)
  have hz : 0 ≤ z := sub_nonneg.mpr (Int.floor_le _)
  have hz1 : z ≤ 1 := by
    change x/s+w-(⌊x/s+w⌋ : ℝ) ≤ 1
    linarith [Int.lt_floor_add_one (x/s+w)]
  have hl := Int.floor_le_floor (show b ≤ b+(s/t)*z from le_add_of_nonneg_right (mul_nonneg (div_pos hs ht).le hz))
  have hu := Int.floor_le_floor (show b+(s/t)*z ≤ b+s/t by nlinarith [div_pos hs ht])
  change ⌊b+s/t⌋=⌊b⌋ at hgood
  have hf : ⌊b+(s/t)*z⌋=⌊b⌋ := le_antisymm (hu.trans_eq hgood) hl
  have he : b+(s/t)*z=x/t+u := by
    dsimp [b,z]
    field_simp
    ring
  rw [he] at hf
  have hb : (s/t)*(label s w x : ℝ)+u-(s/t)*w=b := by dsimp [b]; ring
  unfold relativeLabel
  rw [hb]
  change ⌊x/t+u⌋-⌊b⌋=0
  omega

theorem gridInformation_le_fine_add_boundary (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) (v : ℝ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hst : s ≤ t) (u w : ℝ) :
    gridInformation μ v t u ≤ gridInformation μ v s w+
      (∫ x, Boundary.increment (s/t) (u+((s/t)*(label s w x : ℝ)-(s/t)*w)) ∂fairShift μ v)*Real.log 2 := by
  classical
  let ν := μ.map (fun x => x+v)
  let : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff (measurable_id.add_const v).aemeasurable).2 inferInstance
  let := fairShift_probability μ v
  have hcν : CompactlyCarried ν := by simpa only [one_mul] using hμ.map_affine 1 v
  have hcρ := hμ.fairShift v
  let f := label s w
  let g := relativeLabel t s u w
  let F := fun x => (g x,f x)
  have hF : Measurable F := (relativeLabel_measurable t s u w).prodMk (label_measurable s w)
  have hceil : ⌈s/t⌉=(1 : ℤ) := by
    have hl := Int.ceil_pos.mpr (div_pos hs ht)
    have hu : ⌈s/t⌉ ≤ (1 : ℤ) := Int.ceil_le.mpr (by norm_num; exact (div_le_one ht).mpr hst)
    omega
  have hg : ∀ x, g x ∈ Finset.Icc (0 : ℤ) 1 := by
    intro x
    simpa only [hceil] using relativeLabel_mem ht hs u w x
  let aμ := Finset.Icc ⌊-hμ.choose/s+w⌋ ⌊hμ.choose/s+w⌋
  let aν := Finset.Icc ⌊-hcν.choose/s+w⌋ ⌊hcν.choose/s+w⌋
  have hfμ : ∀ᵐ x ∂μ, f x ∈ aμ := label_ae_finite μ hs hμ.choose_spec.2
  have hfν : ∀ᵐ x ∂ν, f x ∈ aν := label_ae_finite ν hs hcν.choose_spec.2
  have hFμ : ∀ᵐ x ∂μ, F x ∈ (Finset.Icc (0 : ℤ) 1) ×ˢ aμ := by
    filter_upwards [hfμ] with x hx
    exact Finset.mem_product.mpr ⟨hg x,hx⟩
  have hFν : ∀ᵐ x ∂ν, F x ∈ (Finset.Icc (0 : ℤ) 1) ×ˢ aν := by
    filter_upwards [hfν] with x hx
    exact Finset.mem_product.mpr ⟨hg x,hx⟩
  let r : ℤ × ℤ → ℤ := fun p => p.1+⌊(s/t)*(p.2 : ℝ)+u-(s/t)*w⌋
  have hr : r ∘ F=label t u := by
    funext x
    dsimp [r,F,g,f,relativeLabel]
    omega
  have hh := information_le_map_add μ ν F hF _ _ hFμ hFν Prod.snd r
  rw [hr,← fairShift_eq_halfMix] at hh
  change gridInformation μ v t u ≤ gridInformation μ v s w+entropy (fairShift μ v) F-
    entropy (fairShift μ v) f at hh
  let bad : ℤ → Prop := fun k => ⌊u+(s/t)*(k : ℝ)-(s/t)*w+s/t⌋ ≠ ⌊u+(s/t)*(k : ℝ)-(s/t)*w⌋
  have hgood : ∀ᵐ x ∂fairShift μ v, ¬bad (f x) → g x=0 := by
    apply Filter.Eventually.of_forall
    intro x hx
    apply relativeLabel_zero_of_good ht hs u w x
    exact not_not.mp hx
  have hb := entropy_binary_extra (fairShift μ v) f g (label_measurable s w)
    (relativeLabel_measurable t s u w) _ (label_ae_finite (fairShift μ v) hs hcρ.choose_spec.2)
    (Filter.Eventually.of_forall hg) bad hgood
  have he : (fun x => if bad (f x) then (1 : ℝ) else 0)=
      fun x => Boundary.increment (s/t) (u+((s/t)*(label s w x : ℝ)-(s/t)*w)) := by
    funext x
    rw [Boundary.increment_eq_ite (div_pos hs ht).le ((div_le_one ht).mpr hst)]
    simp only [bad,f,add_sub_assoc,ite_not]
  rw [he] at hb
  change entropy (fairShift μ v) F-entropy (fairShift μ v) f ≤ _ at hb
  linarith

theorem averaged_fairShift_gain_compare (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) (v : ℝ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s ≤ t) :
    averaged (fairShift μ v) t-averaged μ t ≤
      averaged (fairShift μ v) s-averaged μ s+(s/t)*Real.log 2 := by
  let := fairShift_probability μ v
  have hh (w : ℝ) : averaged (fairShift μ v) t-averaged μ t ≤
      gridInformation μ v s w+(s/t)*Real.log 2 := by
    let b := fun x => (s/t)*(label s w x : ℝ)-(s/t)*w
    have hb : Measurable b :=
      ((((measurable_of_countable (fun n : ℤ => (n : ℝ))).comp
        (label_measurable s w)).const_mul (s/t)).sub_const ((s/t)*w))
    have hi := (intervalIntegrable_const (c := gridInformation μ v s w)).add
      ((Boundary.increment_measure_intervalIntegrable (fairShift μ v) (div_pos hs ht).le
        ((div_le_one ht).mpr hst) b hb).mul_const (Real.log 2))
    have h := intervalIntegral.integral_mono zero_le_one
      (gridInformation_intervalIntegrable μ hμ v ht) hi
      (fun u => gridInformation_le_fine_add_boundary μ hμ v hs ht hst u w)
    rw [integral_gridInformation μ hμ v ht,
      intervalIntegral.integral_add intervalIntegrable_const
        ((Boundary.increment_measure_intervalIntegrable (fairShift μ v) (div_pos hs ht).le
          ((div_le_one ht).mpr hst) b hb).mul_const (Real.log 2)),
      intervalIntegral.integral_const,intervalIntegral.integral_mul_const,
      Boundary.integral_increment_measure (fairShift μ v) (div_pos hs ht).le
        ((div_le_one ht).mpr hst) b hb] at h
    simpa only [sub_zero,one_smul] using h
  have h := intervalIntegral.integral_mono zero_le_one
    (intervalIntegrable_const (c := averaged (fairShift μ v) t-averaged μ t))
    ((gridInformation_intervalIntegrable μ hμ v hs).add intervalIntegrable_const) hh
  rw [intervalIntegral.integral_const,
    intervalIntegral.integral_add (gridInformation_intervalIntegrable μ hμ v hs) intervalIntegrable_const,
    integral_gridInformation μ hμ v hs,intervalIntegral.integral_const] at h
  simpa only [sub_zero,one_smul] using h

theorem two_point_gain (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s v t : ℝ} (hs : 0 < s) (hsv : s < v) (hvt : v < t) :
    deficit μ v-(s/v+v/t)*Real.log 2 ≤
      (averaged (fairShift μ v) s-averaged (fairShift μ v) t)-(averaged μ s-averaged μ t) := by
  have hv := hs.trans hsv
  have ht := hv.trans hvt
  have hf := averaged_fairShift_gain_compare μ hμ v hs hv hsv.le
  have hc := averaged_fairShift_gain_le μ hμ hv ht hvt.le
  have hd : averaged (fairShift μ v) v-averaged μ v=deficit μ v := by
    rw [averaged_fairShift μ hμ hv]
    unfold deficit
    ring
  rw [hd] at hf
  nlinarith

end MeasureEntropy

end EntropyRateDimension

end

end OAI

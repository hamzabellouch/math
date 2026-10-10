import OAI.MeasureTheory.SelfSimilar.FiniteDistribution

namespace OAI

universe uι uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace MeasureEntropy

noncomputable def mass {α : Type uα} {β : Type uβ} [MeasurableSpace α] (μ : Measure α)
    (f : α → β) (b : β) : ℝ := μ.real {x | f x = b}

noncomputable def entropy {α : Type uα} {β : Type uβ} [MeasurableSpace α] (μ : Measure α)
    (f : α → β) : ℝ := ∑' b, Real.negMulLog (mass μ f b)

theorem mass_nonneg {α : Type uα} {β : Type uβ} [MeasurableSpace α] (μ : Measure α)
    (f : α → β) (b : β) : 0 ≤ mass μ f b := ENNReal.toReal_nonneg

theorem mass_le_one {α : Type uα} {β : Type uβ} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f : α → β) (b : β) : mass μ f b ≤ 1 := by
  exact (measureReal_mono (Set.subset_univ _)).trans_eq (by simp)

theorem entropy_nonneg {α : Type uα} {β : Type uβ} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f : α → β) : 0 ≤ entropy μ f :=
  tsum_nonneg (fun b => Real.negMulLog_nonneg (mass_nonneg μ f b) (mass_le_one μ f b))

theorem mass_eq_zero_of_ae {α : Type uα} {β : Type uβ} [MeasurableSpace α] (μ : Measure α)
    (f : α → β) (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) {b : β} (hb : b ∉ s) :
    mass μ f b = 0 := by
  have hh : μ {x | f x = b} = 0 := measure_mono_null (by
    intro x hx
    change f x = b at hx
    change f x ∉ s
    simpa only [hx] using hb) (ae_iff.mp hs)
  simp only [mass, Measure.real_def, hh, ENNReal.toReal_zero]

theorem entropy_eq_sum {α : Type uα} {β : Type uβ} [MeasurableSpace α] (μ : Measure α)
    (f : α → β) (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) :
    entropy μ f = ∑ b ∈ s, Real.negMulLog (mass μ f b) := by
  apply tsum_eq_sum
  intro b hb
  rw [mass_eq_zero_of_ae μ f s hs hb, Real.negMulLog_zero]

theorem mass_sum {α : Type uα} {β : Type uβ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → β) (hf : Measurable f) (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) :
    ∑ b ∈ s, mass μ f b = 1 := by
  classical
  have hd : (↑s : Set β).PairwiseDisjoint (fun b => {x | f x = b}) := by
    intro b _ c _ hbc
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hbc (hx.symm.trans hy)
  have hm : ∀ b ∈ s, MeasurableSet {x | f x = b} :=
    fun b _ => (measurableSet_singleton b).preimage hf
  have he : (⋃ b ∈ s, {x | f x = b}) = {x | f x ∈ s} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨b,hb,hxb⟩
      simpa only [hxb] using hb
    · intro hx
      exact ⟨f x,hx,rfl⟩
  have hu : μ (⋃ b ∈ s, {x | f x = b}) = 1 := by
    rw [he]
    calc
      _ = μ Set.univ := measure_congr (by
        filter_upwards [hs] with x hx
        apply propext
        change (f x ∈ s) ↔ True
        exact iff_true_intro hx)
      _ = 1 := measure_univ
  rw [measure_biUnion_finset hd hm] at hu
  have he' := congrArg ENNReal.toReal hu
  simpa only [ENNReal.toReal_sum (fun b _ => measure_ne_top μ _), ENNReal.toReal_one, mass, Measure.real_def] using he'

def CompactlyCarried (μ : Measure ℝ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ μ (Set.Icc (-B) B)ᶜ = 0

noncomputable def label (s u x : ℝ) : ℤ := ⌊x/s+u⌋

noncomputable def grid (μ : Measure ℝ) (s u : ℝ) : ℝ := entropy μ (label s u)

noncomputable def averaged (μ : Measure ℝ) (s : ℝ) : ℝ :=
  ∫ u in Set.Icc (0 : ℝ) 1, grid μ s u

theorem label_measurable (s u : ℝ) : Measurable (label s u) :=
  ((measurable_id.div_const s).add_const u).floor

theorem label_joint_measurable (s : ℝ) : Measurable (fun ux : ℝ × ℝ => label s ux.1 ux.2) :=
  ((measurable_snd.div_const s).add measurable_fst).floor

theorem measurable_mass_label (μ : Measure ℝ) [IsFiniteMeasure μ] (s : ℝ) (b : ℤ) :
    Measurable (fun u => mass μ (label s u) b) := by
  have h := measurable_measure_prodMk_left (ν := μ)
    ((measurableSet_singleton b).preimage (label_joint_measurable s))
  exact h.ennreal_toReal

theorem measurable_grid (μ : Measure ℝ) [IsFiniteMeasure μ] (s : ℝ) :
    Measurable (grid μ s) :=
  Measurable.tsum (fun b => Real.continuous_negMulLog.measurable.comp (measurable_mass_label μ s b))

theorem label_in_interval {B s u x : ℝ} (hs : 0 < s) (hx : x ∈ Set.Icc (-B) B) :
    label s u x ∈ Finset.Icc ⌊-B/s+u⌋ ⌊B/s+u⌋ := by
  exact Finset.mem_Icc.mpr ⟨Int.floor_le_floor (by linarith [(div_le_div_iff_of_pos_right hs).mpr hx.1]),
    Int.floor_le_floor (by linarith [(div_le_div_iff_of_pos_right hs).mpr hx.2])⟩

theorem label_ae_finite (μ : Measure ℝ) {B s u : ℝ} (hs : 0 < s)
    (hB : μ (Set.Icc (-B) B)ᶜ = 0) :
    ∀ᵐ x ∂μ, label s u x ∈ Finset.Icc ⌊-B/s+u⌋ ⌊B/s+u⌋ := by
  have hb : ∀ᵐ x ∂μ, x ∈ Set.Icc (-B) B := ae_iff.mpr hB
  exact hb.mono (fun _ hx => label_in_interval hs hx)

theorem grid_eq_sum (μ : Measure ℝ) {B s u : ℝ} (hs : 0 < s)
    (hB : μ (Set.Icc (-B) B)ᶜ = 0) :
    grid μ s u = ∑ b ∈ Finset.Icc ⌊-B/s+u⌋ ⌊B/s+u⌋,
      Real.negMulLog (mass μ (label s u) b) :=
  entropy_eq_sum μ _ _ (label_ae_finite μ hs hB)

theorem label_ae_uniform (μ : Measure ℝ) {B s u : ℝ} (hs : 0 < s)
    (hB : μ (Set.Icc (-B) B)ᶜ = 0) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᵐ x ∂μ, label s u x ∈ Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋ := by
  filter_upwards [label_ae_finite μ hs hB] with x hx
  obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hx
  exact Finset.mem_Icc.mpr ⟨(Int.floor_le_floor (by linarith [hu.1] : -B/s ≤ -B/s+u)).trans hlo,
    hhi.trans (Int.floor_le_floor (by linarith [hu.2] : B/s+u ≤ B/s+1))⟩

theorem grid_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ] (s u : ℝ) : 0 ≤ grid μ s u :=
  entropy_nonneg μ _

theorem grid_le_card (μ : Measure ℝ) [IsProbabilityMeasure μ] {B s u : ℝ} (hs : 0 < s)
    (hB : μ (Set.Icc (-B) B)ᶜ = 0) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    grid μ s u ≤ (Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋).card := by
  rw [grid, entropy_eq_sum μ _ _ (label_ae_uniform μ hs hB hu)]
  calc
    _ ≤ ∑ b ∈ Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro b _
      exact (Real.negMulLog_le_one_sub_self (mass_nonneg μ _ b)).trans
        (sub_le_self _ (mass_nonneg μ _ b))
    _ = _ := by simp

theorem grid_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    {s : ℝ} (hs : 0 < s) : Integrable (grid μ s) (volume.restrict (Set.Icc 0 1)) := by
  obtain ⟨B,_,hB⟩ := hμ
  apply (integrable_const ((Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋).card : ℝ)).mono'
    (measurable_grid μ s).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (grid_nonneg μ s u)]
  exact grid_le_card μ hs hB hu

theorem averaged_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : ℝ) :
    0 ≤ averaged μ s := integral_nonneg (fun _ => grid_nonneg μ s _)

theorem mass_comp {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [DecidableEq γ]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → β) (hf : Measurable f)
    (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) (g : β → γ) (c : γ) :
    mass μ (g ∘ f) c = FiniteEntropy.mass s (mass μ f) g c := by
  classical
  let t := s.filter (fun b => g b = c)
  have hd : (↑t : Set β).PairwiseDisjoint (fun b => {x | f x = b}) := by
    intro b _ d _ hbd
    exact Set.disjoint_left.mpr (fun _ hx hy => hbd (hx.symm.trans hy))
  have he : {x | g (f x) = c} =ᵐ[μ] ⋃ b ∈ t, {x | f x = b} := by
    filter_upwards [hs] with x hx
    apply propext
    change (g (f x) = c) ↔ x ∈ ⋃ b ∈ t, {x | f x = b}
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨f x,Finset.mem_filter.mpr ⟨hx,h⟩,rfl⟩
    · rintro ⟨b,hb,he⟩
      exact he ▸ (Finset.mem_filter.mp hb).2
  unfold mass
  change μ.real {x | g (f x) = c} = _
  rw [measureReal_congr he, measureReal_biUnion_finset hd]
  · rfl
  · intro b _
    exact (measurableSet_singleton b).preimage hf

theorem entropy_comp {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [DecidableEq γ]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → β) (hf : Measurable f)
    (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) (g : β → γ) :
    entropy μ (g ∘ f) = FiniteEntropy.observableEntropy s (mass μ f) g := by
  classical
  rw [entropy_eq_sum μ (g ∘ f) (s.image g) (hs.mono (fun _ hx => Finset.mem_image_of_mem g hx))]
  exact Finset.sum_congr rfl (fun b _ => congrArg Real.negMulLog (mass_comp μ f hf s hs g b))

theorem entropy_comp_injective {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [DecidableEq γ] [Nonempty β] [Nonempty γ]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → β) (hf : Measurable f)
    (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) (g : β → γ) (hg : Function.Injective g) :
    entropy μ (g ∘ f) = entropy μ f := by
  rw [entropy_comp μ f hf s hs g, FiniteEntropy.observableEntropy_of_injective s _ g
    (fun b _ => mass_nonneg μ f b) hg, entropy_eq_sum μ f s hs]
  rfl

theorem mass_map {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (μ : Measure α) (f : α → β) (hf : Measurable f) (g : β → γ) (hg : Measurable g) (c : γ) :
    mass (μ.map f) g c = mass μ (g ∘ f) c := by
  unfold mass Measure.real
  change ((μ.map f) (g ⁻¹' {c})).toReal = _
  rw [Measure.map_apply hf ((measurableSet_singleton c).preimage hg)]
  rfl

theorem entropy_map {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (μ : Measure α) (f : α → β) (hf : Measurable f) (g : β → γ) (hg : Measurable g) :
    entropy (μ.map f) g = entropy μ (g ∘ f) := by
  exact tsum_congr (fun c => congrArg Real.negMulLog (mass_map μ f hf g hg c))

theorem grid_periodic (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) : Function.Periodic (grid μ s) 1 := by
  intro u
  obtain ⟨B,_,hB⟩ := hμ
  have he : label s (u+1) = (fun b : ℤ => b+1) ∘ label s u := by
    funext x
    simp only [label, Function.comp_apply]
    rw [← add_assoc, Int.floor_add_one]
  rw [grid, he, entropy_comp_injective μ (label s u) (label_measurable s u)
    _ (label_ae_finite μ hs hB) _ (add_left_injective 1)]
  rfl

theorem grid_translate (μ : Measure ℝ) (s u b : ℝ) :
    grid (μ.map (fun x => x+b)) s u = grid μ s (u+b/s) := by
  rw [grid, entropy_map μ (fun x => x+b) (measurable_id.add_const b) _ (label_measurable s u)]
  congr 1
  funext x
  simp only [Function.comp_apply, label, add_div]
  congr 1
  ring

theorem grid_scale_pos (μ : Measure ℝ) {a s : ℝ} (_ha : 0 < a) (u : ℝ) :
    grid (μ.map (fun x => a*x)) s u = grid μ (s/a) u := by
  rw [grid, entropy_map μ (fun x => a*x) (measurable_const.mul measurable_id) _ (label_measurable s u)]
  congr 1
  funext x
  simp only [Function.comp_apply, label]
  congr 2
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

theorem entropy_comp_le {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [DecidableEq γ]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → β) (hf : Measurable f)
    (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) (g : β → γ) :
    entropy μ (g ∘ f) ≤ entropy μ f := by
  rw [entropy_comp μ f hf s hs g, entropy_eq_sum μ f s hs]
  exact FiniteEntropy.observableEntropy_le s _ g (fun b _ => mass_nonneg μ f b)

theorem entropy_pair_le {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    [DecidableEq β] [DecidableEq γ]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → β) (hf : Measurable f)
    (g : α → γ) (hg : Measurable g) (s : Finset β) (t : Finset γ)
    (hs : ∀ᵐ x ∂μ, f x ∈ s) (ht : ∀ᵐ x ∂μ, g x ∈ t) :
    entropy μ (fun x => (f x,g x)) ≤ entropy μ f + entropy μ g := by
  classical
  let F := fun x => (f x,g x)
  have hF : Measurable F := hf.prodMk hg
  have hst : ∀ᵐ x ∂μ, F x ∈ s ×ˢ t := by
    filter_upwards [hs,ht] with x hx hy
    exact Finset.mem_product.mpr ⟨hx,hy⟩
  have h := FiniteEntropy.observableEntropy_pair_le (s ×ˢ t) (mass μ F) Prod.fst Prod.snd
    (fun b _ => mass_nonneg μ F b) (mass_sum μ F hF (s ×ˢ t) hst)
  have hid : (fun b : β × γ => (b.1,b.2)) = id := rfl
  rw [hid, FiniteEntropy.observableEntropy_id] at h
  have hfst := entropy_comp μ F hF (s ×ˢ t) hst Prod.fst
  have hsnd := entropy_comp μ F hF (s ×ˢ t) hst Prod.snd
  change entropy μ f = _ at hfst
  change entropy μ g = _ at hsnd
  rw [hfst, hsnd, entropy_eq_sum μ F (s ×ˢ t) hst]
  exact h

theorem averaged_eq_intervalIntegral (μ : Measure ℝ) (s : ℝ) :
    averaged μ s = ∫ u in (0 : ℝ)..1, grid μ s u := by
  rw [averaged, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le zero_le_one]

theorem grid_intervalIntegrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (a b : ℝ) :
    IntervalIntegrable (grid μ s) volume a b := by
  apply (grid_periodic μ hμ hs).intervalIntegrable₀ one_ne_zero
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr (grid_integrable μ hμ hs)

theorem averaged_translate (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (b : ℝ) :
    averaged (μ.map (fun x => x+b)) s = averaged μ s := by
  simp only [averaged_eq_intervalIntegral, grid_translate]
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_comm (1 : ℝ)] using
    (grid_periodic μ hμ hs).intervalIntegral_add_eq (b/s) 0

theorem averaged_scale_pos (μ : Measure ℝ) {a s : ℝ} (ha : 0 < a) :
    averaged (μ.map (fun x => a*x)) s = averaged μ (s/a) := by
  unfold averaged
  exact integral_congr_ae (Filter.Eventually.of_forall (grid_scale_pos μ ha))

theorem averaged_grid_nsmul (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) :
    (∫ u in (0 : ℝ)..1, grid μ s ((N : ℝ)*u)) = averaged μ s := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [intervalIntegral.integral_comp_mul_left _ hNr, mul_zero, mul_one]
  have he := (grid_periodic μ hμ hs).intervalIntegral_add_zsmul_eq (N : ℤ) 0
    (grid_intervalIntegrable μ hμ hs)
  simp only [zsmul_eq_mul, zero_add, Int.cast_natCast, mul_one] at he
  rw [he, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hNr, one_mul, averaged_eq_intervalIntegral]

theorem label_nested (s u x : ℝ) {N : ℕ} (hN : 0 < N) :
    label ((N : ℝ)*s) u x = label s ((N : ℝ)*u) x / (N : ℤ) := by
  simp only [label]
  rw [← Int.floor_div_natCast]
  congr 1
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [add_div, mul_div_cancel_left₀ u hn]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem entropy_congr_ae {α : Type uα} {β : Type uβ} [MeasurableSpace α]
    (μ : Measure α) {f g : α → β} (h : f =ᵐ[μ] g) : entropy μ f = entropy μ g := by
  apply tsum_congr
  intro b
  congr 1
  apply measureReal_congr
  filter_upwards [h] with x hx
  exact congrArg (fun y => y = b) hx

theorem ae_label_reflect (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : ℝ) :
    ∀ᵐ u ∂volume, ∀ᵐ x ∂μ, label s (-u) (-x) = -label s u x - 1 := by
  have hm : MeasurableSet {ux : ℝ × ℝ | ux.2/s+ux.1 ∉ Set.range (Int.cast : ℤ → ℝ)} :=
    ((Set.countable_range (Int.cast : ℤ → ℝ)).measurableSet.preimage
      ((measurable_snd.div_const s).add measurable_fst)).compl
  have he : ∀ᵐ u ∂volume, ∀ᵐ x ∂μ, x/s+u ∉ Set.range (Int.cast : ℤ → ℝ) := by
    apply (Measure.ae_ae_comm hm).mpr
    apply Filter.Eventually.of_forall
    intro x
    have h := (Set.countable_range (fun n : ℤ => (n : ℝ)-x/s)).ae_notMem volume
    filter_upwards [h] with u hu
    rintro ⟨n,hn⟩
    apply hu
    exact ⟨n,by linarith⟩
  filter_upwards [he] with u hu
  filter_upwards [hu] with x hx
  unfold label
  rw [neg_div, ← neg_add, Int.floor_neg, (Int.ceil_eq_floor_add_one_iff_notMem _).mpr hx]
  omega

theorem grid_reflect_ae (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) :
    (fun u => grid (μ.map Neg.neg) s (-u)) =ᵐ[volume] grid μ s := by
  filter_upwards [ae_label_reflect μ s] with u hu
  obtain ⟨B,_,hB⟩ := hμ
  rw [grid, entropy_map μ Neg.neg measurable_neg _ (label_measurable s (-u))]
  have hh : (label s (-u) ∘ Neg.neg) =ᵐ[μ] (fun b : ℤ => -b-1) ∘ label s u := hu
  rw [entropy_congr_ae μ hh, entropy_comp_injective μ (label s u)
    (label_measurable s u) _ (label_ae_finite μ hs hB) (fun b : ℤ => -b-1)]
  · rfl
  · intro a b hab
    change -a-1 = -b-1 at hab
    omega

theorem averaged_reflect (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) :
    averaged (μ.map Neg.neg) s = averaged μ s := by
  rw [averaged_eq_intervalIntegral, averaged_eq_intervalIntegral]
  have he := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 0)
    (grid (μ.map Neg.neg) s)
  simp only [neg_zero, neg_neg] at he
  rw [← he]
  calc
    _ = ∫ u in (-1 : ℝ)..0, grid μ s u := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [grid_reflect_ae μ hμ hs] with u hu
      exact fun _ => hu
    _ = _ := by simpa only [neg_add_cancel, zero_add] using
      (grid_periodic μ hμ hs).intervalIntegral_add_eq (-1) 0

theorem CompactlyCarried.map_affine {μ : Measure ℝ} (hμ : CompactlyCarried μ) (a b : ℝ) :
    CompactlyCarried (μ.map (fun x => a*x+b)) := by
  obtain ⟨B,hB,hμB⟩ := hμ
  let C := |a| * B + |b|
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  rw [Measure.map_apply (f := fun x : ℝ => a*x+b) (by fun_prop) measurableSet_Icc.compl]
  apply measure_mono_null _ hμB
  intro x hx hxin
  apply hx
  have hxb : |x| ≤ B := abs_le.mpr hxin
  have hax : |a*x+b| ≤ C := (abs_add_le _ _).trans (by
    rw [abs_mul]
    exact add_le_add_left (mul_le_mul_of_nonneg_left hxb (abs_nonneg a)) _)
  exact abs_le.mp hax

theorem averaged_scale (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s a : ℝ} (hs : 0 < s) (ha : a ≠ 0) :
    averaged (μ.map (fun x => a*x)) s = averaged μ (s/|a|) := by
  rcases ha.lt_or_gt with ha | ha
  · have hn : 0 < -a := neg_pos.mpr ha
    have hp : IsProbabilityMeasure (μ.map Neg.neg) := (Measure.isProbabilityMeasure_map_iff measurable_neg.aemeasurable).2 inferInstance
    let := hp
    have hc : CompactlyCarried (μ.map Neg.neg) := by
      convert hμ.map_affine (-1) 0 using 1; simp
    have hm : μ.map (fun x => a*x) = (μ.map Neg.neg).map (fun x => (-a)*x) := by
      rw [Measure.map_map (g := fun x : ℝ => (-a)*x) (by fun_prop) measurable_neg]
      congr 1
      funext x
      simp only [Function.comp_apply, neg_mul_neg]
    rw [hm, averaged_scale_pos _ hn, averaged_reflect μ hμ (div_pos hs hn), abs_of_neg ha]
  · rw [averaged_scale_pos μ ha, abs_of_pos ha]

theorem averaged_affine (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s a : ℝ} (hs : 0 < s) (ha : a ≠ 0) (b : ℝ) :
    averaged (μ.map (fun x => a*x+b)) s = averaged μ (s/|a|) := by
  have hp : IsProbabilityMeasure (μ.map (fun x => a*x)) := (Measure.isProbabilityMeasure_map_iff (measurable_const.mul measurable_id).aemeasurable).2 inferInstance
  let := hp
  have hc : CompactlyCarried (μ.map (fun x => a*x)) := by
    simpa only [add_zero] using hμ.map_affine a 0
  have he : μ.map (fun x => a*x+b) = (μ.map (fun x => a*x)).map (fun x => x+b) := by
    rw [Measure.map_map (g := fun x : ℝ => x+b) (f := fun x : ℝ => a*x) (by fun_prop) (by fun_prop)]
    rfl
  rw [he, averaged_translate _ hc hs b, averaged_scale μ hμ hs ha]

theorem entropy_le_add_of_reconstruct {α : Type uα} {β : Type uβ} {γ : Type uγ} {δ : Type uδ} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSingletonClass β]
    [MeasurableSingletonClass γ] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → δ) (g : α → β) (h : α → γ)
    (hg : Measurable g) (hh : Measurable h) (s : Finset β) (t : Finset γ)
    (hs : ∀ᵐ x ∂μ, g x ∈ s) (ht : ∀ᵐ x ∂μ, h x ∈ t)
    (q : β × γ → δ) (hq : ∀ᵐ x ∂μ, f x = q (g x,h x)) :
    entropy μ f ≤ entropy μ g + entropy μ h := by
  have hst : ∀ᵐ x ∂μ, (g x,h x) ∈ s ×ˢ t := by
    filter_upwards [hs,ht] with x hx hy
    exact Finset.mem_product.mpr ⟨hx,hy⟩
  calc
    entropy μ f = entropy μ (q ∘ fun x => (g x,h x)) := entropy_congr_ae μ hq
    _ ≤ entropy μ (fun x => (g x,h x)) := entropy_comp_le μ _ (hg.prodMk hh) _ hst q
    _ ≤ entropy μ g + entropy μ h := entropy_pair_le μ g hg h hh s t hs ht

theorem entropy_le_log_card {α : Type uα} {β : Type uβ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → β) (hf : Measurable f) (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) :
    entropy μ f ≤ Real.log s.card := by
  rw [entropy_eq_sum μ f s hs]
  exact FiniteEntropy.entropy_le_log_card s _ (fun b _ => mass_nonneg μ f b)
    (mass_sum μ f hf s hs)

theorem floor_relative_bounds {a z b : ℝ} (ha : 0 < a) (hz : 0 ≤ z) (hz' : z < 1) :
    ⌊b+a*z⌋-⌊b⌋ ∈ Finset.Icc (0 : ℤ) ⌈a⌉ := by
  apply Finset.mem_Icc.mpr
  constructor
  · have h := Int.floor_le_floor (show b ≤ b+a*z by nlinarith)
    omega
  · have hlt : b+a*z < ((⌊b⌋+⌈a⌉+1 : ℤ) : ℝ) := by
      push_cast
      nlinarith [Int.lt_floor_add_one b, Int.le_ceil a]
    have hh := Int.floor_lt.mpr hlt
    omega

noncomputable def relativeLabel (s t u v x : ℝ) : ℤ :=
  label s u x - ⌊(t/s)*(label t v x : ℝ)+u-(t/s)*v⌋

theorem relativeLabel_measurable (s t u v : ℝ) : Measurable (relativeLabel s t u v) := by
  unfold relativeLabel
  exact (label_measurable s u).sub
    (((((measurable_of_countable (fun n : ℤ => (n : ℝ))).comp (label_measurable t v)).const_mul (t/s)).add_const u).sub_const ((t/s)*v)).floor

theorem relativeLabel_mem {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (u v x : ℝ) :
    relativeLabel s t u v x ∈ Finset.Icc (0 : ℤ) ⌈t/s⌉ := by
  let z := x/t+v-(label t v x : ℝ)
  have hz : 0 ≤ z := sub_nonneg.mpr (Int.floor_le _)
  have hz' : z < 1 := by
    change x/t+v-(⌊x/t+v⌋ : ℝ) < 1
    linarith [Int.lt_floor_add_one (x/t+v)]
  have he : (t/s)*(label t v x : ℝ)+u-(t/s)*v+(t/s)*z = x/s+u := by
    dsimp [z]
    field_simp; ring
  have h := floor_relative_bounds (b := (t/s)*(label t v x : ℝ)+u-(t/s)*v)
    (div_pos ht hs) hz hz'
  rw [he] at h
  exact h

theorem grid_le_grid_add_log (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (u v : ℝ) :
    grid μ s u ≤ grid μ t v + Real.log (⌈t/s⌉+1 : ℝ) := by
  obtain ⟨B,_,hB⟩ := hμ
  have hrel : ∀ᵐ x ∂μ, relativeLabel s t u v x ∈ Finset.Icc (0 : ℤ) ⌈t/s⌉ :=
    Filter.Eventually.of_forall (relativeLabel_mem hs ht u v)
  have he := entropy_le_add_of_reconstruct μ (label s u) (label t v) (relativeLabel s t u v)
    (label_measurable t v) (relativeLabel_measurable s t u v) _ _
    (label_ae_finite μ ht hB) hrel
    (fun p : ℤ × ℤ => ⌊(t/s)*(p.1 : ℝ)+u-(t/s)*v⌋+p.2)
    (Filter.Eventually.of_forall (fun x => by dsimp [relativeLabel]; omega))
  have hc := entropy_le_log_card μ _ (relativeLabel_measurable s t u v) _ hrel
  have hn : 0 ≤ ⌈t/s⌉+1 := by have hh := (Int.ceil_pos.mpr (div_pos ht hs)); omega
  have hcard : ((Finset.Icc (0 : ℤ) ⌈t/s⌉).card : ℝ) = (⌈t/s⌉ : ℝ)+1 := by
    rw [Int.card_Icc]
    have he := congrArg (fun k : ℤ => (k : ℝ)) (Int.toNat_of_nonneg hn)
    simpa only [sub_zero, Int.cast_natCast, Int.cast_add, Int.cast_one] using he
  rw [hcard] at hc
  exact he.trans (add_le_add_right hc _)

theorem grid_le_grid_add_log_two (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hts : t ≤ s) (u v : ℝ) :
    grid μ s u ≤ grid μ t v + Real.log 2 := by
  have hc : ⌈t/s⌉ = (1 : ℤ) := by
    have hh := Int.ceil_pos.mpr (div_pos ht hs)
    have hu : ⌈t/s⌉ ≤ (1 : ℤ) := Int.ceil_le.mpr (by
      norm_num
      exact (div_le_one hs).mpr hts)
    omega
  simpa only [hc, Int.cast_one, one_add_one_eq_two] using grid_le_grid_add_log μ hμ hs ht u v

theorem grid_le_grid_add_log_ratio (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (u v : ℝ) :
    grid μ s u ≤ grid μ t v + Real.log (t/s+2) := by
  have hc : (0 : ℝ) < (⌈t/s⌉ : ℝ)+1 := by
    have hh := Int.le_ceil (t/s)
    linarith [div_pos ht hs]
  have hu : (⌈t/s⌉ : ℝ)+1 ≤ t/s+2 := by linarith [Int.ceil_lt_add_one (t/s)]
  exact (grid_le_grid_add_log μ hμ hs ht u v).trans
    (add_le_add_right (Real.log_le_log hc hu) _)

theorem averaged_le_averaged_add_log_two (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hts : t ≤ s) :
    averaged μ s ≤ averaged μ t + Real.log 2 := by
  have hi := (grid_integrable μ hμ ht).add (integrable_const (Real.log 2))
  have hh := integral_mono_ae (grid_integrable μ hμ hs) hi
    (Filter.Eventually.of_forall (fun u => grid_le_grid_add_log_two μ hμ hs ht hts u u))
  simp only [Pi.add_apply] at hh
  rw [integral_add (grid_integrable μ hμ ht) (integrable_const _)] at hh
  simpa [averaged, integral_const, Measure.real_def] using hh

theorem averaged_le_averaged_add_log_ratio (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    averaged μ s ≤ averaged μ t + Real.log (t/s+2) := by
  have hi := (grid_integrable μ hμ ht).add (integrable_const (Real.log (t/s+2)))
  have hh := integral_mono_ae (grid_integrable μ hμ hs) hi
    (Filter.Eventually.of_forall (fun u => grid_le_grid_add_log_ratio μ hμ hs ht u u))
  simp only [Pi.add_apply] at hh
  rw [integral_add (grid_integrable μ hμ ht) (integrable_const _)] at hh
  simpa [averaged, integral_const, Measure.real_def] using hh

theorem nested_grid_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) (u : ℝ) :
    0 ≤ grid μ s ((N : ℝ)*u)-grid μ ((N : ℝ)*s) u ∧
      grid μ s ((N : ℝ)*u)-grid μ ((N : ℝ)*s) u ≤ Real.log N := by
  classical
  obtain ⟨B,_,hB⟩ := hμ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNz : (0 : ℤ) < N := by exact_mod_cast hN
  let f := label s ((N : ℝ)*u)
  let g := label ((N : ℝ)*s) u
  have hf := label_ae_finite (u := (N : ℝ)*u) μ hs hB
  have hg := label_ae_finite (u := u) μ (mul_pos hNr hs) hB
  have hfg : g = (fun z : ℤ => z/(N : ℤ)) ∘ f := by
    funext x
    exact label_nested s u x hN
  have hlow := entropy_comp_le μ f (label_measurable _ _) _ hf (fun z : ℤ => z/(N : ℤ))
  rw [← hfg] at hlow
  have hm : Measurable (fun x => f x % (N : ℤ)) :=
    (measurable_of_countable (fun z : ℤ => z % (N : ℤ))).comp (label_measurable _ _)
  have hr : ∀ᵐ x ∂μ, f x % (N : ℤ) ∈ Finset.Ico (0 : ℤ) (N : ℤ) := by
    apply Filter.Eventually.of_forall
    intro x
    exact Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ hNz.ne', Int.emod_lt_of_pos _ hNz⟩
  have hh := entropy_le_add_of_reconstruct μ f g (fun x => f x%(N : ℤ))
    (label_measurable _ _) hm _ _ hg hr
    (fun p : ℤ × ℤ => p.1*(N : ℤ)+p.2) (Filter.Eventually.of_forall (fun x => by
      rw [hfg]
      exact (Int.ediv_mul_add_emod (f x) N).symm))
  have her := entropy_le_log_card μ _ hm _ hr
  simp only [Int.card_Ico, sub_zero, Int.toNat_natCast] at her
  change entropy μ f ≤ entropy μ g + entropy μ (fun x => f x%(N : ℤ)) at hh
  change 0 ≤ entropy μ f-entropy μ g ∧ entropy μ f-entropy μ g ≤ Real.log N
  constructor <;> linarith

theorem averaged_nested_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) :
    0 ≤ averaged μ s-averaged μ ((N : ℝ)*s) ∧
      averaged μ s-averaged μ ((N : ℝ)*s) ≤ Real.log N := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hf : IntervalIntegrable (fun u => grid μ s ((N : ℝ)*u)) volume 0 1 := by
    simpa only [zero_div, div_self hNr] using
      (grid_intervalIntegrable μ hμ hs 0 (N : ℝ)).comp_mul_left (c := (N : ℝ))
  have hc := grid_intervalIntegrable μ hμ (mul_pos hpos hs) 0 1
  have hi := hf.sub hc
  have hge := intervalIntegral.integral_mono zero_le_one (intervalIntegrable_const (c := (0 : ℝ))) hi
    (fun u => (nested_grid_bounds μ hμ hs hN u).1)
  have hle := intervalIntegral.integral_mono zero_le_one hi
    (intervalIntegrable_const (c := Real.log N)) (fun u => (nested_grid_bounds μ hμ hs hN u).2)
  rw [intervalIntegral.integral_sub hf hc, averaged_grid_nsmul μ hμ hs hN,
    ← averaged_eq_intervalIntegral] at hge hle
  simpa only [intervalIntegral.integral_const, sub_zero, one_smul] using And.intro hge hle

theorem mass_mixture {ι : Type uι} {α : Type uα} {β : Type uβ} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) (ν : ι → Measure α) [∀ i, IsFiniteMeasure (ν i)] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hm : μ = ∑ i, ENNReal.ofReal (w i) • ν i) (f : α → β) (b : β) :
    mass μ f b = ∑ i, w i*mass (ν i) f b := by
  unfold mass
  rw [hm]
  simp only [Measure.real_def, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul]
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hw i)]

theorem entropy_coarsening_mixture {ι : Type uι} {α : Type uα} {β : Type uβ} {γ : Type uγ} [Fintype ι]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass β]
    [DecidableEq β] [DecidableEq γ]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : ι → Measure α)
    [∀ i, IsProbabilityMeasure (ν i)] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : μ = ∑ i, ENNReal.ofReal (w i) • ν i)
    (f : α → β) (hf : Measurable f) (s : Finset β)
    (hs : ∀ᵐ x ∂μ, f x ∈ s) (hsi : ∀ i, ∀ᵐ x ∂ν i, f x ∈ s) (g : β → γ) :
    (∑ i, w i*(entropy (ν i) f-entropy (ν i) (g ∘ f))) ≤
      entropy μ f-entropy μ (g ∘ f) := by
  classical
  have hh := FiniteEntropy.conditionalEntropy_mixture Finset.univ s w
    (fun i => mass (ν i) f) id g (fun i _ => hw i)
    (fun i _ b _ => mass_nonneg (ν i) f b) (fun i _ => mass_sum (ν i) f hf s (hsi i))
  have he : (fun b => ∑ i, w i*mass (ν i) f b) = mass μ f :=
    funext (fun b => (mass_mixture μ ν w hw hm f b).symm)
  rw [he, FiniteEntropy.conditionalEntropy_id _ _ _ (fun b _ => mass_nonneg μ f b)] at hh
  have hi : ∀ i, FiniteEntropy.conditionalEntropy s (mass (ν i) f) id g =
      entropy (ν i) f-entropy (ν i) (g ∘ f) := by
    intro i
    rw [FiniteEntropy.conditionalEntropy_id _ _ _ (fun b _ => mass_nonneg (ν i) f b),
      ← entropy_comp (ν i) f hf s (hsi i) g, entropy_eq_sum (ν i) f s (hsi i)]
    rfl
  simp_rw [hi] at hh
  rw [← entropy_comp μ f hf s hs g] at hh
  rw [entropy_eq_sum μ f s hs]
  exact hh

theorem nested_grid_mixture {ι : Type uι} [Fintype ι]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, CompactlyCarried (ν i)) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : μ = ∑ i, ENNReal.ofReal (w i) • ν i)
    {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) (u : ℝ) :
    (∑ i, w i*(grid (ν i) s ((N : ℝ)*u)-grid (ν i) ((N : ℝ)*s) u)) ≤
      grid μ s ((N : ℝ)*u)-grid μ ((N : ℝ)*s) u := by
  classical
  obtain ⟨B,_,hB⟩ := hμ
  choose C hC hCi using hν
  let v := (N : ℝ)*u
  let a := Finset.Icc ⌊-B/s+v⌋ ⌊B/s+v⌋
  let ai := fun i => Finset.Icc ⌊-C i/s+v⌋ ⌊C i/s+v⌋
  let A := a ∪ Finset.univ.biUnion ai
  have ha : ∀ᵐ x ∂μ, label s v x ∈ A := (label_ae_finite μ hs hB).mono (fun x hx =>
    Finset.mem_union_left _ hx)
  have hai : ∀ i, ∀ᵐ x ∂ν i, label s v x ∈ A := by
    intro i
    filter_upwards [label_ae_finite (u := v) (ν i) hs (hCi i)] with x hx
    exact Finset.mem_union_right a (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩)
  have hh := entropy_coarsening_mixture μ ν w hw hm (label s v) (label_measurable s v)
    A ha hai (fun z : ℤ => z/(N : ℤ))
  have he : (fun z : ℤ => z/(N : ℤ)) ∘ label s v = label ((N : ℝ)*s) u := by
    funext x
    exact (label_nested s u x hN).symm
  rw [he] at hh
  exact hh

theorem grid_nsmul_intervalIntegrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) :
    IntervalIntegrable (fun u => grid μ s ((N : ℝ)*u)) volume 0 1 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simpa only [zero_div, div_self hn] using
    (grid_intervalIntegrable μ hμ hs 0 (N : ℝ)).comp_mul_left (c := (N : ℝ))

theorem averaged_nested_mixture {ι : Type uι} [Fintype ι]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, CompactlyCarried (ν i)) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : μ = ∑ i, ENNReal.ofReal (w i) • ν i)
    {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) :
    (∑ i, w i*(averaged (ν i) s-averaged (ν i) ((N : ℝ)*s))) ≤
      averaged μ s-averaged μ ((N : ℝ)*s) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hi := fun i => (grid_nsmul_intervalIntegrable (ν i) (hν i) hs hN).sub
    (grid_intervalIntegrable (ν i) (hν i) (mul_pos hn hs) 0 1)
  have hf := (grid_nsmul_intervalIntegrable μ hμ hs hN).sub
    (grid_intervalIntegrable μ hμ (mul_pos hn hs) 0 1)
  have hh := intervalIntegral.integral_mono zero_le_one (IntervalIntegrable.sum Finset.univ
    (fun i (_ : i ∈ Finset.univ) => (hi i).const_mul (w i))) hf
      (fun u => by
        simpa only [Finset.sum_apply] using nested_grid_mixture μ hμ ν hν w hw hm hs hN u)
  simp only [Finset.sum_apply] at hh
  rw [intervalIntegral.integral_finsetSum (fun i (_ : i ∈ Finset.univ) => (hi i).const_mul (w i))] at hh
  simp_rw [intervalIntegral.integral_const_mul] at hh
  simp_rw [intervalIntegral.integral_sub (grid_nsmul_intervalIntegrable (ν _) (hν _) hs hN)
    (grid_intervalIntegrable (ν _) (hν _) (mul_pos hn hs) 0 1),
    averaged_grid_nsmul (ν _) (hν _) hs hN, ← averaged_eq_intervalIntegral] at hh
  rw [intervalIntegral.integral_sub (grid_nsmul_intervalIntegrable μ hμ hs hN)
    (grid_intervalIntegrable μ hμ (mul_pos hn hs) 0 1),
    averaged_grid_nsmul μ hμ hs hN, ← averaged_eq_intervalIntegral] at hh
  exact hh

theorem CompactlyCarried.mixture {ι : Type uι} [Fintype ι]
    (ν : ι → Measure ℝ) (hν : ∀ i, CompactlyCarried (ν i)) (w : ι → ℝ) :
    CompactlyCarried (∑ i, ENNReal.ofReal (w i) • ν i) := by
  classical
  choose C hC hCi using hν
  let B := ∑ i, C i
  have hi : ∀ i, C i ≤ B := fun i => Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
  refine ⟨B, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i _
  have hz : ν i (Set.Icc (-B) B)ᶜ = 0 := measure_mono_null (by
    intro x hx hxin
    exact hx ⟨by linarith [hxin.1,hi i],by linarith [hxin.2,hi i]⟩) (hCi i)
  rw [hz, mul_zero]

theorem mixture_probability {ι : Type uι} {α : Type uα} [Fintype ι] [MeasurableSpace α]
    (ν : ι → Measure α) [∀ i, IsProbabilityMeasure (ν i)] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1) :
    IsProbabilityMeasure (∑ i, ENNReal.ofReal (w i) • ν i) := by
  constructor
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i), hw1, ENNReal.ofReal_one]

theorem averaged_nested_translate_mixture {ι : Type uι} [Fintype ι]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1) (b : ι → ℝ)
    {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) :
    averaged μ s-averaged μ ((N : ℝ)*s) ≤
      averaged (∑ i, ENNReal.ofReal (w i) • μ.map (fun x => x+b i)) s-
      averaged (∑ i, ENNReal.ofReal (w i) • μ.map (fun x => x+b i)) ((N : ℝ)*s) := by
  let ν := fun i => μ.map (fun x => x+b i)
  have hp : ∀ i, IsProbabilityMeasure (ν i) := fun i =>
    (Measure.isProbabilityMeasure_map_iff (measurable_id.add_const (b i)).aemeasurable).2 inferInstance
  let := hp
  have hc : ∀ i, CompactlyCarried (ν i) := fun i => by
    simpa only [one_mul] using hμ.map_affine 1 (b i)
  let ρ := ∑ i, ENNReal.ofReal (w i) • ν i
  have hpρ := mixture_probability ν w hw hw1
  let := hpρ
  have hh := averaged_nested_mixture ρ (CompactlyCarried.mixture ν hc w) ν hc w hw rfl hs hN
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have he : ∀ i, averaged (ν i) s-averaged (ν i) ((N : ℝ)*s) =
      averaged μ s-averaged μ ((N : ℝ)*s) := by
    intro i
    rw [averaged_translate μ hμ hs, averaged_translate μ hμ (mul_pos hn hs)]
  simp_rw [he] at hh
  simpa only [← Finset.sum_mul, hw1, one_mul] using hh

theorem entropy_summable {α : Type uα} {β : Type uβ} [MeasurableSpace α] (μ : Measure α)
    (f : α → β) (a : Finset β) (ha : ∀ᵐ x ∂μ, f x ∈ a) :
    Summable (fun b => Real.negMulLog (mass μ f b)) := by
  apply summable_of_ne_finset_zero (s := a)
  intro b hb
  simp only [mass_eq_zero_of_ae μ f a ha hb, Real.negMulLog_zero]

theorem mass_summable {α : Type uα} {β : Type uβ} [MeasurableSpace α] (μ : Measure α)
    (f : α → β) (a : Finset β) (ha : ∀ᵐ x ∂μ, f x ∈ a) :
    Summable (mass μ f) := by
  apply summable_of_ne_finset_zero (s := a)
  exact fun b hb => mass_eq_zero_of_ae μ f a ha hb

theorem mass_tsum {α : Type uα} {β : Type uβ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → β) (hf : Measurable f) (a : Finset β) (ha : ∀ᵐ x ∂μ, f x ∈ a) :
    ∑' b, mass μ f b = 1 := by
  rw [tsum_eq_sum (fun b hb => mass_eq_zero_of_ae μ f a ha hb)]
  exact mass_sum μ f hf a ha

noncomputable def fairShift (μ : Measure ℝ) (v : ℝ) : Measure ℝ :=
  ∑ i : Fin 2, ENNReal.ofReal (1/2 : ℝ) • μ.map (fun x => x+(i : ℝ)*v)

theorem fairShift_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] (v : ℝ) :
    IsProbabilityMeasure (fairShift μ v) := by
  let ν := fun i : Fin 2 => μ.map (fun x => x+(i : ℝ)*v)
  have : ∀ i, IsProbabilityMeasure (ν i) := fun i =>
    (Measure.isProbabilityMeasure_map_iff (measurable_id.add_const _).aemeasurable).2 inferInstance
  let := this
  exact mixture_probability ν (fun _ => 1/2) (by intro; positivity) (by norm_num [Fin.sum_univ_two])

theorem CompactlyCarried.fairShift {μ : Measure ℝ} (hμ : CompactlyCarried μ) (v : ℝ) :
    CompactlyCarried (fairShift μ v) := by
  apply CompactlyCarried.mixture
  intro i
  simpa only [one_mul] using hμ.map_affine 1 ((i : ℝ)*v)

theorem label_add_scale {s : ℝ} (hs : s ≠ 0) (u x : ℝ) :
    label s u (x+s) = label s u x+1 := by
  dsimp only [label]
  rw [add_div, div_self hs]
  convert Int.floor_add_one (x/s+u) using 1
  congr 1
  ring

theorem mass_fairShift (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) (u : ℝ) (j : ℤ) :
    mass (fairShift μ s) (label s u) j =
      (mass μ (label s u) j+mass μ (label s u) (j-1))/2 := by
  have hi : ∀ i : Fin 2, IsProbabilityMeasure (μ.map (fun x => x+(i : ℝ)*s)) :=
    fun i => (Measure.isProbabilityMeasure_map_iff (measurable_id.add_const _).aemeasurable).2 inferInstance
  let := hi
  rw [mass_mixture (fairShift μ s) _ (fun _ : Fin 2 => 1/2) (by intro; positivity) rfl,
    Fin.sum_univ_two]
  simp only [Fin.val_zero, Nat.cast_zero, zero_mul, add_zero, Fin.val_one,
    Nat.cast_one, one_mul]
  rw [mass_map μ (fun x => x) measurable_id (label s u) (label_measurable s u),
    mass_map μ (fun x => x+s) (measurable_id.add_const s) (label s u) (label_measurable s u)]
  have he : mass μ ((label s u) ∘ (fun x => x+s)) j = mass μ (label s u) (j-1) := by
    unfold mass
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, Function.comp_apply, label_add_scale hs.ne']
    omega
  rw [he]
  change (1/2)*mass μ (label s u) j+(1/2)*mass μ (label s u) (j-1) = _
  ring

theorem mass_int_div_two {α : Type uα} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (f : α → ℤ) (hf : Measurable f) (k : ℤ) :
    mass μ (fun x => f x/2) k = mass μ f (2*k)+mass μ f (2*k+1) := by
  have he : {x | f x/2=k} = {x | f x=2*k} ∪ {x | f x=2*k+1} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    omega
  unfold mass
  rw [he]
  apply measureReal_union
  · exact Set.disjoint_left.mpr (by
      intro x hx hy
      simp only [Set.mem_ofPred_eq] at hx hy
      omega)
  · exact measurableSet_eq_fun hf measurable_const
  · exact measure_ne_top μ _
  · exact measure_ne_top μ _

theorem mass_nested_two (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (s u : ℝ) (k : ℤ) :
    mass μ (label (2*s) (u/2)) k =
      mass μ (label s u) (2*k)+mass μ (label s u) (2*k+1) := by
  have he : label (2*s) (u/2) = fun x => label s u x/2 := by
    funext x
    simpa only [Nat.cast_ofNat, show (2 : ℝ) * (u / 2) = u by ring] using
      label_nested s (u/2) x (by norm_num : 0 < (2 : ℕ))
  rw [he, mass_int_div_two μ _ (label_measurable s u)]

theorem mass_fairShift_odd (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) (u : ℝ) (k : ℤ) :
    mass (fairShift μ s) (label s u) (2*k+1) =
      mass μ (label (2*s) (u/2)) k/2 := by
  rw [mass_fairShift μ hs, mass_nested_two]
  simp only [add_sub_cancel_right]
  ring

theorem mass_fairShift_even (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) (u : ℝ) (k : ℤ) :
    mass (fairShift μ s) (label s u) (2*k) =
      mass μ (label (2*s) ((u+1)/2)) k/2 := by
  have he (j : ℤ) : mass μ (label s (u+1)) j = mass μ (label s u) (j-1) := by
    unfold mass label
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, ← add_assoc, Int.floor_add_one]
    omega
  rw [mass_fairShift μ hs, mass_nested_two, he, he]
  simp only [add_sub_cancel_right]
  ring

theorem entropy_half_mass {α : Type uα} {β : Type uβ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → β) (hf : Measurable f) (a : Finset β) (ha : ∀ᵐ x ∂μ, f x ∈ a) :
    (∑' b, Real.negMulLog (mass μ f b/2)) = entropy μ f/2+Real.log 2/2 := by
  have he (b : β) : Real.negMulLog (mass μ f b/2) =
      (1/2)*Real.negMulLog (mass μ f b)+Real.negMulLog (1/2)*mass μ f b := by
    rw [div_eq_mul_inv, Real.negMulLog_mul]
    ring_nf
  simp_rw [he]
  rw [((entropy_summable μ f a ha).mul_left (1/2)).tsum_add
    ((mass_summable μ f a ha).mul_left (Real.negMulLog (1/2))),
    tsum_mul_left, tsum_mul_left, mass_tsum μ f hf a ha]
  have hc : Real.negMulLog (1/2)=Real.log 2/2 := by
    change -(1/2 : ℝ)*Real.log (1/2)=_
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    ring
  rw [hc]
  change (1/2)*entropy μ f+(Real.log 2/2)*1 = _
  ring

theorem grid_fairShift (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (u : ℝ) :
    grid (fairShift μ s) s u = Real.log 2+
      (grid μ (2*s) (u/2)+grid μ (2*s) ((u+1)/2))/2 := by
  classical
  obtain ⟨B,hB,hBμ⟩ := (hμ.fairShift s)
  let F := fun j => Real.negMulLog (mass (fairShift μ s) (label s u) j)
  have hf : Summable F := entropy_summable (fairShift μ s) _ _ (label_ae_finite _ hs hBμ)
  have heven : Summable (fun k : ℤ => F (k*2)) := hf.comp_injective (i := fun k : ℤ => k*2) (by
    intro a b h
    change a*2=b*2 at h
    omega)
  have hodd : Summable (fun k : ℤ => F (k*2+1)) := hf.comp_injective (i := fun k : ℤ => k*2+1) (by
    intro a b h
    change a*2+1=b*2+1 at h
    omega)
  have hprod := ((Int.divModEquiv 2).symm.summable_iff).mpr hf
  change Summable (fun p => F ((Int.divModEquiv 2).symm p)) at hprod
  change (∑' j, F j) = _
  rw [← (Int.divModEquiv 2).symm.tsum_eq F, hprod.tsum_prod]
  simp only [tsum_fintype, Fin.sum_univ_two, Int.divModEquiv_symm_apply,
    Nat.cast_ofNat, Fin.val_zero, Nat.cast_zero, add_zero, Fin.val_one, Nat.cast_one]
  rw [heven.tsum_add hodd]
  dsimp only [F]
  simp_rw [show ∀ k : ℤ, k*2=2*k from fun k => mul_comm k 2,
    mass_fairShift_even μ hs, mass_fairShift_odd μ hs]
  obtain ⟨C,hC,hCμ⟩ := hμ
  rw [entropy_half_mass μ _ (label_measurable _ _) _
      (label_ae_finite μ (by linarith : 0 < 2*s) hCμ),
    entropy_half_mass μ _ (label_measurable _ _) _
      (label_ae_finite μ (by linarith : 0 < 2*s) hCμ)]
  change grid μ (2*s) ((u+1)/2)/2+Real.log 2/2+
    (grid μ (2*s) (u/2)/2+Real.log 2/2) = _
  ring

theorem averaged_fairShift (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) :
    averaged (fairShift μ s) s = averaged μ (2*s)+Real.log 2 := by
  have ht : 0 < 2*s := by linarith
  let f := grid μ (2*s)
  have hi0 : IntervalIntegrable (fun u => f (u/2)) volume 0 1 := by
    have h := (grid_intervalIntegrable μ hμ ht 0 (1/2)).comp_mul_left (c := (1/2 : ℝ))
    norm_num at h
    simpa only [f, div_eq_mul_inv, mul_comm, one_mul] using h
  have hi1 : IntervalIntegrable (fun u => f ((u+1)/2)) volume 0 1 := by
    have h := (grid_intervalIntegrable μ hμ ht (1/2) 1).comp_mul_left (c := (1/2 : ℝ))
    norm_num at h
    have hh := h.comp_add_right 1
    norm_num at hh
    simpa only [f, div_eq_mul_inv, mul_comm, one_mul] using hh
  have he0 : (∫ u in (0 : ℝ)..1, f (u/2)) = 2*(∫u in (0 : ℝ)..(1/2), f u) := by
    rw [intervalIntegral.integral_comp_div f (by norm_num : (2 : ℝ) ≠ 0)]
    simp only [zero_div, smul_eq_mul]
  have he1 : (∫ u in (0 : ℝ)..1, f ((u+1)/2)) = 2*(∫u in (1/2 : ℝ)..1, f u) := by
    rw [intervalIntegral.integral_comp_add_right (fun u => f (u/2)) 1]
    norm_num only [zero_add, one_add_one_eq_two]
    rw [intervalIntegral.integral_comp_div f (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num only [div_self (by norm_num : (2 : ℝ) ≠ 0), smul_eq_mul]
  rw [averaged_eq_intervalIntegral]
  calc
    _ = ∫u in (0 : ℝ)..1, Real.log 2+(f (u/2)+f ((u+1)/2))/2 := by
      apply intervalIntegral.integral_congr
      intro u _
      exact grid_fairShift μ hμ hs u
    _ = Real.log 2+(2*(∫u in (0 : ℝ)..(1/2), f u)+
        2*(∫u in (1/2 : ℝ)..1, f u))/2 := by
      rw [intervalIntegral.integral_add intervalIntegrable_const ((hi0.add hi1).div_const 2),
        intervalIntegral.integral_div, intervalIntegral.integral_add hi0 hi1, he0, he1]
      simp only [intervalIntegral.integral_const, sub_zero, one_smul]
    _ = averaged μ (2*s)+Real.log 2 := by
      have hh := intervalIntegral.integral_add_adjacent_intervals
        (grid_intervalIntegrable μ hμ ht 0 (1/2)) (grid_intervalIntegrable μ hμ ht (1/2) 1)
      change (∫u in (0 : ℝ)..(1/2), f u)+(∫u in (1/2 : ℝ)..1, f u) = _ at hh
      rw [← mul_add, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), hh,
        ← averaged_eq_intervalIntegral]
      ring

noncomputable def observationLaw {α : Type uα} {β : Type uβ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → β) (hf : Measurable f) (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) :
    FiniteDistribution β :=
  ⟨mass μ f,s,mass_nonneg μ f,fun _b hb => mass_eq_zero_of_ae μ f s hs hb,
    mass_sum μ f hf s hs⟩

noncomputable def gridLaw (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (u : ℝ) : FiniteDistribution ℤ :=
  observationLaw μ (label s u) (label_measurable s u)
    (Finset.Icc ⌊-hμ.choose/s+u⌋ ⌊hμ.choose/s+u⌋)
    (label_ae_finite μ hs hμ.choose_spec.2)

theorem gridLaw_weight (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (u : ℝ) :
    (gridLaw μ hμ hs u).weight=mass μ (label s u) := rfl

theorem gridLaw_entropy (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (u : ℝ) :
    (gridLaw μ hμ hs u).entropy=grid μ s u := rfl

noncomputable def gridDeficit (μ : Measure ℝ) (s u : ℝ) : ℝ :=
  grid (fairShift μ s) s u-grid μ s u

theorem gridDeficit_eq_js (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (u : ℝ) :
    gridDeficit μ s u=(gridLaw μ hμ hs u).js ((gridLaw μ hμ hs u).translate 1) := by
  let := fairShift_probability μ s
  let p := gridLaw μ hμ hs u
  have he : (p.mix (p.translate 1)).weight=(gridLaw (fairShift μ s) (hμ.fairShift s) hs u).weight := by
    funext b
    change (p.weight b+(p.translate 1).weight b)/2=mass (fairShift μ s) (label s u) b
    rw [FiniteDistribution.translate_weight, mass_fairShift μ hs]
    rfl
  have ht : (p.translate 1).entropy=p.entropy :=
    FiniteDistribution.entropy_map_injective p (fun a : ℤ => a+1) (add_left_injective 1)
  rw [FiniteDistribution.js, FiniteDistribution.entropy_congr _ _ he, ht]
  change grid (fairShift μ s) s u-grid μ s u=
    grid (fairShift μ s) s u-(grid μ s u+grid μ s u)/2
  ring

theorem gridDeficit_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (u : ℝ) :
    0 ≤ gridDeficit μ s u ∧ gridDeficit μ s u ≤ Real.log 2 := by
  rw [gridDeficit_eq_js μ hμ hs u]
  exact ⟨FiniteDistribution.js_nonneg _ _,FiniteDistribution.js_le_log_two _ _⟩

theorem gridLaw_coarsen_two (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (u : ℝ) :
    ((gridLaw μ hμ hs (2*u)).map (fun n : ℤ => n/2)).weight=
      (gridLaw μ hμ (mul_pos (by norm_num : (0 : ℝ)<2) hs) u).weight := by
  classical
  let : DecidableEq ℤ := fun _ _ => Classical.propDecidable _
  funext b
  rw [FiniteDistribution.map_weight_on _ _ _ (Finset.Subset.refl _)]
  change FiniteEntropy.mass (Finset.Icc ⌊-hμ.choose/s+2*u⌋ ⌊hμ.choose/s+2*u⌋) (mass μ (label s (2*u))) (fun n : ℤ => n/2) b=
    mass μ (label (2*s) u) b
  rw [← mass_comp μ (label s (2*u)) (label_measurable _ _) _
    (label_ae_finite μ hs hμ.choose_spec.2)]
  congr 1
  funext x
  symm
  simpa using label_nested s u x (by norm_num : 0 < (2 : ℕ))

theorem gridDeficit_double_sq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (u : ℝ) :
    (gridDeficit μ (2*s) u)^2 ≤ 8*(Real.log 2)^2*gridDeficit μ s (2*u) := by
  let p := gridLaw μ hμ hs (2*u)
  let q := gridLaw μ hμ (mul_pos (by norm_num : (0 : ℝ)<2) hs) u
  have he : (p.map (fun n => n/2)).weight=q.weight := gridLaw_coarsen_two μ hμ hs u
  have he' : ((p.translate 2).map (fun n => n/2)).weight=(q.translate 1).weight := by
    rw [FiniteDistribution.map_translate_div_two]
    funext b
    rw [FiniteDistribution.translate_weight, FiniteDistribution.translate_weight, he]
  have hh := FiniteDistribution.js_two_step_coarsen p (fun n => n/2)
  rw [FiniteDistribution.js_congr _ _ q (q.translate 1) he he'] at hh
  rw [gridDeficit_eq_js μ hμ (mul_pos (by norm_num : (0 : ℝ)<2) hs) u,
    gridDeficit_eq_js μ hμ hs (2*u)]
  exact hh

theorem gridDeficit_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) :
    Integrable (gridDeficit μ s) (volume.restrict (Set.Icc 0 1)) := by
  let := fairShift_probability μ s
  exact (grid_integrable (fairShift μ s) (hμ.fairShift s) hs).sub (grid_integrable μ hμ hs)

theorem integral_gridDeficit (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) :
    (∫ u in Set.Icc (0 : ℝ) 1, gridDeficit μ s u)=
      Real.log 2-(averaged μ s-averaged μ (2*s)) := by
  let := fairShift_probability μ s
  simp only [gridDeficit]
  rw [integral_sub (grid_integrable _ (hμ.fairShift s) hs) (grid_integrable μ hμ hs)]
  change averaged (fairShift μ s) s-averaged μ s=_
  rw [averaged_fairShift μ hμ hs]
  ring

noncomputable def deficit (μ : Measure ℝ) (s : ℝ) : ℝ :=
  Real.log 2-(averaged μ s-averaged μ (2*s))

theorem deficit_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) :
    0 ≤ deficit μ s ∧ deficit μ s ≤ Real.log 2 := by
  rw [deficit, ← integral_gridDeficit μ hμ hs]
  constructor
  · exact integral_nonneg (fun u => (gridDeficit_bounds μ hμ hs u).1)
  · have hh := integral_mono (gridDeficit_integrable μ hμ hs)
      (integrable_const (Real.log 2)) (fun u => (gridDeficit_bounds μ hμ hs u).2)
    simpa using hh

theorem gridDeficit_sq_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) :
    Integrable (fun u => (gridDeficit μ s u)^2) (volume.restrict (Set.Icc 0 1)) := by
  apply (integrable_const ((Real.log 2)^2)).mono'
    ((gridDeficit_integrable μ hμ hs).aestronglyMeasurable.pow 2)
  filter_upwards [] with u
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  obtain ⟨h0,h1⟩ := gridDeficit_bounds μ hμ hs u
  exact pow_le_pow_left₀ h0 h1 2

theorem integral_gridDeficit_double_shift (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) :
    (∫ u in Set.Icc (0 : ℝ) 1, gridDeficit μ s (2*u))=deficit μ s := by
  let := fairShift_probability μ s
  have hi (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : CompactlyCarried ν) :
      IntervalIntegrable (fun u => grid ν s (2*u)) volume 0 1 := by
    have h := (grid_intervalIntegrable ν hν hs 0 2).comp_mul_left (c := (2 : ℝ))
    norm_num at h
    exact h
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  simp only [gridDeficit]
  have he (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : CompactlyCarried ν) :
      (∫ u in (0 : ℝ)..1, grid ν s (2*u)) = averaged ν s := by
    simpa using averaged_grid_nsmul ν hν hs (by norm_num : 0 < (2 : ℕ))
  rw [intervalIntegral.integral_sub (hi _ (hμ.fairShift s)) (hi μ hμ),
    he _ (hμ.fairShift s), he μ hμ,
    averaged_fairShift μ hμ hs, deficit]
  ring

theorem deficit_double_sq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) :
    (deficit μ (2*s))^2 ≤ 8*(Real.log 2)^2*deficit μ s := by
  let := fairShift_probability μ s
  have ht : 0 < 2*s := mul_pos (by norm_num) hs
  let : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  have hj := (convexOn_pow (𝕜 := ℝ) 2).map_integral_le
    (continuous_pow 2).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall (fun u => (gridDeficit_bounds μ hμ ht u).1))
    (gridDeficit_integrable μ hμ ht) (gridDeficit_sq_integrable μ hμ ht)
  rw [integral_gridDeficit μ hμ ht] at hj
  change (deficit μ (2*s))^2 ≤ _ at hj
  have hi : Integrable (fun u => gridDeficit μ s (2*u))
      (volume.restrict (Set.Icc 0 1)) := by
    apply (integrable_const (Real.log 2)).mono'
      (((measurable_grid (fairShift μ s) s).sub (measurable_grid μ s)).comp
        (measurable_const.mul measurable_id)).aestronglyMeasurable
    filter_upwards [] with u
    exact (abs_of_nonneg (gridDeficit_bounds μ hμ hs (2*u)).1).le.trans
      (gridDeficit_bounds μ hμ hs (2*u)).2
  have hh := integral_mono (gridDeficit_sq_integrable μ hμ ht)
    (hi.const_mul (8*(Real.log 2)^2)) (gridDeficit_double_sq μ hμ hs)
  change (∫ u in Set.Icc (0 : ℝ) 1, (gridDeficit μ (2*s) u)^2) ≤ _ at hh
  rw [integral_const_mul, integral_gridDeficit_double_shift μ hμ hs] at hh
  exact hj.trans hh

theorem deficit_dyadic_tendsto_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) (v : ℕ → ℝ) (hv : ∀ n, 0 < v n)
    (h : Filter.Tendsto (fun n => deficit μ (v n)) Filter.atTop (nhds 0)) (j : ℕ) :
    Filter.Tendsto (fun n => deficit μ ((2 : ℝ)^j*v n)) Filter.atTop (nhds 0) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    have hz : Filter.Tendsto (fun n => Real.sqrt (8*(Real.log 2)^2 *
        deficit μ ((2 : ℝ)^j*v n))) Filter.atTop (nhds 0) := by
      simpa using (ih.const_mul (8*(Real.log 2)^2)).sqrt
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz
    · intro n
      exact (deficit_bounds μ hμ (s := (2 : ℝ)^(j+1)*v n)
        (mul_pos (pow_pos (by norm_num) _) (hv n))).1
    · intro n
      apply Real.le_sqrt_of_sq_le
      have hb := deficit_double_sq μ hμ (s := (2 : ℝ)^j*v n)
        (mul_pos (pow_pos (by norm_num) _) (hv n))
      have he : (2 : ℝ)^(j+1)*v n = 2*((2 : ℝ)^j*v n) := by rw [pow_succ]; ring
      rwa [← he] at hb

theorem sum_dyadic_deficit (μ : Measure ℝ) (s : ℝ) (K : ℕ) :
    (∑j ∈ Finset.range K, deficit μ ((2 : ℝ)^j*s))=
      K*Real.log 2-(averaged μ s-averaged μ ((2 : ℝ)^K*s)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [deficit, Nat.cast_add, Nat.cast_one, pow_succ]
    have he : 2*((2 : ℝ)^K*s)=2^K*2*s := by ring
    rw [he]
    ring

theorem wide_window_saturation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) (v : ℕ → ℝ) (hv : ∀ n, 0 < v n)
    (h : Filter.Tendsto (fun n => deficit μ (v n)) Filter.atTop (nhds 0)) (K : ℕ) :
    Filter.Tendsto (fun n => averaged μ (v n)-averaged μ ((2 : ℝ)^K*v n))
      Filter.atTop (nhds (K*Real.log 2)) := by
  have hh := tendsto_finsetSum (Finset.range K) (fun j _ => deficit_dyadic_tendsto_zero μ hμ v hv h j)
  simp only [sum_dyadic_deficit, Finset.sum_const_zero] at hh
  have ht := (tendsto_const_nhds (x := (K : ℝ)*Real.log 2)).sub hh
  simpa only [sub_sub_cancel, sub_zero] using ht

end MeasureEntropy
end EntropyRateDimension
end

end OAI

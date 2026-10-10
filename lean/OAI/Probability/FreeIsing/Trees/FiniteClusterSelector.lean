import OAI.Probability.FreeIsing.Model

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.FiniteCluster

variable {V : Type*}

def IsMinimum (R : V → V → Prop) (marker : V → ℝ) (v a : V) : Prop :=
  R v a ∧ ∀ b, R v b → b ≠ a → marker a < marker b

theorem IsMinimum.unique {R : V → V → Prop} {marker : V → ℝ} {v a b : V}
    (ha : IsMinimum R marker v a) (hb : IsMinimum R marker v b) : a = b := by
  by_contra hab
  exact (lt_asymm (ha.2 b hb.1 (Ne.symm hab))) (hb.2 a ha.1 hab)

def selector (R : V → V → Prop) (marker : V → ℝ) (v : V) : V := by
  classical
  exact if h : ∃ a, IsMinimum R marker v a then h.choose else v

theorem selector_eq_of_minimum {R : V → V → Prop} {marker : V → ℝ} {v a : V}
    (ha : IsMinimum R marker v a) : selector R marker v = a := by
  classical
  have h : ∃ a, IsMinimum R marker v a := ⟨a, ha⟩
  rw [selector, dite_eq_left h]
  exact h.choose_spec.unique ha

theorem selector_eq_self_of_not_exists {R : V → V → Prop} {marker : V → ℝ} {v : V}
    (h : ¬ ∃ a, IsMinimum R marker v a) : selector R marker v = v := by
  classical
  exact dite_eq_right h

theorem selector_eq_iff (R : V → V → Prop) (marker : V → ℝ) (v a : V) :
    selector R marker v = a ↔
      IsMinimum R marker v a ∨ ((¬ ∃ b, IsMinimum R marker v b) ∧ v = a) := by
  classical
  by_cases h : ∃ b, IsMinimum R marker v b
  · constructor
    · intro heq
      left
      rw [selector, dite_eq_left h] at heq
      exact heq ▸ h.choose_spec
    · rintro (ha | ⟨hn, _⟩)
      · exact selector_eq_of_minimum ha
      · exact (hn h).elim
  · simp only [selector, dite_eq_right h]
    constructor
    · exact fun heq => Or.inr ⟨h, heq⟩
    · rintro (ha | ⟨_, heq⟩)
      · exact (h ⟨a, ha⟩).elim
      · exact heq

theorem exists_minimum_of_finite {R : V → V → Prop} {marker : V → ℝ} {v : V}
    (hfinite : {a | R v a}.Finite) (hne : ∃ a, R v a)
    (hinj : Function.Injective marker) : ∃ a, IsMinimum R marker v a := by
  obtain ⟨a, ha, hmin⟩ := Set.exists_min_image {a | R v a} marker hfinite hne
  refine ⟨a, ha, ?_⟩
  intro b hb hba
  exact lt_of_le_of_ne (hmin b hb) (fun hab => hba (hinj hab.symm))

theorem selector_mem {R : V → V → Prop} {marker : V → ℝ} {v : V}
    (hfinite : {a | R v a}.Finite) (hrefl : R v v)
    (hinj : Function.Injective marker) : R v (selector R marker v) := by
  obtain ⟨a, ha⟩ := exists_minimum_of_finite hfinite ⟨v, hrefl⟩ hinj
  rw [selector_eq_of_minimum ha]
  exact ha.1

theorem selector_eq_of_same_cluster {R : V → V → Prop} {marker : V → ℝ} {v w : V}
    (hrow : ∀ a, R v a ↔ R w a)
    (hex : ∃ a, IsMinimum R marker v a) : selector R marker v = selector R marker w := by
  obtain ⟨a, ha⟩ := hex
  have hw : IsMinimum R marker w a := by
    refine ⟨(hrow a).mp ha.1, ?_⟩
    intro b hb hba
    exact ha.2 b ((hrow b).mpr hb) hba
  rw [selector_eq_of_minimum ha, selector_eq_of_minimum hw]

theorem selector_eq_of_related {R : V → V → Prop} {marker : V → ℝ} {v w : V}
    (hR : Equivalence R) (hvw : R v w) (hfinite : {a | R v a}.Finite)
    (hinj : Function.Injective marker) : selector R marker v = selector R marker w := by
  apply selector_eq_of_same_cluster
  · intro a
    exact ⟨fun hva => hR.trans (hR.symm hvw) hva, fun hwa => hR.trans hvw hwa⟩
  · exact exists_minimum_of_finite hfinite ⟨v, hR.refl v⟩ hinj

theorem selector_eq_iff_related {R : V → V → Prop} {marker : V → ℝ} {v w : V}
    (hR : Equivalence R) (hv : {a | R v a}.Finite) (hw : {a | R w a}.Finite)
    (hinj : Function.Injective marker) :
    selector R marker v = selector R marker w ↔ R v w := by
  constructor
  · intro heq
    have hv' := selector_mem hv (hR.refl v) hinj
    have hw' := selector_mem hw (hR.refl w) hinj
    rw [heq] at hv'
    exact hR.trans hv' (hR.symm hw')
  · exact fun hvw => selector_eq_of_related hR hvw hv hinj

theorem isMinimum_reindex (e : V ≃ V) (R : V → V → Prop) (marker : V → ℝ)
    (v a : V) :
    IsMinimum (fun x y => R (e.symm x) (e.symm y)) (marker ∘ e.symm) (e v) (e a) ↔
      IsMinimum R marker v a := by
  constructor
  · rintro ⟨ha, hmin⟩
    refine ⟨by simpa using ha, ?_⟩
    intro b hb hba
    simpa using hmin (e b) (by simpa using hb)
      (fun h => hba (e.injective h))
  · rintro ⟨ha, hmin⟩
    refine ⟨by simpa using ha, ?_⟩
    intro b hb hba
    simp only [Function.comp_apply, e.symm_apply_apply]
    apply hmin (e.symm b) (by simpa using hb)
    intro h
    apply hba
    exact (e.apply_symm_apply b).symm.trans (congrArg e h)

theorem selector_reindex (e : V ≃ V) (R : V → V → Prop) (marker : V → ℝ) (v : V) :
    selector (fun x y => R (e.symm x) (e.symm y)) (marker ∘ e.symm) (e v) =
      e (selector R marker v) := by
  classical
  by_cases h : ∃ a, IsMinimum R marker v a
  · obtain ⟨a, ha⟩ := h
    rw [selector_eq_of_minimum ha,
      selector_eq_of_minimum ((isMinimum_reindex e R marker v a).mpr ha)]
  · have h' : ¬ ∃ a, IsMinimum (fun x y => R (e.symm x) (e.symm y))
        (marker ∘ e.symm) (e v) a := by
      rintro ⟨a, ha⟩
      apply h
      refine ⟨e.symm a, (isMinimum_reindex e R marker v (e.symm a)).mp ?_⟩
      simpa using ha
    rw [selector_eq_self_of_not_exists h, selector_eq_self_of_not_exists h']

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω] [Countable V]

theorem measurableSet_isMinimum (R : Ω → V → V → Prop) (marker : Ω → V → ℝ)
    (hR : ∀ v a, MeasurableSet {ω | R ω v a})
    (hm : ∀ a, Measurable (fun ω => marker ω a)) (v a : V) :
    MeasurableSet {ω | IsMinimum (R ω) (marker ω) v a} := by
  have hforall : MeasurableSet (⋂ b, {ω | R ω v b → b ≠ a → marker ω a < marker ω b}) :=
    .iInter fun b => (hR v b).imp
      ((MeasurableSet.const (b ≠ a)).imp (measurableSet_lt (hm a) (hm b)))
  convert (hR v a).inter hforall using 1
  ext ω
  simp [IsMinimum]

theorem measurable_selector [MeasurableSpace V]
    (R : Ω → V → V → Prop) (marker : Ω → V → ℝ)
    (hR : ∀ v a, MeasurableSet {ω | R ω v a})
    (hm : ∀ a, Measurable (fun ω => marker ω a)) (v : V) :
    Measurable (fun ω => selector (R ω) (marker ω) v) := by
  apply measurable_to_countable'
  intro a
  have hmin := measurableSet_isMinimum R marker hR hm v
  have hex : MeasurableSet {ω | ∃ b, IsMinimum (R ω) (marker ω) v b} := by
    convert MeasurableSet.iUnion hmin using 1
    ext ω
    simp
  have hnone : MeasurableSet {ω | ¬ ∃ b, IsMinimum (R ω) (marker ω) v b} := hex.compl
  have hset : (fun ω => selector (R ω) (marker ω) v) ⁻¹' {a} =
      {ω | IsMinimum (R ω) (marker ω) v a} ∪
      ({ω | ¬ ∃ b, IsMinimum (R ω) (marker ω) v b} ∩ {ω | v = a}) := by
    ext ω
    exact selector_eq_iff (R ω) (marker ω) v a
  rw [hset]
  exact (hmin a).union (hnone.inter (MeasurableSet.const _))

end Measurability

def color {C : Type*} (R : V → V → Prop) (marker : V → ℝ)
    (labels : V → C) (v : V) : C :=
  labels (selector R marker v)

theorem color_eq_of_related {C : Type*} {R : V → V → Prop} {marker : V → ℝ}
    (labels : V → C) {v w : V} (hR : Equivalence R) (hvw : R v w)
    (hfinite : {a | R v a}.Finite) (hinj : Function.Injective marker) :
    color R marker labels v = color R marker labels w := by
  unfold color
  rw [selector_eq_of_related hR hvw hfinite hinj]

theorem color_reindex {C : Type*} (e : V ≃ V) (R : V → V → Prop)
    (marker : V → ℝ) (labels : V → C) (v : V) :
    color (fun x y => R (e.symm x) (e.symm y)) (marker ∘ e.symm)
      (labels ∘ e.symm) (e v) = color R marker labels v := by
  simp only [color, selector_reindex, Function.comp_apply, e.symm_apply_apply]

theorem measurable_color {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    [Countable V] (R : Ω → V → V → Prop) (marker : Ω → V → ℝ)
    (labels : Ω → V → C) (hR : ∀ v a, MeasurableSet {ω | R ω v a})
    (hm : ∀ a, Measurable (fun ω => marker ω a))
    (hc : ∀ a, Measurable (fun ω => labels ω a)) :
    Measurable (fun ω => color (R ω) (marker ω) (labels ω)) := by
  let : MeasurableSpace V := ⊤
  let : MeasurableSingletonClass V := ⟨fun _ => trivial⟩
  apply Measurable.of_eval
  intro v
  have happly : Measurable (fun p : Ω × V => labels p.1 p.2) :=
    measurable_from_prod_countable_left hc
  exact happly.comp (measurable_id.prodMk (measurable_selector R marker hR hm v))

theorem ae_marker_ne [Countable V] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] {v w : V} (hvw : v ≠ w) :
    ∀ᵐ marker ∂Measure.infinitePi (fun _ : V => μ), marker v ≠ marker w := by
  have hprod : ∀ᵐ p : ℝ × ℝ ∂μ.prod μ, p.1 ≠ p.2 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
    exact Filter.Eventually.of_forall fun x => (μ.ae_ne x).mono fun y hy => Ne.symm hy
  have hmap : ∀ᵐ p : ℝ × ℝ ∂Measure.map (fun marker : V → ℝ => (marker v, marker w))
      (Measure.infinitePi (fun _ : V => μ)), p.1 ≠ p.2 := by
    rw [Measure.infinitePi_map_eval_prod hvw]
    exact hprod
  exact ae_of_ae_map ((measurable_pi_apply v).prodMk (measurable_pi_apply w)).aemeasurable hmap

theorem ae_marker_injective [Countable V] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] :
    ∀ᵐ marker ∂Measure.infinitePi (fun _ : V => μ), Function.Injective marker := by
  have hall : ∀ᵐ marker ∂Measure.infinitePi (fun _ : V => μ),
      ∀ v w : V, v ≠ w → marker v ≠ marker w := by
    apply ae_all_iff.mpr
    intro v
    apply ae_all_iff.mpr
    intro w
    by_cases hvw : v = w
    · exact Filter.Eventually.of_forall fun _ h => (h hvw).elim
    · exact (ae_marker_ne μ hvw).mono fun _ h _ => h
  filter_upwards [hall] with marker hmarker
  intro v w heq
  by_contra hne
  exact hmarker v w hne heq

theorem ae_uniform_markers_injective (d : ℕ) :
    ∀ᵐ marker ∂labelMeasure d, Function.Injective marker := by
  have : NullSingletonClass uniform01 := by
    unfold uniform01
    infer_instance
  exact ae_marker_injective uniform01

end Problem367.FiniteCluster

end

end OAI

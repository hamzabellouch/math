import OAI.Probability.SLE.Mass.RationalTraceMass

namespace OAI

/-! Uniform local total-variation control for the all-time extension. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal CompactlySupported

namespace SLEExactGauge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

/-- Local total variation is expressed uniformly on measurable sets. The
finite-terminal form applies to each compact restriction in the source. -/
theorem RationalTraceIncrements.local_variation_continuity
    {μ : ℚ → Measure X} {ν : Measure X} [ν.Regular] [IsFiniteMeasure ν]
    [NullSingletonClass ν] {γ : ℝ → X} (H : RationalTraceIncrements μ ν γ)
    (hγ : Continuous γ) (M : ℝ → Measure X)
    (hMr : ∀ t, (M t).Regular) (hdom : ∀ t, M t ≤ ν)
    (hrat : ∀ q : ℚ, M q=μ q)
    (hcont : ∀ f : C_c(X,ℝ), Continuous (fun t => ∫ x, f x ∂M t)) :
    ∀ t₀ : ℝ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ s t : ℝ, dist s t₀ < δ → dist t t₀ < δ →
        ∀ A : Set X, MeasurableSet A → |(M s A).toReal-(M t A).toReal| < ε := by
  intro t₀ ε hε
  obtain ⟨U,hUsub,hU,hνU⟩ := ({γ t₀} : Set X).exists_isOpen_lt_of_lt (μ := ν)
    (ENNReal.ofReal ε) (by simpa using ENNReal.ofReal_pos.mpr hε)
  have htU : γ t₀ ∈ U := hUsub (mem_singleton _)
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp
    (hγ.continuousAt.preimage_mem_nhds (hU.mem_nhds htU))
  have hI (a b : ℝ) (ha : dist a t₀ < δ) (hb : dist b t₀ < δ) : γ '' Icc a b ⊆ U := by
    rintro _ ⟨x,hx,rfl⟩
    apply hδsub
    rw [Metric.mem_ball,Real.dist_eq]
    rw [Real.dist_eq,abs_lt] at ha hb
    exact abs_lt.mpr ⟨lt_of_lt_of_le ha.1 (sub_le_sub_right hx.1 t₀),
      lt_of_le_of_lt (sub_le_sub_right hx.2 t₀) hb.2⟩
  have hq (p q : ℚ) (hp : dist (p:ℝ) t₀ < δ) (hq : dist (q:ℝ) t₀ < δ) :
      μ p ≤ μ q+ν.restrict U := by
    rcases le_total p q with hpq | hqp
    · exact (H.monotone hpq).trans (Measure.le_add_right le_rfl)
    · obtain ⟨η,hη,hην⟩ := H.increment q p hqp
      rw [hη]
      exact add_le_add le_rfl (hην.trans (Measure.restrict_mono (hI q p hq hp) le_rfl))
  have hreal (s t : ℝ) (hs : dist s t₀ < δ) (ht : dist t t₀ < δ) :
      M s ≤ M t+ν.restrict U := by
    let : (M s).Regular := hMr s
    let : (M t).Regular := hMr t
    let : IsFiniteMeasure (M t) := isFiniteMeasure_of_le ν (hdom t)
    let : (ν.restrict U).Regular := Measure.Regular.restrict_of_measure_ne_top (measure_ne_top ν U)
    obtain ⟨p,hp⟩ := exists_rational_sequence_tendsto s
    obtain ⟨q,hqt⟩ := exists_rational_sequence_tendsto t
    have hpU : ∀ᶠ n in atTop, dist (p n:ℝ) t₀ < δ :=
      hp.eventually (isOpen_lt (continuous_id.dist continuous_const) continuous_const |>.mem_nhds hs)
    have hqU : ∀ᶠ n in atTop, dist (q n:ℝ) t₀ < δ :=
      hqt.eventually (isOpen_lt (continuous_id.dist continuous_const) continuous_const |>.mem_nhds ht)
    apply radon_measure_le_of_nonneg_tests
    intro f hfn
    have hplim : Tendsto (fun n => ∫ x, f x ∂μ (p n)) atTop (𝓝 (∫ x, f x ∂M s)) := by
      simpa only [Function.comp_def,hrat] using (hcont f).continuousAt.tendsto.comp hp
    have hqlim : Tendsto (fun n => ∫ x, f x ∂(μ (q n)+ν.restrict U)) atTop
        (𝓝 (∫ x, f x ∂(M t+ν.restrict U))) := by
      have hi := ((hcont f).continuousAt.tendsto.comp hqt).add
        (tendsto_const_nhds (x := ∫ x, f x ∂ν.restrict U))
      simp only [Function.comp_def,hrat] at hi
      have hqadd (n : ℕ) : (∫ x, f x ∂(μ (q n)+ν.restrict U))=
          (∫ x, f x ∂μ (q n))+(∫ x, f x ∂ν.restrict U) := by
        let : (μ (q n)).Regular := H.regular (q n)
        exact integral_add_measure f.integrable f.integrable
      simpa only [hqadd,integral_add_measure f.integrable f.integrable] using hi
    apply le_of_tendsto_of_tendsto hplim hqlim
    filter_upwards [hpU,hqU] with n hpn hqn
    let : (μ (q n)).Regular := H.regular (q n)
    let : IsFiniteMeasure (μ (q n)) := isFiniteMeasure_of_le ν (H.dominated (q n))
    exact integral_mono_measure (hq (p n) (q n) hpn hqn) (ae_of_all _ hfn) f.integrable
  refine ⟨δ,hδ,fun s t hs ht A hA => ?_⟩
  have hst := hreal s t hs ht A
  have hts := hreal t s ht hs A
  have hsn : M s A ≠ ⊤ := ((hdom s A).trans_lt (measure_lt_top ν A)).ne
  have htn : M t A ≠ ⊤ := ((hdom t A).trans_lt (measure_lt_top ν A)).ne
  have hUn : ν U ≠ ⊤ := measure_ne_top ν U
  rw [Measure.add_apply,Measure.restrict_apply hA,inter_comm] at hst hts
  have hUA : ν (U ∩ A) ≤ ν U := measure_mono inter_subset_left
  have hcan : ν (U ∩ A) ≠ ⊤ := (hUA.trans_lt hUn.lt_top).ne
  have hst' := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨htn,hcan⟩) hst
  have hts' := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hsn,hcan⟩) hts
  rw [ENNReal.toReal_add htn hcan] at hst'
  rw [ENNReal.toReal_add hsn hcan] at hts'
  have hless : (ν (U ∩ A)).toReal < ε := by
    have hUl : (ν U).toReal < ε := by
      simpa only [ENNReal.toReal_ofReal hε.le] using
        (ENNReal.toReal_lt_toReal hUn ENNReal.ofReal_ne_top).mpr hνU
    exact (ENNReal.toReal_mono hUn hUA).trans_lt hUl
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

/-- The pathwise rational squeeze gives one increasing extension with
local total-variation continuity. -/
theorem RationalTraceIncrements.exists_locally_tv_continuous_extension
    {μ : ℚ → Measure X} {ν : Measure X} [ν.Regular] [IsFiniteMeasure ν]
    [NullSingletonClass ν] {γ : ℝ → X} (H : RationalTraceIncrements μ ν γ)
    (hγ : Continuous γ) :
    ∃ M : ℝ → Measure X, (∀ t, (M t).Regular) ∧ (∀ t, M t ≤ ν) ∧
      (∀ q : ℚ, M q=μ q) ∧ Monotone M ∧
      (∀ f : C_c(X,ℝ), Continuous (fun t => ∫ x, f x ∂M t)) ∧
      ∀ t₀ : ℝ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s t : ℝ, dist s t₀ < δ → dist t t₀ < δ →
          ∀ A : Set X, MeasurableSet A → |(M s A).toReal-(M t A).toReal| < ε := by
  obtain ⟨M,hMr,hdom,hrat,hcont,hmono⟩ := H.exists_continuous_extension hγ
  exact ⟨M,hMr,hdom,hrat,hmono,hcont,H.local_variation_continuity hγ M hMr hdom hrat hcont⟩

end SLEExactGauge

end

end OAI

import OAI.Probability.SLE.Mass.RationalTraceMassLocal

namespace OAI

/-! Local total-variation continuity of the half-plane reconstruction.
Only the mass of a fixed compact is used; the terminal mass may be infinite. -/

noncomputable section
open Set Filter MeasureTheory Classical
open scoped Topology ENNReal CompactlySupported

namespace SLEExactGauge

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

private lemma halfPlane_regular_add (μ ν : Measure upperHalfPlane) [μ.Regular] [ν.Regular] :
    (μ + ν).Regular := by
  let : IsFiniteMeasureOnCompacts (μ + ν) := ⟨fun K hK => by
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top,hK.measure_lt_top⟩⟩
  infer_instance

theorem HalfPlaneTraceIncrements.local_variation_continuity
    {μ : ℚ → Measure upperHalfPlane} {ν : Measure upperHalfPlane} [ν.Regular]
    [NullSingletonClass ν] {γ : ℝ → ℂ}
    (H : HalfPlaneTraceIncrements μ ν γ) (hγ : Continuous γ)
    (M : ℝ → Measure upperHalfPlane) (hMr : ∀ t, (M t).Regular)
    (hdom : ∀ t, M t ≤ ν) (hrat : ∀ q : ℚ, M q = μ q)
    (hcont : ∀ f : C_c(upperHalfPlane,ℝ), Continuous (fun t => ∫ z, f z ∂M t))
    (K : Set upperHalfPlane) (hK : IsCompact K) :
    ∀ t₀ : ℝ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ s t : ℝ, dist s t₀ < δ → dist t t₀ < δ →
        ∀ A : Set upperHalfPlane, MeasurableSet A → A ⊆ K →
          |(M s A).toReal-(M t A).toReal| < ε := by
  intro t₀ ε hε
  let ρ := ambientCompactRestriction ν K
  let : IsFiniteMeasure ρ := ambientCompactRestriction_finite ν K hK
  let : NullSingletonClass ρ := ambientCompactRestriction_nullSingletons ν K
  obtain ⟨U,hUsub,hU,hρU⟩ := ({γ t₀} : Set ℂ).exists_isOpen_lt_of_lt (μ := ρ)
    (ENNReal.ofReal ε) (by simpa using ENNReal.ofReal_pos.mpr hε)
  let V : Set upperHalfPlane := (Subtype.val : upperHalfPlane → ℂ) ⁻¹' U
  have hV : IsOpen V := hU.preimage continuous_subtype_val
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
      μ p ≤ μ q+ν.restrict V := by
    rcases le_total p q with hpq | hqp
    · exact (H.monotone hpq).trans (Measure.le_add_right le_rfl)
    · obtain ⟨η,hη,hην⟩ := H.increment q p hqp
      rw [hη]
      apply add_le_add le_rfl
      exact hην.trans (Measure.restrict_mono
        (show {z : upperHalfPlane | (z : ℂ) ∈ γ '' Icc (q:ℝ) p} ⊆ V
          from fun z hz => hI q p hq hp hz) le_rfl)
  have hreal (s t : ℝ) (hs : dist s t₀ < δ) (ht : dist t t₀ < δ) :
      M s ≤ M t+ν.restrict V := by
    let : (M s).Regular := hMr s
    let : (M t).Regular := hMr t
    let : (ν.restrict V).Regular := inferInstance
    let : (M t+ν.restrict V).Regular := halfPlane_regular_add _ _
    obtain ⟨p,hp⟩ := exists_rational_sequence_tendsto s
    obtain ⟨q,hqt⟩ := exists_rational_sequence_tendsto t
    have hpU : ∀ᶠ n in atTop, dist (p n:ℝ) t₀ < δ :=
      hp.eventually (isOpen_lt (continuous_id.dist continuous_const) continuous_const |>.mem_nhds hs)
    have hqU : ∀ᶠ n in atTop, dist (q n:ℝ) t₀ < δ :=
      hqt.eventually (isOpen_lt (continuous_id.dist continuous_const) continuous_const |>.mem_nhds ht)
    apply radon_measure_le_of_nonneg_tests
    intro f hfn
    have hplim : Tendsto (fun n => ∫ z, f z ∂μ (p n)) atTop (𝓝 (∫ z, f z ∂M s)) := by
      simpa only [Function.comp_def,hrat] using (hcont f).continuousAt.tendsto.comp hp
    have hqlim : Tendsto (fun n => ∫ z, f z ∂(μ (q n)+ν.restrict V)) atTop
        (𝓝 (∫ z, f z ∂(M t+ν.restrict V))) := by
      have hi := ((hcont f).continuousAt.tendsto.comp hqt).add
        (tendsto_const_nhds (x := ∫ z, f z ∂ν.restrict V))
      simp only [Function.comp_def,hrat] at hi
      have hqadd (n : ℕ) : (∫ z, f z ∂(μ (q n)+ν.restrict V)) =
          (∫ z, f z ∂μ (q n))+(∫ z, f z ∂ν.restrict V) := by
        let : (μ (q n)).Regular := H.regular (q n)
        exact integral_add_measure f.integrable f.integrable
      simpa only [hqadd,integral_add_measure f.integrable f.integrable] using hi
    apply le_of_tendsto_of_tendsto hplim hqlim
    filter_upwards [hpU,hqU] with n hpn hqn
    let : (μ (q n)).Regular := H.regular (q n)
    let : (μ (q n)+ν.restrict V).Regular := halfPlane_regular_add _ _
    exact integral_mono_measure (hq (p n) (q n) hpn hqn) (ae_of_all _ hfn) f.integrable
  refine ⟨δ,hδ,fun s t hs ht A hA hAK => ?_⟩
  have hst := hreal s t hs ht A
  have hts := hreal t s ht hs A
  have hsn : M s A ≠ ⊤ := ((hdom s A).trans ((measure_mono hAK))).trans_lt hK.measure_lt_top |>.ne
  have htn : M t A ≠ ⊤ := ((hdom t A).trans ((measure_mono hAK))).trans_lt hK.measure_lt_top |>.ne
  have hUn : ρ U ≠ ⊤ := measure_ne_top ρ U
  rw [Measure.add_apply,Measure.restrict_apply hA,inter_comm] at hst hts
  have hUA : ν (V ∩ A) ≤ ρ U := by
    change ν (V ∩ A) ≤ ambientCompactRestriction ν K U
    rw [ambientCompactRestriction,Measure.map_apply measurable_subtype_coe hU.measurableSet]
    change ν (V ∩ A) ≤ ν.restrict K V
    rw [Measure.restrict_apply hV.measurableSet]
    exact measure_mono (fun z hz => ⟨hz.1,hAK hz.2⟩)
  have hcan : ν (V ∩ A) ≠ ⊤ := (hUA.trans_lt hUn.lt_top).ne
  have hst' := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨htn,hcan⟩) hst
  have hts' := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hsn,hcan⟩) hts
  rw [ENNReal.toReal_add htn hcan] at hst'
  rw [ENNReal.toReal_add hsn hcan] at hts'
  have hless : (ν (V ∩ A)).toReal < ε := by
    have hUl : (ρ U).toReal < ε := by
      simpa only [ENNReal.toReal_ofReal hε.le] using
        (ENNReal.toReal_lt_toReal hUn ENNReal.ofReal_ne_top).mpr hρU
    exact (ENNReal.toReal_mono hUn hUA).trans_lt hUl
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

theorem HalfPlaneTraceIncrements.exists_locally_tv_continuous_extension
    {μ : ℚ → Measure upperHalfPlane} {ν : Measure upperHalfPlane} [ν.Regular]
    [NullSingletonClass ν] {γ : ℝ → ℂ}
    (H : HalfPlaneTraceIncrements μ ν γ) (hγ : Continuous γ) :
    ∃ M : ℝ → Measure upperHalfPlane, (∀ t, (M t).Regular) ∧ (∀ t, M t ≤ ν) ∧
      (∀ q : ℚ, M q = μ q) ∧ Monotone M ∧
      (∀ f : C_c(upperHalfPlane,ℝ), Continuous (fun t => ∫ z, f z ∂M t)) ∧
      ∀ K : Set upperHalfPlane, IsCompact K →
        ∀ t₀ : ℝ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
          ∀ s t : ℝ, dist s t₀ < δ → dist t t₀ < δ →
            ∀ A : Set upperHalfPlane, MeasurableSet A → A ⊆ K →
              |(M s A).toReal-(M t A).toReal| < ε := by
  obtain ⟨M,hMr,hdom,hrat,hcont,hmono⟩ := H.exists_continuous_extension hγ
  exact ⟨M,hMr,hdom,hrat,hmono,hcont,
    fun K hK => H.local_variation_continuity hγ M hMr hdom hrat hcont K hK⟩

end SLEExactGauge

end

end OAI

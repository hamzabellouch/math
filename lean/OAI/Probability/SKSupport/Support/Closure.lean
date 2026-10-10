import Mathlib
import OAI.Probability.SKSupport.Model

namespace OAI

section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace ZeroTemperatureSK.SupportDeterministic
abbrev Time := Set.Ico (0 : ℝ) 1

structure IsOrderParameter (γ : ℝ → ℝ) : Prop where
  nonneg : ∀ t ∈ Set.Ico (0 : ℝ) 1, 0 ≤ γ t
  monotone : MonotoneOn γ (Set.Ico (0 : ℝ) 1)
  rightContinuous : ∀ t ∈ Set.Ico (0 : ℝ) 1, ContinuousWithinAt γ (Set.Ici t) t
  integrable : IntegrableOn γ (Set.Ico (0 : ℝ) 1)

def IsStieltjesMeasure (γ : ℝ → ℝ) (μ : Measure Time) : Prop :=
  ∀ t : Time, μ (Set.Iic t) = ENNReal.ofReal (γ t)

namespace IsStieltjesMeasure

variable {γ : ℝ → ℝ} {μ : Measure Time}

lemma cdf_add_Ioc (hμ : IsStieltjesMeasure γ μ) {a b : Time} (hab : a ≤ b) :
    ENNReal.ofReal (γ a) + μ (Ioc a b) = ENNReal.ofReal (γ b) := by
  rw [← hμ a, ← hμ b, ← measure_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
    Iic_union_Ioc_eq_Iic hab]

lemma eq_cdf_of_measure_Ioc_zero (hμ : IsStieltjesMeasure γ μ)
    (hγ : IsOrderParameter γ) {a b : Time} (hab : a ≤ b)
    (hz : μ (Ioc a b) = 0) : γ a = γ b := by
  have he := hμ.cdf_add_Ioc hab
  rw [hz, add_zero] at he
  exact (ENNReal.ofReal_eq_ofReal_iff (hγ.nonneg a a.property) (hγ.nonneg b b.property)).mp he

lemma measure_zero_of_disjoint_support {s : Set Time}
    (hs : Disjoint s μ.support) : μ s = 0 := by
  apply measure_mono_null (Set.disjoint_left.mp hs) μ.measure_compl_support

lemma eq_cdf_of_support_free (hμ : IsStieltjesMeasure γ μ)
    (hγ : IsOrderParameter γ) {a b : Time} (hab : a ≤ b)
    (hs : Disjoint (Ioc a b) μ.support) : γ a = γ b :=
  hμ.eq_cdf_of_measure_Ioc_zero hγ hab (measure_zero_of_disjoint_support hs)

lemma lt_cdf_of_full_support (hμ : IsStieltjesMeasure γ μ)
    (hS : μ.support = univ) {a b : Time} (hab : a < b) : γ a < γ b := by
  let c : Time := ⟨((a : ℝ) + b) / 2, by
    constructor
    · linarith [a.property.1, b.property.1]
    · linarith [a.property.2, b.property.2]⟩
  have hac : a < c := by change (a : ℝ) < ((a : ℝ) + b) / 2; change (a : ℝ) < b at hab; linarith
  have hcb : c < b := by change ((a : ℝ) + b) / 2 < b; change (a : ℝ) < b at hab; linarith
  have hcS : c ∈ μ.support := by rw [hS]; trivial
  have hpos : 0 < μ (Ioc a b) :=
    lt_of_lt_of_le ((μ.mem_support_iff_forall c).mp hcS _ (Ioo_mem_nhds hac hcb))
      (measure_mono Ioo_subset_Ioc_self)
  have hlt : ENNReal.ofReal (γ a) < ENNReal.ofReal (γ b) := by
    rw [← hμ.cdf_add_Ioc hab.le]
    exact ENNReal.lt_add_right ENNReal.ofReal_ne_top hpos.ne'
  exact (ENNReal.ofReal_lt_ofReal_iff'.mp hlt).1

lemma strictMonoOn_of_full_support (hμ : IsStieltjesMeasure γ μ)
    (hS : μ.support = univ) : StrictMonoOn γ (Ico (0 : ℝ) 1) := by
  intro a ha b hb hab
  exact hμ.lt_cdf_of_full_support hS (a := ⟨a,ha⟩) (b := ⟨b,hb⟩) hab

end IsStieltjesMeasure

def InSupport (μ : Measure Time) (t : ℝ) : Prop :=
  ∃ ht : t ∈ Ico (0 : ℝ) 1, (⟨t, ht⟩ : Time) ∈ μ.support

lemma inSupport_coe {μ : Measure Time} {t : Time} :
    InSupport μ t ↔ t ∈ μ.support := by
  constructor
  · rintro ⟨ht, h⟩; exact h
  · intro ht; exact ⟨t.property, ht⟩

lemma exists_support_gap {μ : Measure Time} {x : Time}
    (hx : x ∉ μ.support) (hright : ∃ B ∈ μ.support, x < B) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b < 1 ∧ (a = 0 ∨ InSupport μ a) ∧
      InSupport μ b ∧ ∀ t ∈ Ioo a b, ¬ InSupport μ t := by
  obtain ⟨F, hF, hpre⟩ :=
    (Topology.IsInducing.subtypeVal (t := Ico (0 : ℝ) 1)).isClosed_iff.mp μ.isClosed_support
  have hFiff (t : Time) : (t : ℝ) ∈ F ↔ t ∈ μ.support := by
    change t ∈ (Subtype.val ⁻¹' F) ↔ _
    rw [hpre]
  obtain ⟨B, hBS, hxB⟩ := hright
  have hcompactA : IsCompact ({0} ∪ (F ∩ Icc (0 : ℝ) x)) :=
    isCompact_singleton.union (isCompact_Icc.inter_left hF)
  obtain ⟨a, ha⟩ := hcompactA.exists_isGreatest (by exact ⟨0, Or.inl rfl⟩)
  have hcompactB : IsCompact (F ∩ Icc (x : ℝ) B) :=
    isCompact_Icc.inter_left hF
  obtain ⟨b, hb⟩ := hcompactB.exists_isLeast
    ⟨B, (hFiff B).mpr hBS, hxB.le, le_rfl⟩
  have ha0 : 0 ≤ a := ha.2 (Or.inl rfl)
  have hax : a ≤ x := by
    rcases ha.1 with heq | hm
    · simpa only [mem_singleton_iff] using heq ▸ x.property.1
    · exact hm.2.2
  have hb1 : b < 1 := hb.1.2.2.trans_lt B.property.2
  have hxb : (x : ℝ) < b := by
    refine lt_of_le_of_ne hb.1.2.1 ?_
    intro heq
    apply hx
    apply (hFiff x).mp
    simpa [heq] using hb.1.1
  refine ⟨a, b, ha0, hax.trans_lt hxb, hb1, ?_, ?_, ?_⟩
  · rcases ha.1 with heq | hm
    · exact Or.inl heq
    · exact Or.inr ⟨⟨ha0, hax.trans_lt x.property.2⟩,
        (hFiff ⟨a, ⟨ha0, hax.trans_lt x.property.2⟩⟩).mp hm.1⟩
  · exact ⟨⟨x.property.1.trans hxb.le, hb1⟩,
      (hFiff ⟨b, ⟨x.property.1.trans hxb.le, hb1⟩⟩).mp hb.1.1⟩
  · intro t ht hts
    obtain ⟨ht01, hts⟩ := hts
    have htF : t ∈ F := (hFiff ⟨t, ht01⟩).mpr hts
    by_cases htx : t ≤ x
    · exact (not_lt_of_ge (ha.2 (Or.inr ⟨htF, ht01.1, htx⟩))) ht.1
    · exact (not_lt_of_ge (hb.2 ⟨htF, le_of_not_ge htx, ht.2.le.trans hb.1.2.2⟩)) ht.2

lemma support_cofinal_of_no_terminal_plateau {γ : ℝ → ℝ} {μ : Measure Time}
    (hγ : IsOrderParameter γ) (hμ : IsStieltjesMeasure γ μ)
    (hend : ¬ ∃ a c : ℝ, 0 ≤ a ∧ a < 1 ∧ 0 ≤ c ∧
      ∀ t ∈ Ioo a 1, γ t = c) (x : Time) :
    ∃ B ∈ μ.support, x < B := by
  by_contra hn
  push Not at hn
  let d : Time := ⟨((x : ℝ) + 1) / 2, by
    constructor <;> linarith [x.property.1, x.property.2]⟩
  apply hend
  refine ⟨x, γ d, x.property.1, x.property.2, hγ.nonneg d d.property, ?_⟩
  intro t ht
  let t' : Time := ⟨t, ⟨x.property.1.trans ht.1.le, ht.2⟩⟩
  have hxd : x < d := by change (x : ℝ) < ((x : ℝ)+1)/2; linarith [x.property.2]
  have heq {u v : Time} (hu : x < u) (hv : x < v) (huv : u ≤ v) :
      γ u = γ v := by
    apply hμ.eq_cdf_of_support_free hγ huv
    rw [Set.disjoint_left]
    intro z hz hzs
    exact (not_lt_of_ge (hn z hzs)) (hu.trans hz.1)
  change γ t' = γ d
  rcases le_total t' d with htd | hdt
  · exact heq ht.1 hxd htd
  · exact (heq hxd ht.1 hdt).symm

lemma constant_on_support_gap {γ : ℝ → ℝ} {μ : Measure Time}
    (hγ : IsOrderParameter γ) (hμ : IsStieltjesMeasure γ μ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 1)
    (hgap : ∀ t ∈ Ioo a b, ¬ InSupport μ t) :
    ∃ c, 0 ≤ c ∧ ∀ t ∈ Ioo a b, γ t = c := by
  let d : Time := ⟨(a+b)/2, by constructor <;> linarith⟩
  have hd : (d : ℝ) ∈ Ioo a b := by change a < (a+b)/2 ∧ (a+b)/2 < b; constructor <;> linarith
  refine ⟨γ d, hγ.nonneg d d.property, ?_⟩
  have heq {u v : Time} (hu : (u : ℝ) ∈ Ioo a b)
      (hv : (v : ℝ) ∈ Ioo a b) (huv : u ≤ v) : γ u = γ v := by
    apply hμ.eq_cdf_of_support_free hγ huv
    rw [Set.disjoint_left]
    intro z hz hzs
    exact hgap z ⟨hu.1.trans (show (u : ℝ) < z from hz.1), (show (z : ℝ) ≤ v from hz.2).trans_lt hv.2⟩ ⟨z.property, hzs⟩
  intro t ht
  let t' : Time := ⟨t, ⟨ha.trans ht.1.le, ht.2.trans hb⟩⟩
  change γ t' = γ d
  rcases le_total t' d with htd | hdt
  · exact heq ht hd htd
  · exact (heq hd ht hdt).symm

lemma zero_on_initial_support_gap {γ : ℝ → ℝ} {μ : Measure Time}
    (hγ : IsOrderParameter γ) (hμ : IsStieltjesMeasure γ μ) {b : ℝ}
    (hb : b < 1) (h0 : ¬ InSupport μ 0)
    (hgap : ∀ t ∈ Ioo 0 b, ¬ InSupport μ t) :
    ∀ t ∈ Ioo 0 b, γ t = 0 := by
  intro t ht
  let t' : Time := ⟨t, ⟨ht.1.le, ht.2.trans hb⟩⟩
  have hm : μ (Iic t') = 0 := by
    apply IsStieltjesMeasure.measure_zero_of_disjoint_support
    rw [Set.disjoint_left]
    intro z hz hzs
    by_cases hz0 : (z : ℝ) = 0
    · exact h0 (hz0 ▸ ⟨z.property, hzs⟩)
    · exact hgap z ⟨lt_of_le_of_ne z.property.1 (Ne.symm hz0), hz.trans_lt ht.2⟩
        ⟨z.property, hzs⟩
  rw [hμ t', ENNReal.ofReal_eq_zero] at hm
  exact le_antisymm hm (hγ.nonneg t' t'.property)

lemma IsStieltjesMeasure.finiteOnCompacts {γ : ℝ → ℝ} {μ : Measure Time}
    (hμ : IsStieltjesMeasure γ μ) : IsFiniteMeasureOnCompacts μ := by
  constructor
  intro K hK
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  · obtain ⟨b, hb⟩ := (hK.image continuous_subtype_val).exists_isGreatest (hne.image Subtype.val)
    obtain ⟨b', hb'K, rfl⟩ := hb.1
    apply lt_of_le_of_lt (measure_mono (t := Iic b') ?_)
    · rw [hμ b']; exact ENNReal.ofReal_lt_top
    · intro t ht; exact hb.2 ⟨t, ht, rfl⟩

lemma isCompact_time_Iic (b : Time) : IsCompact (Iic b) := by
  rw [Subtype.isCompact_iff]
  have heq : Subtype.val '' Iic b = Icc (0 : ℝ) b := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨u.property.1, hu⟩
    · intro ht
      exact ⟨⟨t, ⟨ht.1, ht.2.trans_lt b.property.2⟩⟩, ht.2, rfl⟩
  rw [heq]
  exact isCompact_Icc

end ZeroTemperatureSK.SupportDeterministic

namespace ZeroTemperatureSK.SupportDeterministic.Variation

lemma continuous_zero_on_support_of_integral_nonpos
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    {ν : Measure Y} {F : Y → ℝ} (hF : Continuous F)
    (hF0 : ∀ x, 0 ≤ F x) (hFi : Integrable F ν) (hI : ∫ x, F x ∂ν ≤ 0) :
    ∀ x ∈ ν.support, F x = 0 := by
  have hz : ∫ x, F x ∂ν = 0 := le_antisymm hI (integral_nonneg hF0)
  have hae : F =ᵐ[ν] 0 := (integral_eq_zero_iff_of_nonneg hF0 hFi).mp hz
  intro x hx
  by_contra hne
  have hn : {y | F y ≠ 0} ∈ 𝓝 x :=
    (isOpen_ne.preimage hF).mem_nhds hne
  have hp : 0 < ν {y | F y ≠ 0} := (ν.mem_support_iff_forall x).mp hx _ hn
  have hzset : ν {y | F y ≠ 0} = 0 := by
    simpa only [Filter.EventuallyEq, ae_iff, Pi.zero_apply] using hae
  exact hp.ne' hzset

theorem zero_on_support_of_compact_mass_removal {γ G : ℝ → ℝ} {μ : Measure Time}
    (hμ : IsStieltjesMeasure γ μ)
    (hGc : ContinuousOn G (Ico (0 : ℝ) 1))
    (hG0 : ∀ t ∈ Ico (0 : ℝ) 1, 0 ≤ G t)
    (hremove : ∀ K : Set Time, IsCompact K → ∫ t in K, G t ∂μ ≤ 0) :
    ∀ t, InSupport μ t → G t = 0 := by
  let : IsFiniteMeasureOnCompacts μ := hμ.finiteOnCompacts
  have hcont : Continuous (fun t : Time => G t) :=
    continuousOn_iff_continuous_domRestrict.mp hGc
  intro t ht
  obtain ⟨ht, hts⟩ := ht
  let x : Time := ⟨t,ht⟩
  let b : Time := ⟨(t+1)/2, by constructor <;> linarith [ht.1, ht.2]⟩
  have hxb : x < b := by change t < (t+1)/2; linarith [ht.2]
  have hxint : x ∈ interior (Iic b) :=
    mem_interior_iff_mem_nhds.mpr (mem_of_superset (Iio_mem_nhds hxb) Iio_subset_Iic_self)
  have hxs : x ∈ (μ.restrict (Iic b)).support := μ.interior_inter_support ⟨hxint, hts⟩
  exact continuous_zero_on_support_of_integral_nonpos hcont
    (fun y => hG0 y y.property)
    (hcont.continuousOn.integrableOn_compact (isCompact_time_Iic b))
    (hremove (Iic b) (isCompact_time_Iic b)) x hxs

lemma value_contact_of_potential_min {q G : ℝ → ℝ} {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hG0 : ∀ t ∈ Ico (0 : ℝ) 1, 0 ≤ G t)
    (hGs : G s = 0) (hGd : HasDerivAt G (s - q s) s) : q s = s := by
  have hmin : IsLocalMin G s := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
    rw [hGs]
    exact hG0 t ⟨ht.1.le, ht.2⟩
  have hzero := hmin.hasDerivAt_eq_zero hGd
  linarith

lemma derivative_contact_of_potential_min {q G : ℝ → ℝ} {s d : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1)
    (hGc : ContinuousOn G (Ico (0 : ℝ) 1))
    (hG0 : ∀ t ∈ Ico (0 : ℝ) 1, 0 ≤ G t)
    (hGs : G s = 0) (hqs : q s = s)
    (hqd : HasDerivWithinAt q d (Ici s) s)
    (hGd : ∀ t ∈ Ioo s 1, HasDerivAt G (t - q t) t) : d ≤ 1 := by
  by_contra hd
  have hd : 1 < d := lt_of_not_ge hd
  have hsel : Ici s \ {s} = Ioi s := by ext t; simp
  have hlim : Tendsto (slope q s) (𝓝[>] s) (𝓝 d) := by
    simpa only [hsel] using (hasDerivWithinAt_iff_tendsto_slope.mp hqd)
  have he : ∀ᶠ t in 𝓝[>] s, 1 < slope q s t ∧ t < 1 :=
    (hlim.eventually (Ioi_mem_nhds hd)).and
      (mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hs.2))
  obtain ⟨b, hsb, hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  obtain ⟨y, hsy, hyb⟩ := exists_between (show s < b from hsb)
  have hy1 : y < 1 := (hb ⟨hsy, hyb⟩).2
  have hanti : StrictAntiOn G (Icc s y) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc s y)
      (hGc.mono (by intro t ht; exact ⟨hs.1.trans ht.1, ht.2.trans_lt hy1⟩))
    intro t ht
    rw [interior_Icc] at ht
    have hslt := (hb ⟨ht.1, ht.2.trans hyb⟩).1
    have hgt : t < q t := by
      rw [slope_def_field, hqs, lt_div_iff₀ (sub_pos.mpr ht.1)] at hslt
      linarith
    rw [(hGd t ⟨ht.1, ht.2.trans hy1⟩).deriv]
    exact sub_neg.mpr hgt
  have hneg := hanti (left_mem_Icc.mpr hsy.le) (right_mem_Icc.mpr hsy.le) hsy
  rw [hGs] at hneg
  exact (not_lt_of_ge (hG0 y ⟨hs.1.trans hsy.le, hy1⟩)) hneg

theorem contact_conditions {γ q q' G : ℝ → ℝ} {μ : Measure Time}
    (hμ : IsStieltjesMeasure γ μ)
    (hGc : ContinuousOn G (Ico (0 : ℝ) 1))
    (hG0 : ∀ t ∈ Ico (0 : ℝ) 1, 0 ≤ G t)
    (hremove : ∀ K : Set Time, IsCompact K → ∫ t in K, G t ∂μ ≤ 0)
    (hq0 : q 0 = 0)
    (hqderiv : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt q (q' t) (Ici t) t)
    (hGderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt G (t - q t) t) :
    ∀ t, InSupport μ t → q t = t ∧ q' t ≤ 1 := by
  intro t ht
  have ht01 : t ∈ Ico (0 : ℝ) 1 := ht.choose
  have hGt : G t = 0 := zero_on_support_of_compact_mass_removal hμ hGc hG0 hremove t ht
  have hqt : q t = t := by
    rcases eq_or_lt_of_le ht01.1 with ht0 | htpos
    · simpa only [← ht0] using hq0
    · exact value_contact_of_potential_min ⟨htpos, ht01.2⟩ hG0 hGt
        (hGderiv t ⟨htpos, ht01.2⟩)
  exact ⟨hqt, derivative_contact_of_potential_min ht01 hGc hG0 hGt hqt (hqderiv t ht01)
    (fun s hs => hGderiv s ⟨ht01.1.trans_lt hs.1, hs.2⟩)⟩

noncomputable def contactPotential (q : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in s..1, q t - t

lemma contact_integrable {q : ℝ → ℝ}
    (hqc : ContinuousOn q (Ico (0 : ℝ) 1))
    (hqbound : ∀ t ∈ Ico (0 : ℝ) 1, |q t| ≤ 1) :
    IntegrableOn (fun t => q t - t) (Icc (0 : ℝ) 1) := by
  apply (integrableOn_Icc_iff_integrableOn_Ico).mpr
  apply (integrableOn_const (C := (2 : ℝ)) measure_Ico_lt_top.ne).mono'
    ((hqc.sub continuousOn_id).aestronglyMeasurable measurableSet_Ico)
  filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
  calc
    ‖q t - t‖ = |q t - t| := Real.norm_eq_abs _
    _ ≤ |q t| + |t| := abs_sub _ _
    _ ≤ 2 := by rw [abs_of_nonneg ht.1]; linarith [hqbound t ht, ht.2]

lemma contactPotential_continuousOn {q : ℝ → ℝ}
    (hqi : IntegrableOn (fun t => q t - t) (Icc (0 : ℝ) 1)) :
    ContinuousOn (contactPotential q) (Icc (0 : ℝ) 1) := by
  have hqi' : IntegrableOn (fun t => q t - t) (uIcc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using hqi
  change ContinuousOn (fun s => ∫ t in s..1, q t - t) (Icc (0 : ℝ) 1)
  simpa only [uIcc_of_le zero_le_one] using
    intervalIntegral.continuousOn_primitive_interval_left hqi'

lemma contactPotential_hasDerivAt {q : ℝ → ℝ}
    (hqi : IntegrableOn (fun t => q t - t) (Icc (0 : ℝ) 1))
    (hqc : ContinuousOn q (Ico (0 : ℝ) 1))
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (contactPotential q) (s - q s) s := by
  have hfi : IntervalIntegrable (fun t => q t - t) volume s 1 := by
    apply IntegrableOn.intervalIntegrable
    rw [uIcc_of_le hs.2.le]
    exact hqi.mono_set (by intro t ht; exact ⟨hs.1.le.trans ht.1, ht.2⟩)
  have hcont : ContinuousOn (fun t => q t - t) (Ioo (0 : ℝ) 1) :=
    (hqc.mono Ioo_subset_Ico_self).sub continuousOn_id
  have hd := intervalIntegral.integral_hasDerivAt_left hfi
    (hcont.stronglyMeasurableAtFilter isOpen_Ioo s hs)
    (hcont.continuousAt (Ioo_mem_nhds hs.1 hs.2))
  change HasDerivAt (fun s => ∫ t in s..1, q t - t) (s - q s) s
  simpa only [neg_sub] using hd

end ZeroTemperatureSK.SupportDeterministic.Variation

namespace ZeroTemperatureSK.SupportDeterministic.Variation

theorem no_gap_of_derivative_lt_one {q q' : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hc : ContinuousOn q (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt q (q' t) t)
    (ha : q a = a) (hb : q b = b)
    (hbound : ∀ t ∈ Ioo a b, q' t < 1) : False := by
  obtain ⟨t, ht, heq⟩ := exists_hasDerivAt_eq_slope q q' hab hc hd
  rw [ha, hb, div_self (sub_ne_zero.mpr hab.ne')] at heq
  exact (hbound t ht).ne heq

theorem no_gap_of_strictConvex_derivative {q q' : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hc : ContinuousOn q (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt q (q' t) t)
    (ha : q a = a) (hb : q b = b)
    (hconvex : StrictConvexOn ℝ (Icc a b) q')
    (hda : q' a ≤ 1) (hdb : q' b ≤ 1) : False := by
  apply no_gap_of_derivative_lt_one hab hc hd ha hb
  intro t ht
  exact (hconvex.lt_on_openSegment
      (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le)
      hab.ne (Ioo_subset_openSegment ht)).trans_le (max_le hda hdb)

theorem no_positive_constant_gap {q q' : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hc : ContinuousOn q (Icc a b))
    (hc' : ContinuousOn q' (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt q (q' t) t)
    (ha : q a = a) (hb : q b = b)
    (hcurvature : ∀ t ∈ Ioo a b, 0 < (deriv^[2] q') t)
    (hda : q' a ≤ 1) (hdb : q' b ≤ 1) : False := by
  apply no_gap_of_strictConvex_derivative hab hc hd ha hb ?_ hda hdb
  apply strictConvexOn_of_deriv2_pos (convex_Icc a b) hc'
  simpa only [interior_Icc] using hcurvature

theorem no_zero_constant_gap {q q' : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hc : ContinuousOn q (Icc a b))
    (hc' : ContinuousOn q' (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt q (q' t) t)
    (ha : q a = a) (hb : q b = b)
    (hcurvature : ∀ t ∈ Ioo a b, 0 < deriv q' t)
    (hdb : q' b ≤ 1) : False := by
  have hm : StrictMonoOn q' (Icc a b) :=
    strictMonoOn_of_deriv_pos (convex_Icc a b) hc'
      (by simpa only [interior_Icc] using hcurvature)
  apply no_gap_of_derivative_lt_one hab hc hd ha hb
  intro t ht
  exact (hm (Ioo_subset_Icc_self ht) (right_mem_Icc.mpr hab.le) ht.2).trans_le hdb

end ZeroTemperatureSK.SupportDeterministic.Variation

namespace ZeroTemperatureSK.SupportDeterministic.Variation

theorem full_support_of_contact_and_gap_curvature
    {γ q q' : ℝ → ℝ} {μ : Measure Time}
    (hγ : IsOrderParameter γ) (hμ : IsStieltjesMeasure γ μ)
    (hc : ContinuousOn q (Ico (0 : ℝ) 1))
    (hc' : ContinuousOn q' (Ico (0 : ℝ) 1))
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt q (q' t) t)
    (hq0 : q 0 = 0)
    (hcontact : ∀ t, InSupport μ t → q t = t ∧ q' t ≤ 1)
    (hend : ¬ ∃ a c : ℝ, 0 ≤ a ∧ a < 1 ∧ 0 ≤ c ∧
      ∀ t ∈ Ioo a 1, γ t = c)
    (hpositive : ∀ a b c : ℝ, 0 ≤ a → a < b → b < 1 → 0 < c →
      (∀ t ∈ Ioo a b, γ t = c) → ∀ t ∈ Ioo a b, 0 < (deriv^[2] q') t)
    (hzero : ∀ a b : ℝ, 0 ≤ a → a < b → b < 1 →
      (∀ t ∈ Ioo a b, γ t = 0) → ∀ t ∈ Ioo a b, 0 < deriv q' t) :
    μ.support = univ ∧ StrictMonoOn γ (Ico (0 : ℝ) 1) ∧
      ∀ t ∈ Ico (0 : ℝ) 1, q t = t := by
  have hS : μ.support = univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    obtain ⟨a, b, ha, hab, hb, haS, hbS, hgap⟩ :=
      exists_support_gap hx (support_cofinal_of_no_terminal_plateau hγ hμ hend x)
    have hsub : Icc a b ⊆ Ico (0 : ℝ) 1 := by
      intro t ht; exact ⟨ha.trans ht.1, ht.2.trans_lt hb⟩
    have hderiv : ∀ t ∈ Ioo a b, HasDerivAt q (q' t) t := by
      intro t ht; exact hd t ⟨ha.trans_lt ht.1, ht.2.trans hb⟩
    have hqa : q a = a := by
      rcases haS with rfl | haS
      · exact hq0
      · exact (hcontact a haS).1
    have hqb : q b = b := (hcontact b hbS).1
    have hdb : q' b ≤ 1 := (hcontact b hbS).2
    obtain ⟨c, hc0, hconstant⟩ := constant_on_support_gap hγ hμ ha hab hb hgap
    rcases eq_or_lt_of_le hc0 with heq | hpos
    · apply no_zero_constant_gap hab (hc.mono hsub) (hc'.mono hsub) hderiv hqa hqb
        (hzero a b ha hab hb (by simpa only [← heq] using hconstant)) hdb
    · have hda : q' a ≤ 1 := by
        by_cases haS' : InSupport μ a
        · exact (hcontact a haS').2
        · have ha0 : a = 0 := haS.resolve_right haS'
          subst a
          have hz := zero_on_initial_support_gap hγ hμ hb haS' hgap
          have hmid : b / 2 ∈ Ioo (0 : ℝ) b := by constructor <;> linarith
          have heq : c = 0 := (hconstant _ hmid).symm.trans (hz _ hmid)
          exact False.elim (hpos.ne' heq)
      exact no_positive_constant_gap hab (hc.mono hsub) (hc'.mono hsub)
        hderiv hqa hqb (hpositive a b c ha hab hb hpos hconstant) hda hdb
  refine ⟨hS, hμ.strictMonoOn_of_full_support hS, ?_⟩
  intro t ht
  exact (hcontact t ⟨ht, by rw [hS]; trivial⟩).1

theorem derivative_eq_one_of_full_contact {q q' : ℝ → ℝ}
    (hq : ∀ t ∈ Ico (0 : ℝ) 1, q t = t)
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt q (q' t) t)
    (hd0 : HasDerivWithinAt q (q' 0) (Ici (0 : ℝ)) 0) :
    ∀ t ∈ Ico (0 : ℝ) 1, q' t = 1 := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with ht0 | htpos
  · subst t
    have heq : q =ᶠ[𝓝[Ici (0 : ℝ)] 0] id := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with x hx hx1
      exact hq x ⟨hx, hx1⟩
    have hid : HasDerivWithinAt q 1 (Ici (0 : ℝ)) 0 :=
      (hasDerivAt_id (0 : ℝ)).hasDerivWithinAt.congr_of_eventuallyEq heq (hq 0 (by simp))
    exact (hd0.derivWithin (uniqueDiffWithinAt_Ici 0)).symm.trans
      (hid.derivWithin (uniqueDiffWithinAt_Ici 0))
  · have heq : q =ᶠ[𝓝 t] id := by
      filter_upwards [Ioo_mem_nhds htpos ht.2] with x hx
      exact hq x ⟨hx.1.le, hx.2⟩
    have hid : HasDerivAt q 1 t := (hasDerivAt_id t).congr_of_eventuallyEq heq
    exact (hd t ⟨htpos, ht.2⟩).unique hid

end ZeroTemperatureSK.SupportDeterministic.Variation

end

end OAI

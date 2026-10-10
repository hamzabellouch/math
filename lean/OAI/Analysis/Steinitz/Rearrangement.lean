import OAI.Analysis.Steinitz.KernelConvexity

namespace OAI

/-! Vertical Steiner rearrangement and shifted section geometry. -/

section

open Set MeasureTheory
open scoped Pointwise
namespace ShiftedSections
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def sectionDomain (K : Set E) (e : E) (ell s : ℝ) : Set E :=
  {y | ∃ c : ℝ, |c|+s < ell ∧ y+(c-s) • e ∈ K ∧ y+(c+s) • e ∈ K}

lemma section_open {K : Set E} (hK : IsOpen K) (e : E) (ell s : ℝ) :
    IsOpen (sectionDomain K e ell s) := by
  have he : sectionDomain K e ell s =
      ⋃ c : ℝ, ⋃ (_ : |c|+s<ell),
        ((fun y : E => y+(c-s) • e) ⁻¹' K) ∩ ((fun y : E => y+(c+s) • e) ⁻¹' K) := by
    ext y
    simp only [sectionDomain, mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage]
    aesop
  rw [he]
  apply isOpen_iUnion
  intro c
  apply isOpen_iUnion
  intro _
  exact (hK.preimage (by fun_prop)).inter (hK.preimage (by fun_prop))

lemma section_mix {K : Set E} (hK : Convex ℝ K) (e : E) (ell : ℝ)
    {y z : E} {s r a b : ℝ} (hy : y ∈ sectionDomain K e ell s)
    (hz : z ∈ sectionDomain K e ell r) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    a • y+b • z ∈ sectionDomain K e ell (a*s+b*r) := by
  obtain ⟨c,hc,hcl,hcr⟩ := hy
  obtain ⟨d,hd,hdl,hdr⟩ := hz
  refine ⟨a*c+b*d, ?_, ?_, ?_⟩
  · have hleft : |a*c+b*d| ≤ a*|c|+b*|d| := by
      simpa only [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] using abs_add_le (a*c) (b*d)
    have hstrict : a*(|c|+s)+b*(|d|+r) < ell := by
      rcases eq_or_lt_of_le ha with he | hp
      · have ha0 : a=0 := he.symm
        have hb1 : b=1 := by linarith
        simpa only [ha0,hb1,zero_mul,one_mul,zero_add] using hd
      · have h₁ := mul_lt_mul_of_pos_left hc hp
        have h₂ := mul_le_mul_of_nonneg_left hd.le hb
        have he : a*ell+b*ell=ell := by rw [← add_mul, hab, one_mul]
        linarith
    nlinarith
  · convert hK hcl hdl ha hb hab using 1; module
  · convert hK hcr hdr ha hb hab using 1; module

lemma section_convex {K : Set E} (hK : Convex ℝ K) (e : E) (ell s : ℝ) :
    Convex ℝ (sectionDomain K e ell s) := by
  intro y hy z hz a b ha hb hab
  have h := section_mix hK e ell hy hz ha hb hab
  have hs : a*s+b*s=s := by rw [← add_mul, hab, one_mul]
  rwa [hs] at h

lemma line_segment_mem {K : Set E} (hK : Convex ℝ K) {y e : E} {c z : ℝ}
    (hleft : y+(c-1) • e ∈ K) (hright : y+(c+1) • e ∈ K)
    (hz : c-1 ≤ z ∧ z ≤ c+1) : y+z • e ∈ K := by
  have ha : 0 ≤ (c+1-z)/2 := by linarith [hz.2]
  have hb : 0 ≤ (z-c+1)/2 := by linarith [hz.1]
  have hab : (c+1-z)/2+(z-c+1)/2=1 := by ring
  convert hK hleft hright ha hb hab using 1; module

lemma section_symmetric {K : Set E} (hK : ∀ x ∈ K, -x ∈ K) (e : E) (ell s : ℝ) :
    ∀ y ∈ sectionDomain K e ell s, -y ∈ sectionDomain K e ell s := by
  intro y hy
  obtain ⟨c,hc,hcl,hcr⟩ := hy
  refine ⟨-c,by simpa only [abs_neg] using hc,?_,?_⟩
  · convert hK _ hcr using 1; module
  · convert hK _ hcl using 1; module

lemma shifted_step {K : Set E} (hK : Convex ℝ K) (e : E)
    {y : E} (hy : y ∈ sectionDomain K e (5/2) 1) {q : ℝ} (hq : |q|≤1/4) :
    ∃ ε : ℝ, (ε = -1 ∨ ε = 1) ∧ y+(q+ε) • e ∈ K := by
  obtain ⟨c,hc,hcl,hcr⟩ := hy
  have hca : |c|<3/2 := by linarith
  have hcb : -(3/2)<c ∧ c<3/2 := abs_lt.mp hca
  have hqb : -(1/4)≤q ∧ q≤1/4 := abs_le.mp hq
  rcases le_total q c with h | h
  · refine ⟨1,Or.inr rfl,line_segment_mem hK hcl hcr ?_⟩
    constructor <;> linarith [hcb.1,hcb.2,hqb.1,hqb.2]
  · refine ⟨-1,Or.inl rfl,line_segment_mem hK hcl hcr ?_⟩
    constructor <;> linarith [hcb.1,hcb.2,hqb.1,hqb.2]

lemma zero_mem_of_symmetric_convex {K : Set E} (hK : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hne : K.Nonempty) : (0:E) ∈ K := by
  obtain ⟨x,hx⟩ := hne
  have h := hK hx (hsym x hx) (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)+1/2=1)
  simpa only [smul_neg, add_neg_cancel] using h

end ShiftedSections

end

section

open MeasureTheory Set Filter
open scoped ENNReal
namespace VerticalRearrangement

section Layer
variable {X U V : Type*} [MeasurableSpace X] [MeasurableSpace U] [MeasurableSpace V]
  {μ : Measure X} {ν : Measure U} {ρ : Measure V} [SFinite μ] [SFinite ν] [SFinite ρ]

lemma layer_pair (a : X → U → ℝ≥0∞) (b : X → V → ℝ≥0∞)
    (ha : Measurable (Function.uncurry a)) (hb : Measurable (Function.uncurry b)) :
    (∫⁻ x, (∫⁻ u, a x u ∂ν) * (∫⁻ v, b x v ∂ρ) ∂μ) =
      ∫⁻ u, ∫⁻ v, ∫⁻ x, a x u * b x v ∂μ ∂ρ ∂ν := by
  have hai (x : X) : Measurable (a x) := ha.comp measurable_prodMk_left
  have hbi (x : X) : Measurable (b x) := hb.comp measurable_prodMk_left
  simp_rw [← lintegral_mul_const _ (hai _), ← lintegral_const_mul _ (hbi _)]
  rw [lintegral_lintegral_swap]
  · apply lintegral_congr
    intro u
    apply lintegral_lintegral_swap
    exact ((ha.comp (measurable_fst.prodMk measurable_const)).mul
      (hb.comp (measurable_fst.prodMk measurable_snd))).aemeasurable
  · apply Measurable.aemeasurable
    apply Measurable.lintegral_prod_right
    exact (ha.comp (measurable_fst.fst.prodMk measurable_fst.snd)).mul
      (hb.comp (measurable_fst.fst.prodMk measurable_snd))

noncomputable def layer (S : U → Set X) (ν : Measure U) (x : X) : ℝ≥0∞ :=
  ∫⁻ u, (S u).indicator (fun _ => (1 : ℝ≥0∞)) x ∂ν

lemma layer_measurable (S : U → Set X) (hS : MeasurableSet {p : X × U | p.1 ∈ S p.2}) :
    Measurable (layer S ν) := by
  apply Measurable.lintegral_prod_right
  exact measurable_const.indicator hS

lemma layer_pair_sets (S : U → Set X) (T : V → Set X)
    (hS : MeasurableSet {p : X × U | p.1 ∈ S p.2})
    (hT : MeasurableSet {p : X × V | p.1 ∈ T p.2}) :
    (∫⁻ x, layer S ν x * layer T ρ x ∂μ) =
      ∫⁻ u, ∫⁻ v, μ (S u ∩ T v) ∂ρ ∂ν := by
  unfold layer
  rw [layer_pair (fun x u => (S u).indicator (fun _ => (1:ℝ≥0∞)) x)
    (fun x v => (T v).indicator (fun _ => (1:ℝ≥0∞)) x)
    (measurable_const.indicator hS) (measurable_const.indicator hT)]
  apply lintegral_congr
  intro u
  apply lintegral_congr
  intro v
  have hs : MeasurableSet (S u) := hS.preimage measurable_prodMk_right
  have ht : MeasurableSet (T v) := hT.preimage measurable_prodMk_right
  have he (x : X) : (S u).indicator (fun _ => (1:ℝ≥0∞)) x *
      (T v).indicator (fun _ => (1:ℝ≥0∞)) x = (S u ∩ T v).indicator (fun _ => (1:ℝ≥0∞)) x := by
    by_cases hx : x ∈ S u <;> by_cases hy : x ∈ T v <;> simp [hx,hy]
  simp_rw [he]
  rw [lintegral_indicator (hs.inter ht), lintegral_one, Measure.restrict_apply_univ]

end Layer

lemma measure_inter_eq_min_of_nested {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (S T : Set X) (h : S ⊆ T ∨ T ⊆ S) : μ (S ∩ T) = min (μ S) (μ T) := by
  rcases h with h | h
  · rw [inter_eq_left.mpr h, min_eq_left (measure_mono h)]
  · rw [inter_eq_right.mpr h, min_eq_right (measure_mono h)]

noncomputable def centered (a : ℝ≥0∞) : Set ℝ :=
  {s | |s| < a.toReal / 2}

lemma centered_measurable (a : ℝ≥0∞) : MeasurableSet (centered a) :=
  measurableSet_lt measurable_id.abs measurable_const

lemma measure_centered {a : ℝ≥0∞} (ha : a ≠ ⊤) : volume (centered a) = a := by
  have he : centered a = Ioo (-(a.toReal/2)) (a.toReal/2) := by
    ext s
    change |s| < a.toReal / 2 ↔ -(a.toReal/2) < s ∧ s < a.toReal/2
    exact abs_lt
  rw [he, Real.volume_Ioo, show a.toReal/2 - -(a.toReal/2) = a.toReal by ring,
    ENNReal.ofReal_toReal ha]

lemma centered_mono {a b : ℝ≥0∞} (ha : a ≤ b) (hb : b ≠ ⊤) : centered a ⊆ centered b := by
  intro s hs
  exact hs.trans_le (div_le_div_of_nonneg_right (ENNReal.toReal_mono hb ha) (by norm_num))

lemma centered_inter {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    volume (centered a ∩ centered b) = min a b := by
  rcases le_total a b with h | h
  · rw [inter_eq_left.mpr (centered_mono h hb), measure_centered ha, min_eq_left h]
  · rw [inter_eq_right.mpr (centered_mono h ha), measure_centered hb, min_eq_right h]

noncomputable def heightMeasure : Measure ℝ :=
  volume.withDensity (fun s : ℝ => ENNReal.ofReal |s|)

instance : SFinite heightMeasure := by
  unfold heightMeasure
  infer_instance

lemma integral_abs_symmetric {r : ℝ} (hr : 0 ≤ r) :
    (∫ s : ℝ in -r..r, |s|) = r^2 := by
  have hl : (∫ s : ℝ in -r..0, |s|) = r^2/2 := by
    have he : (∫ s : ℝ in -r..0, |s|) = ∫ s : ℝ in -r..0, -s := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by linarith : -r ≤ (0:ℝ))] at hx
      exact abs_of_nonpos hx.2
    rw [he, intervalIntegral.integral_neg, integral_id]
    ring
  have hu : (∫ s : ℝ in 0..r, |s|) = r^2/2 := by
    have he : (∫ s : ℝ in 0..r, |s|) = ∫ s : ℝ in 0..r, s := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hr] at hx
      exact abs_of_nonneg hx.1
    rw [he, integral_id]
    ring
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_abs.intervalIntegrable (-r) 0) (continuous_abs.intervalIntegrable 0 r), hl, hu]
  ring

lemma heightMeasure_centered {a : ℝ≥0∞} (ha : a ≠ ⊤) :
    heightMeasure (centered a) = a^2/4 := by
  have he : centered a = Ioo (-(a.toReal/2)) (a.toReal/2) := by
    ext s
    change |s| < a.toReal/2 ↔ -(a.toReal/2) < s ∧ s < a.toReal/2
    exact abs_lt
  have hi : IntegrableOn (fun s : ℝ => |s|) (centered a) := by
    rw [he]
    exact continuous_abs.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [heightMeasure, withDensity_apply _ (centered_measurable a),
    ← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun _ => abs_nonneg _))]
  rw [he, restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le (by linarith [ENNReal.toReal_nonneg (a := a)] : -(a.toReal/2) ≤ a.toReal/2),
    integral_abs_symmetric (by positivity)]
  rw [div_pow, ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_pow
    ENNReal.toReal_nonneg, ENNReal.ofReal_toReal ha]
  norm_num

lemma heightMeasure_centered_inter {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    heightMeasure (centered a ∩ centered b) = (min a b)^2/4 := by
  rcases le_total a b with h | h
  · rw [inter_eq_left.mpr (centered_mono h hb), heightMeasure_centered ha, min_eq_left h]
  · rw [inter_eq_right.mpr (centered_mono h ha), heightMeasure_centered hb, min_eq_right h]

section Rearranged
variable {X U V : Type*} [MeasurableSpace X] [MeasurableSpace U] [MeasurableSpace V]
  {μ : Measure X} {ν : Measure U} {ρ : Measure V} [SFinite μ] [SFinite ν] [SFinite ρ]

lemma measure_family_measurable (S : U → Set X)
    (hS : MeasurableSet {p : X × U | p.1 ∈ S p.2}) :
    Measurable (fun u => μ (S u)) := by
  have he (u : U) : μ (S u) = ∫⁻ x, (S u).indicator (fun _ => (1:ℝ≥0∞)) x ∂μ := by
    have hs : MeasurableSet (S u) := hS.preimage measurable_prodMk_right
    rw [lintegral_indicator hs, lintegral_one, Measure.restrict_apply_univ]
  simp_rw [he]
  apply Measurable.lintegral_prod_left
  exact measurable_const.indicator hS

noncomputable def rearranged (S : U → Set X) (μ : Measure X) (ν : Measure U) : ℝ → ℝ≥0∞ :=
  layer (fun u => centered (μ (S u))) ν

lemma centered_family_measurable (S : U → Set X)
    (hS : MeasurableSet {p : X × U | p.1 ∈ S p.2}) :
    MeasurableSet {p : ℝ × U | p.1 ∈ centered (μ (S p.2))} := by
  exact measurableSet_lt measurable_fst.abs
    (((measure_family_measurable S hS).comp measurable_snd).ennreal_toReal.div_const 2)

lemma rearranged_measurable (S : U → Set X)
    (hS : MeasurableSet {p : X × U | p.1 ∈ S p.2}) : Measurable (rearranged S μ ν) :=
  layer_measurable _ (centered_family_measurable S hS)

lemma rearranged_pair (S : U → Set X) (T : V → Set X)
    (hS : MeasurableSet {p : X × U | p.1 ∈ S p.2})
    (hT : MeasurableSet {p : X × V | p.1 ∈ T p.2})
    (hfS : ∀ u, μ (S u) ≠ ⊤) (hfT : ∀ v, μ (T v) ≠ ⊤) :
    (∫⁻ s, rearranged S μ ν s * rearranged T μ ρ s) =
      ∫⁻ u, ∫⁻ v, min (μ (S u)) (μ (T v)) ∂ρ ∂ν := by
  unfold rearranged
  rw [layer_pair_sets _ _ (centered_family_measurable S hS) (centered_family_measurable T hT)]
  simp_rw [centered_inter (hfS _) (hfT _)]

lemma rearranged_inner_ge (S : U → Set X) (T : V → Set X)
    (hS : MeasurableSet {p : X × U | p.1 ∈ S p.2})
    (hT : MeasurableSet {p : X × V | p.1 ∈ T p.2})
    (hfS : ∀ u, μ (S u) ≠ ⊤) (hfT : ∀ v, μ (T v) ≠ ⊤) :
    (∫⁻ x, layer S ν x * layer T ρ x ∂μ) ≤
      ∫⁻ s, rearranged S μ ν s * rearranged T μ ρ s := by
  rw [layer_pair_sets S T hS hT, rearranged_pair S T hS hT hfS hfT]
  apply lintegral_mono
  intro u
  apply lintegral_mono
  intro v
  exact le_min (measure_mono inter_subset_left) (measure_mono inter_subset_right)

lemma rearranged_square (S : U → Set X)
    (hS : MeasurableSet {p : X × U | p.1 ∈ S p.2})
    (hfS : ∀ u, μ (S u) ≠ ⊤) (hnest : ∀ u v, S u ⊆ S v ∨ S v ⊆ S u) :
    (∫⁻ s, (rearranged S μ ν s)^2) = ∫⁻ x, (layer S ν x)^2 ∂μ := by
  simp only [pow_two]
  rw [rearranged_pair S S hS hS hfS hfS, layer_pair_sets S S hS hS]
  simp_rw [measure_inter_eq_min_of_nested μ _ _ (hnest _ _)]

lemma rearranged_height (S : U → Set X)
    (hS : MeasurableSet {p : X × U | p.1 ∈ S p.2})
    (hfS : ∀ u, μ (S u) ≠ ⊤) :
    (∫⁻ s, ENNReal.ofReal |s| * (rearranged S μ ν s)^2) =
      ∫⁻ u, ∫⁻ v, (min (μ (S u)) (μ (S v)))^2/4 ∂ν ∂ν := by
  have hm : Measurable (fun s : ℝ => (rearranged S μ ν s)^2) :=
    (rearranged_measurable (μ := μ) (ν := ν) S hS).pow_const 2
  have he := lintegral_withDensity_eq_lintegral_mul volume
    (f := fun s : ℝ => ENNReal.ofReal |s|) (g := fun s => (rearranged S μ ν s)^2)
    measurable_id.abs.ennreal_ofReal hm
  change (∫⁻ s, ((fun s : ℝ => ENNReal.ofReal |s|) *
    (fun s => (rearranged S μ ν s)^2)) s) = _
  rw [← he]
  change (∫⁻ s, (rearranged S μ ν s)^2 ∂heightMeasure) = _
  simp only [pow_two]
  unfold rearranged
  rw [layer_pair_sets _ _ (centered_family_measurable S hS) (centered_family_measurable S hS)]
  simp only [heightMeasure_centered_inter (hfS _) (hfS _), pow_two]

lemma prod_family_measurable (S : U → Set X)
    (hS : MeasurableSet {p : X × U | p.1 ∈ S p.2}) :
    MeasurableSet {p : (X × X) × U | p.1 ∈ S p.2 ×ˢ S p.2} := by
  exact (hS.preimage (measurable_fst.fst.prodMk measurable_snd)).inter
    (hS.preimage (measurable_fst.snd.prodMk measurable_snd))

lemma rearranged_height_pair (S : U → Set X)
    (hS : MeasurableSet {p : X × U | p.1 ∈ S p.2})
    (hfS : ∀ u, μ (S u) ≠ ⊤) (hnest : ∀ u v, S u ⊆ S v ∨ S v ⊆ S u) :
    (∫⁻ s, ENNReal.ofReal |s| * (rearranged S μ ν s)^2) =
      (∫⁻ p : X × X, (layer (fun u => S u ×ˢ S u) ν p)^2 ∂μ.prod μ)/4 := by
  rw [rearranged_height S hS hfS]
  simp_rw [ENNReal.div_eq_inv_mul, lintegral_const_mul' _ _ (by norm_num : (4:ℝ≥0∞)⁻¹ ≠ ⊤)]
  congr 1
  simp only [pow_two]
  rw [layer_pair_sets _ _ (prod_family_measurable S hS) (prod_family_measurable S hS)]
  simp_rw [prod_inter_prod, Measure.prod_prod,
    measure_inter_eq_min_of_nested μ _ _ (hnest _ _)]

omit [SFinite μ] [SFinite ν] in
lemma rearranged_eq_zero_of_bound (S : U → Set X) {L : ℝ≥0∞} (hL : L ≠ ⊤)
    (hbound : ∀ u, μ (S u) ≤ L) {s : ℝ} (hs : s ∉ centered L) :
    rearranged S μ ν s = 0 := by
  unfold rearranged layer
  have he (u : U) : (centered (μ (S u))).indicator (fun _ => (1:ℝ≥0∞)) s = 0 := by
    apply indicator_of_notMem
    exact fun h => hs (centered_mono (hbound u) hL h)
  simp only [he, lintegral_zero]

end Rearranged

section FunctionLayers
variable {X : Type*} [MeasurableSpace X]
noncomputable def superlevel (f : X → ℝ) (u : ℝ) : Set X := {x | 0 < u ∧ u < f x}

lemma superlevel_measurable {f : X → ℝ} (hf : Measurable f) :
    MeasurableSet {p : X × ℝ | p.1 ∈ superlevel f p.2} :=
  (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_lt measurable_snd (hf.comp measurable_fst))

omit [MeasurableSpace X] in
lemma layer_superlevel (f : X → ℝ) (x : X) : layer (superlevel f) volume x = ENNReal.ofReal (f x) := by
  have he (u : ℝ) : (superlevel f u).indicator (fun _ => (1:ℝ≥0∞)) x =
      (Ioo 0 (f x)).indicator (fun _ => (1:ℝ≥0∞)) u := by
    by_cases h : 0 < u ∧ u < f x <;> simp [superlevel, h]
  simp_rw [layer, he]
  rw [lintegral_indicator measurableSet_Ioo, lintegral_one,
    Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero]

omit [MeasurableSpace X] in
lemma superlevel_nested (f : X → ℝ) (u v : ℝ) :
    superlevel f u ⊆ superlevel f v ∨ superlevel f v ⊆ superlevel f u := by
  by_cases hu : 0 < u
  · by_cases hv : 0 < v
    · rcases le_total u v with h | h
      · exact Or.inr fun x hx => ⟨hu, h.trans_lt hx.2⟩
      · exact Or.inl fun x hx => ⟨hv, h.trans_lt hx.2⟩
    · exact Or.inr fun x hx => (hv hx.1).elim
  · exact Or.inl fun x hx => (hu hx.1).elim

omit [MeasurableSpace X] in
lemma layer_superlevel_prod (f : X → ℝ) (p : X × X) :
    layer (fun u => superlevel f u ×ˢ superlevel f u) volume p =
      ENNReal.ofReal (min (f p.1) (f p.2)) := by
  have he : (fun u => superlevel f u ×ˢ superlevel f u) =
      superlevel (fun q : X × X => min (f q.1) (f q.2)) := by
    funext u
    ext q
    simp only [superlevel, mem_prod, mem_ofPred_eq, lt_min_iff]
    tauto
  rw [he, layer_superlevel]

lemma function_rearranged_height (μ : Measure X) [SFinite μ] {f : X → ℝ}
    (hf : Measurable f) (hfinite : ∀ u, μ (superlevel f u) ≠ ⊤) :
    (∫⁻ s, ENNReal.ofReal |s| * (rearranged (superlevel f) μ volume s)^2) =
      (∫⁻ x, ∫⁻ y, (ENNReal.ofReal (min (f x) (f y)))^2 ∂μ ∂μ)/4 := by
  rw [rearranged_height_pair _ (superlevel_measurable hf) hfinite (superlevel_nested f)]
  simp_rw [layer_superlevel_prod]
  congr 1
  exact lintegral_prod (μ := μ) (ν := μ) _
    (((hf.comp measurable_fst).min (hf.comp measurable_snd)).ennreal_ofReal.pow_const 2).aemeasurable

end FunctionLayers
end VerticalRearrangement

open MeasureTheory Set Filter
open scoped ENNReal
namespace VerticalRearrangement

section RealLayers
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma ae_finite_of_square {f : X → ℝ≥0∞} (hf : Measurable f)
    (hi : ∫⁻ x, (f x)^2 ∂μ ≠ ⊤) : ∀ᵐ x ∂μ, f x < ⊤ := by
  filter_upwards [ae_lt_top (hf.pow_const 2) hi] with x hx
  by_contra hn
  have he : f x = ⊤ := not_lt_top_iff.mp hn
  simp [he] at hx

lemma toReal_memLp {f : X → ℝ≥0∞} (hf : Measurable f)
    (hi : ∫⁻ x, (f x)^2 ∂μ ≠ ⊤) : MemLp (fun x => (f x).toReal) 2 μ := by
  apply (memLp_two_iff_integrable_sq hf.ennreal_toReal.aestronglyMeasurable).mpr
  simpa only [ENNReal.toReal_pow] using
    integrable_toReal_of_lintegral_ne_top (hf.pow_const 2).aemeasurable hi

lemma integral_toReal_square {f : X → ℝ≥0∞} (hf : Measurable f)
    (hi : ∫⁻ x, (f x)^2 ∂μ ≠ ⊤) :
    (∫ x, (f x).toReal^2 ∂μ) = (∫⁻ x, (f x)^2 ∂μ).toReal := by
  simpa only [ENNReal.toReal_pow] using
    integral_toReal (hf.pow_const 2).aemeasurable (ae_lt_top (hf.pow_const 2) hi)

lemma lintegral_mul_ne_top_of_squares {f g : X → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hfi : ∫⁻ x, (f x)^2 ∂μ ≠ ⊤) (hgi : ∫⁻ x, (g x)^2 ∂μ ≠ ⊤) :
    ∫⁻ x, f x * g x ∂μ ≠ ⊤ := by
  have hi := ((toReal_memLp hf hfi).integrable_mul (toReal_memLp hg hgi)).lintegral_lt_top
  have he : (fun x => ENNReal.ofReal ((f x).toReal*(g x).toReal)) =ᵐ[μ]
      fun x => f x*g x := by
    filter_upwards [ae_finite_of_square hf hfi, ae_finite_of_square hg hgi] with x hx hy
    rw [← ENNReal.toReal_mul, ENNReal.ofReal_toReal (ENNReal.mul_ne_top hx.ne hy.ne)]
  exact (lt_of_eq_of_lt (lintegral_congr_ae he).symm hi).ne

lemma integral_toReal_mul {f g : X → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hfi : ∫⁻ x, (f x)^2 ∂μ ≠ ⊤) (hgi : ∫⁻ x, (g x)^2 ∂μ ≠ ⊤) :
    (∫ x, (f x).toReal*(g x).toReal ∂μ) = (∫⁻ x, f x*g x ∂μ).toReal := by
  apply (integral_congr_ae (ae_of_all _ fun _ => ENNReal.toReal_mul.symm)).trans
  apply integral_toReal (hf.mul hg).aemeasurable
  filter_upwards [ae_finite_of_square hf hfi, ae_finite_of_square hg hgi] with x hx hy
  exact ENNReal.mul_lt_top hx hy

end RealLayers

lemma integral_sub_sq {Y : Type*} [MeasurableSpace Y] {ζ : Measure Y} {f g : Y → ℝ}
      (hf : MemLp f 2 ζ) (hg : MemLp g 2 ζ) :
      (∫ y, (f y-g y)^2 ∂ζ) = (∫ y, (f y)^2 ∂ζ)+(∫ y, (g y)^2 ∂ζ)-2*(∫ y, f y*g y ∂ζ) := by
  have hff : Integrable (fun y => f y^2) ζ := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf
  have hgg : Integrable (fun y => g y^2) ζ := (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mp hg
  have hfg : Integrable (fun y => f y*g y) ζ := hf.integrable_mul hg
  simp_rw [show ∀ y, (f y-g y)^2 = f y^2+g y^2-2*(f y*g y) by intro y; ring]
  have hsum : Integrable (fun y => f y^2+g y^2) ζ := hff.add hgg
  have htwo : Integrable (fun y => 2*(f y*g y)) ζ := hfg.const_mul 2
  rw [integral_sub hsum htwo, integral_add hff hgg, integral_const_mul]

section L2
variable {X U V : Type*} [MeasurableSpace X] [MeasurableSpace U] [MeasurableSpace V]
  {μ : Measure X} {ν : Measure U} {ρ : Measure V} [SFinite μ] [SFinite ν] [SFinite ρ]
variable (S : U → Set X) (T : V → Set X)
    (hS : MeasurableSet {p : X × U | p.1 ∈ S p.2})
    (hT : MeasurableSet {p : X × V | p.1 ∈ T p.2})
    (hfS : ∀ u, μ (S u) ≠ ⊤) (hfT : ∀ v, μ (T v) ≠ ⊤)
    (hnS : ∀ u v, S u ⊆ S v ∨ S v ⊆ S u)
    (hnT : ∀ u v, T u ⊆ T v ∨ T v ⊆ T u)
    (hiS : ∫⁻ x, (layer S ν x)^2 ∂μ ≠ ⊤)
    (hiT : ∫⁻ x, (layer T ρ x)^2 ∂μ ≠ ⊤)

include hS hfS hnS hiS in
lemma rearranged_real_memLp : MemLp (fun s => (rearranged S μ ν s).toReal) 2 volume := by
  apply toReal_memLp (rearranged_measurable (μ := μ) (ν := ν) S hS)
  simpa only [rearranged_square S hS hfS hnS] using hiS

include hS hfS hnS hiS in
lemma rearranged_real_square :
    (∫ s, (rearranged S μ ν s).toReal^2) = ∫ x, (layer S ν x).toReal^2 ∂μ := by
  rw [integral_toReal_square (rearranged_measurable (μ := μ) (ν := ν) S hS)
      (by simpa only [rearranged_square S hS hfS hnS] using hiS),
    integral_toReal_square (layer_measurable S hS) hiS,
    rearranged_square S hS hfS hnS]

include hS hT hfS hfT hnS hnT hiS hiT in
lemma rearranged_real_inner :
    (∫ x, (layer S ν x).toReal*(layer T ρ x).toReal ∂μ) ≤
      ∫ s, (rearranged S μ ν s).toReal*(rearranged T μ ρ s).toReal := by
  have hs := rearranged_measurable (μ := μ) (ν := ν) S hS
  have ht := rearranged_measurable (μ := μ) (ν := ρ) T hT
  have his : ∫⁻ s, (rearranged S μ ν s)^2 ≠ ⊤ := by simpa only [rearranged_square S hS hfS hnS] using hiS
  have hit : ∫⁻ s, (rearranged T μ ρ s)^2 ≠ ⊤ := by simpa only [rearranged_square T hT hfT hnT] using hiT
  rw [integral_toReal_mul (layer_measurable S hS) (layer_measurable T hT) hiS hiT,
    integral_toReal_mul hs ht his hit]
  exact ENNReal.toReal_mono (lintegral_mul_ne_top_of_squares hs ht his hit)
    (rearranged_inner_ge S T hS hT hfS hfT)

include hS hT hfS hfT hnS hnT hiS hiT in
lemma rearranged_real_difference :
    (∫ s, ((rearranged S μ ν s).toReal-(rearranged T μ ρ s).toReal)^2) ≤
      ∫ x, ((layer S ν x).toReal-(layer T ρ x).toReal)^2 ∂μ := by
  have hls := toReal_memLp (layer_measurable (ν := ν) S hS) hiS
  have hlt := toReal_memLp (layer_measurable (ν := ρ) T hT) hiT
  have hrs := rearranged_real_memLp S hS hfS hnS hiS
  have hrt := rearranged_real_memLp T hT hfT hnT hiT
  rw [integral_sub_sq hrs hrt, integral_sub_sq hls hlt, rearranged_real_square S hS hfS hnS hiS,
    rearranged_real_square T hT hfT hnT hiT]
  linarith [rearranged_real_inner S T hS hT hfS hfT hnS hnT hiS hiT]

end L2
end VerticalRearrangement

end

section

open MeasureTheory Set Filter
open scoped ENNReal
namespace VerticalRearrangement
section Fibers
variable {X : Type*} [MeasurableSpace X]

noncomputable def fiberStar (F : X × ℝ → ℝ) (p : X × ℝ) : ℝ≥0∞ :=
  rearranged (superlevel (fun s => F (p.1,s))) volume volume p.2

lemma fiberLength_measurable {F : X × ℝ → ℝ} (hF : Measurable F) :
    Measurable (fun p : X × ℝ => volume (superlevel (fun s => F (p.1,s)) p.2)) := by
  apply measure_family_measurable
  change MeasurableSet {p : ℝ × (X × ℝ) | 0 < p.2.2 ∧ p.2.2 < F (p.2.1,p.1)}
  exact (measurableSet_lt measurable_const measurable_snd.snd).inter
    (measurableSet_lt measurable_snd.snd (hF.comp (measurable_snd.fst.prodMk measurable_fst)))

lemma fiberStar_measurable {F : X × ℝ → ℝ} (hF : Measurable F) :
    Measurable (fiberStar F) := by
  unfold fiberStar rearranged layer
  apply Measurable.lintegral_prod_right
  apply measurable_const.indicator
  change MeasurableSet {p : (X × ℝ) × ℝ |
    |p.1.2| < (volume (superlevel (fun r => F (p.1.1,r)) p.2)).toReal / 2}
  exact measurableSet_lt measurable_fst.snd.abs
    (((fiberLength_measurable hF).comp (measurable_fst.fst.prodMk measurable_snd)).ennreal_toReal.div_const 2)

omit [MeasurableSpace X] in
lemma superlevel_measure_ne_top_of_strip {F : X × ℝ → ℝ} {ell : ℝ}
    (hstrip : ∀ p, ell ≤ |p.2| → F p = 0) (x : X) (u : ℝ) :
    volume (superlevel (fun s => F (x,s)) u) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (measure_Ioo_lt_top (μ := (volume : Measure ℝ)) (a := -ell) (b := ell)).ne
  apply measure_mono
  intro s hs
  change 0 < u ∧ u < F (x,s) at hs
  have h : |s| < ell := by
    by_contra hn
    rw [hstrip (x,s) (not_lt.mp hn)] at hs
    linarith [hs.1,hs.2]
  exact abs_lt.mp h

lemma fiberStar_square {F : X × ℝ → ℝ} (hF : Measurable F)
    (hfinite : ∀ x u, volume (superlevel (fun s => F (x,s)) u) ≠ ⊤) (x : X) :
    (∫⁻ s, (fiberStar F (x,s))^2) = ∫⁻ s, (ENNReal.ofReal (F (x,s)))^2 := by
  change (∫⁻ s, (rearranged (superlevel (fun r => F (x,r))) volume volume s)^2) = _
  have hx : Measurable (fun s => F (x,s)) := hF.comp measurable_prodMk_left
  rw [rearranged_square _ (superlevel_measurable hx)
    (hfinite x) (superlevel_nested _)]
  simp only [layer_superlevel]

variable {μ : Measure X}
lemma fiberStar_total_square {F : X × ℝ → ℝ} (hF : Measurable F)
    (hfinite : ∀ x u, volume (superlevel (fun s => F (x,s)) u) ≠ ⊤) :
    (∫⁻ p, (fiberStar F p)^2 ∂μ.prod volume) =
      ∫⁻ p, (ENNReal.ofReal (F p))^2 ∂μ.prod volume := by
  rw [lintegral_prod _ ((fiberStar_measurable hF).pow_const 2).aemeasurable,
    lintegral_prod _ (hF.ennreal_ofReal.pow_const 2).aemeasurable]
  apply lintegral_congr
  exact fiberStar_square hF hfinite

lemma fiberStar_toReal_memLp {F : X × ℝ → ℝ} (hF : Measurable F)
    (hfinite : ∀ x u, volume (superlevel (fun s => F (x,s)) u) ≠ ⊤)
    (hi : ∫⁻ p, (ENNReal.ofReal (F p))^2 ∂μ.prod volume ≠ ⊤) :
    MemLp (fun p => (fiberStar F p).toReal) 2 (μ.prod volume) := by
  apply toReal_memLp (fiberStar_measurable hF)
  rwa [fiberStar_total_square hF hfinite]

lemma fiberStar_total_real_square {F : X × ℝ → ℝ} (hF : Measurable F)
    (hFn : ∀ p, 0 ≤ F p)
    (hfinite : ∀ x u, volume (superlevel (fun s => F (x,s)) u) ≠ ⊤)
    (hi : ∫⁻ p, (ENNReal.ofReal (F p))^2 ∂μ.prod volume ≠ ⊤) :
    (∫ p, (fiberStar F p).toReal^2 ∂μ.prod volume) = ∫ p, F p^2 ∂μ.prod volume := by
  rw [integral_toReal_square (fiberStar_measurable hF)
      (by rwa [fiberStar_total_square hF hfinite]), fiberStar_total_square hF hfinite]
  simpa only [ENNReal.toReal_ofReal (hFn _)] using
    (integral_toReal_square hF.ennreal_ofReal hi).symm

omit [MeasurableSpace X] in
lemma fiberStar_eq_zero_of_measure_le {F : X × ℝ → ℝ} (x : X) (s : ℝ)
    (h : ∀ u, volume (superlevel (fun r => F (x,r)) u) ≤ ENNReal.ofReal (2*|s|)) :
    fiberStar F (x,s) = 0 := by
  unfold fiberStar rearranged layer
  have hz (u : ℝ) : (centered (volume (superlevel (fun r => F (x,r)) u))).indicator
      (fun _ => (1:ℝ≥0∞)) s = 0 := by
    apply indicator_of_notMem
    change ¬ |s| < (volume (superlevel (fun r => F (x,r)) u)).toReal/2
    have hh := ENNReal.toReal_le_of_le_ofReal (by positivity : 0 ≤ 2*|s|) (h u)
    linarith
  simp only [hz,lintegral_zero]

lemma ofReal_square_integral_ne_top {F : X → ℝ} (hF : MemLp F 2 μ) (hFn : ∀ x,0 ≤ F x) :
    ∫⁻ x, (ENNReal.ofReal (F x))^2 ∂μ ≠ ⊤ := by
  have hh := ((memLp_two_iff_integrable_sq hF.aestronglyMeasurable).mp hF).lintegral_lt_top.ne
  simpa only [ENNReal.ofReal_pow (hFn _)] using hh

lemma fiberStar_difference {F G : X × ℝ → ℝ} (hF : Measurable F) (hG : Measurable G)
    (hFn : ∀ p,0 ≤ F p) (hGn : ∀ p,0 ≤ G p)
    (hfF : ∀ x u,volume (superlevel (fun s => F (x,s)) u) ≠ ⊤)
    (hfG : ∀ x u,volume (superlevel (fun s => G (x,s)) u) ≠ ⊤)
    (x : X) (hiF : MemLp (fun s => F (x,s)) 2 volume)
    (hiG : MemLp (fun s => G (x,s)) 2 volume) :
    (∫ s, ((fiberStar F (x,s)).toReal-(fiberStar G (x,s)).toReal)^2) ≤
      ∫ s, (F (x,s)-G (x,s))^2 := by
  have hmF := superlevel_measurable (f := fun r => F (x,r)) (hF.comp measurable_prodMk_left)
  have hmG := superlevel_measurable (f := fun r => G (x,r)) (hG.comp measurable_prodMk_left)
  have hF' : ∫⁻ s, (layer (superlevel (fun r => F (x,r))) volume s)^2 ≠ ⊤ := by
    simpa only [layer_superlevel] using ofReal_square_integral_ne_top hiF (fun s => hFn (x,s))
  have hG' : ∫⁻ s, (layer (superlevel (fun r => G (x,r))) volume s)^2 ≠ ⊤ := by
    simpa only [layer_superlevel] using ofReal_square_integral_ne_top hiG (fun s => hGn (x,s))
  simpa only [fiberStar,layer_superlevel,ENNReal.toReal_ofReal (hFn _),
    ENNReal.toReal_ofReal (hGn _)] using
    rearranged_real_difference _ _ hmF hmG (hfF x) (hfG x)
      (superlevel_nested _) (superlevel_nested _) hF' hG'

lemma fiberStar_memLp {F : X × ℝ → ℝ} (hF : Measurable F) (hFn : ∀ p,0 ≤ F p)
    (hfF : ∀ x u,volume (superlevel (fun s => F (x,s)) u) ≠ ⊤)
    (hiF : MemLp F 2 (μ.prod volume)) :
    MemLp (fun p => (fiberStar F p).toReal) 2 (μ.prod volume) :=
  fiberStar_toReal_memLp hF hfF (ofReal_square_integral_ne_top hiF hFn)

lemma fiberStar_total_difference [SFinite μ] {F G : X × ℝ → ℝ}
    (hF : Measurable F) (hG : Measurable G) (hFn : ∀ p,0 ≤ F p) (hGn : ∀ p,0 ≤ G p)
    (hfF : ∀ x u,volume (superlevel (fun s => F (x,s)) u) ≠ ⊤)
    (hfG : ∀ x u,volume (superlevel (fun s => G (x,s)) u) ≠ ⊤)
    (hiF : MemLp F 2 (μ.prod volume)) (hiG : MemLp G 2 (μ.prod volume)) :
    (∫ p, ((fiberStar F p).toReal-(fiberStar G p).toReal)^2 ∂μ.prod volume) ≤
      ∫ p, (F p-G p)^2 ∂μ.prod volume := by
  have hF2 := (memLp_two_iff_integrable_sq hiF.aestronglyMeasurable).mp hiF
  have hG2 := (memLp_two_iff_integrable_sq hiG.aestronglyMeasurable).mp hiG
  have hS := (fiberStar_memLp hF hFn hfF hiF).sub (fiberStar_memLp hG hGn hfG hiG)
  have hD := hiF.sub hiG
  have hS2 := (memLp_two_iff_integrable_sq hS.aestronglyMeasurable).mp hS
  have hD2 := (memLp_two_iff_integrable_sq hD.aestronglyMeasurable).mp hD
  simp only [Pi.sub_apply] at hS2 hD2
  rw [integral_prod _ hS2,integral_prod _ hD2]
  apply integral_mono_ae hS2.integral_prod_left hD2.integral_prod_left
  filter_upwards [hF2.prod_right_ae,hG2.prod_right_ae] with x hx hy
  exact fiberStar_difference hF hG hFn hGn hfF hfG x
    ((memLp_two_iff_integrable_sq (hF.comp measurable_prodMk_left).aestronglyMeasurable).mpr hx)
    ((memLp_two_iff_integrable_sq (hG.comp measurable_prodMk_left).aestronglyMeasurable).mpr hy)

end Fibers
end VerticalRearrangement

end

section

open Set MeasureTheory
open scoped ENNReal
namespace ShiftedSections
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma line_interval_mem {K : Set E} (hK : Convex ℝ K) {y e : E} {r t z : ℝ}
    (hr : y+r • e ∈ K) (ht : y+t • e ∈ K) (hz : z ∈ Icc r t) : y+z • e ∈ K := by
  have hc : Convex ℝ {a : ℝ | y+a • e ∈ K} := by
    intro a ha b hb u v hu hv huv
    change y+(u*a+v*b) • e ∈ K
    have hvu : v=1-u := by linarith
    subst v
    convert hK ha hb hu hv huv using 1; module
  exact hc.ordConnected.out hr ht hz

lemma section_mono {K : Set E} (hK : Convex ℝ K) (e : E) (ell : ℝ)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    sectionDomain K e ell t ⊆ sectionDomain K e ell s := by
  rintro y ⟨c,hc,hl,hr⟩
  refine ⟨c,lt_of_le_of_lt (add_le_add_right hst _) hc,
    line_interval_mem hK hl hr ⟨?_,?_⟩,line_interval_mem hK hl hr ⟨?_,?_⟩⟩ <;> linarith

lemma section_of_fiber_pair {K : Set E} (hK : Convex ℝ K) {y e : E} {ell r t s : ℝ}
    (hr : |r| < ell) (ht : |t| < ell) (hry : y+r • e ∈ K) (hty : y+t • e ∈ K)
    (hs : 0 ≤ s) (hst : 2*s < t-r) : y ∈ sectionDomain K e ell s := by
  refine ⟨(r+t)/2,?_,line_interval_mem hK hry hty ⟨?_,?_⟩,
    line_interval_mem hK hry hty ⟨?_,?_⟩⟩
  · rw [← lt_sub_iff_add_lt,abs_lt]
    constructor
    · linarith [(abs_lt.mp hr).1]
    · linarith [(abs_lt.mp ht).2]
  all_goals linarith

lemma fiber_measure_le_of_not_section {K : Set E} (hK : Convex ℝ K)
    {y e : E} {ell s : ℝ} (hs : 0 ≤ s) (hy : y ∉ sectionDomain K e ell s) :
    volume {r : ℝ | |r| < ell ∧ y+r • e ∈ K} ≤ ENNReal.ofReal (2*s) := by
  apply (Real.volume_le_diam _).trans
  apply Metric.ediam_le_of_forall_dist_le
  intro r hr t ht
  rw [Real.dist_eq]
  by_contra! hh
  rcases lt_or_ge r t with hrt | htr
  · rw [abs_of_nonpos (sub_nonpos.mpr hrt.le)] at hh
    exact hy (section_of_fiber_pair hK hr.1 ht.1 hr.2 ht.2 hs (by linarith))
  · rw [abs_of_nonneg (sub_nonneg.mpr htr)] at hh
    exact hy (section_of_fiber_pair hK ht.1 hr.1 ht.2 hr.2 hs hh)

lemma section_bounded {K : Set E} (hK : Bornology.IsBounded K) (e : E) {ell s : ℝ}
    (hs : 0 ≤ s) : Bornology.IsBounded (sectionDomain K e ell s) := by
  obtain ⟨R,hR⟩ := hK.subset_closedBall (0:E)
  apply Metric.isBounded_iff_subset_closedBall (0:E) |>.mpr
  refine ⟨R+|ell| * ‖e‖,?_⟩
  rintro y ⟨c,hc,hl,hr⟩
  have hcs : |c-s| < ell := by
    have hh := abs_sub c s
    rw [abs_of_nonneg hs] at hh
    exact hh.trans_lt hc
  have he : ‖(c-s) • e‖ ≤ |ell| * ‖e‖ := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hcs.le.trans (le_abs_self ell)) (norm_nonneg e)
  have hm : ‖y+(c-s) • e‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hR hl
  rw [Metric.mem_closedBall,dist_zero_right]
  calc
    ‖y‖ = ‖(y+(c-s) • e)-(c-s) • e‖ := by rw [add_sub_cancel_right]
    _ ≤ ‖y+(c-s) • e‖+‖(c-s) • e‖ := norm_sub_le _ _
    _ ≤ R+|ell| * ‖e‖ := add_le_add hm he

lemma fiberStar_supported {K : Set E} (hK : Convex ℝ K) {e : E} {ell : ℝ}
    [MeasurableSpace E] {F : E × ℝ → ℝ}
    (hF : ∀ p, p.1+p.2 • e ∉ K ∨ ell ≤ |p.2| → F p = 0)
    {y : E} {s : ℝ} (hy : y ∉ sectionDomain K e ell |s|) :
    VerticalRearrangement.fiberStar F (y,s) = 0 := by
  apply VerticalRearrangement.fiberStar_eq_zero_of_measure_le
  intro u
  apply le_trans (measure_mono ?_) (fiber_measure_le_of_not_section hK (abs_nonneg s) hy)
  intro r hr
  change 0 < u ∧ u < F (y,r) at hr
  have hnot : ¬ (y+r • e ∉ K ∨ ell ≤ |r|) := by
    intro hn
    rw [hF (y,r) hn] at hr
    linarith [hr.1,hr.2]
  push Not at hnot
  exact ⟨hnot.2,hnot.1⟩

end ShiftedSections

end

section

open Set
namespace EuclideanSteinitz

lemma convex_supporting_line {J : Set ℝ} {h : ℝ → ℝ} (hc : ConvexOn ℝ J h)
    (hm : MonotoneOn h J) (h0 : 0 ∈ J) (h1 : 1 ∈ J)
    (hr : ∃ r ∈ J,1 < r) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ x ∈ J, h 1+a*(x-1) ≤ h x := by
  obtain ⟨r,hrJ,hr1⟩ := hr
  let L : Set ℝ := {a | ∃ x ∈ J,x<1 ∧ a=slope h x 1}
  have hL0 : slope h 0 1 ∈ L := ⟨0,h0,by norm_num,rfl⟩
  have hLne : L.Nonempty := ⟨_,hL0⟩
  have hLb : BddAbove L := by
    refine ⟨slope h 1 r,?_⟩
    rintro a ⟨x,hx,hx1,rfl⟩
    simpa only [slope_def_field] using hc.slope_mono_adjacent hx hrJ hx1 hr1
  refine ⟨sSup L,?_,?_⟩
  · have hh := le_csSup hLb hL0
    have hm01 := hm h0 h1 (by norm_num : (0:ℝ)≤1)
    simp only [slope_def_field,sub_zero,div_one] at hh
    linarith
  · intro x hx
    rcases lt_trichotomy x 1 with hx1 | rfl | h1x
    · have hh := le_csSup hLb (show slope h x 1 ∈ L from ⟨x,hx,hx1,rfl⟩)
      rw [slope_def_field,div_le_iff₀ (by linarith : 0 < 1-x)] at hh
      nlinarith
    · simp
    · have hh : sSup L ≤ slope h 1 x := by
        apply csSup_le hLne
        rintro a ⟨y,hy,hy1,rfl⟩
        simpa only [slope_def_field] using hc.slope_mono_adjacent hy hx hy1 h1x
      rw [slope_def_field,le_div_iff₀ (by linarith : 0 < x-1)] at hh
      linarith

end EuclideanSteinitz

end

section

open MeasureTheory Set
open scoped ENNReal NNReal
namespace ShiftedSections
variable {ι : Type*} [Fintype ι]

noncomputable def sectionNorm (K : Set (EuclideanSpace ℝ ι)) (hK : IsOpen K)
    (e : EuclideanSpace ℝ ι) (ell s : ℝ) (v : ι → ℝ≥0) : ℝ :=
  ‖HeatL2.compressedHeat (sectionDomain K e ell s) (section_open hK e ell s).measurableSet
    (GaussianKernel.symbol v) (GaussianKernel.symbol_continuous v).aestronglyMeasurable
    (GaussianKernel.symbol_nonneg v)‖

noncomputable def sectionRate (K : Set (EuclideanSpace ℝ ι)) (hK : IsOpen K)
    (e : EuclideanSpace ℝ ι) (ell : ℝ) (v : ι → ℝ≥0) (s : ℝ) : ℝ :=
  -Real.log (sectionNorm K hK e ell s v)

def activeHeights (K : Set (EuclideanSpace ℝ ι)) (e : EuclideanSpace ℝ ι) (ell : ℝ) : Set ℝ :=
  {s | 0 ≤ s ∧ (sectionDomain K e ell s).Nonempty}

lemma activeHeights_convex {K : Set (EuclideanSpace ℝ ι)} (hK : Convex ℝ K)
    (e : EuclideanSpace ℝ ι) (ell : ℝ) : Convex ℝ (activeHeights K e ell) := by
  rintro s ⟨hs,ys,hys⟩ t ⟨ht,yt,hyt⟩ a b ha hb hab
  exact ⟨add_nonneg (mul_nonneg ha hs) (mul_nonneg hb ht),
    ⟨a • ys+b • yt,section_mix hK e ell hys hyt ha hb hab⟩⟩

lemma sectionNorm_pos {K : Set (EuclideanSpace ℝ ι)} (hKo : IsOpen K)
    (hKb : Bornology.IsBounded K) (e : EuclideanSpace ℝ ι) (ell : ℝ) (v : ι → ℝ≥0)
    {s : ℝ} (hs : s ∈ activeHeights K e ell) : 0 < sectionNorm K hKo e ell s v := by
  let D := sectionDomain K e ell s
  have hDb := section_bounded hKb e (ell := ell) hs.1
  let : IsFiniteMeasure (volume.restrict D) := isFiniteMeasure_restrict.mpr hDb.measure_lt_top.ne
  apply HeatL2.compressed_norm_pos D (section_open hKo e ell s).measurableSet
  exact (section_open hKo e ell s).measure_pos volume hs.2

lemma sectionNorm_le_one {K : Set (EuclideanSpace ℝ ι)} (hKo : IsOpen K)
    (e : EuclideanSpace ℝ ι) (ell s : ℝ) (v : ι → ℝ≥0) : sectionNorm K hKo e ell s v ≤ 1 :=
  HeatL2.compressedHeat_norm_le_one _ _ _ _ _

lemma sectionRate_nonneg {K : Set (EuclideanSpace ℝ ι)} (hKo : IsOpen K)
    (hKb : Bornology.IsBounded K) (e : EuclideanSpace ℝ ι) (ell : ℝ) (v : ι → ℝ≥0)
    {s : ℝ} (hs : s ∈ activeHeights K e ell) : 0 ≤ sectionRate K hKo e ell v s := by
  exact neg_nonneg.mpr (Real.log_nonpos (sectionNorm_pos hKo hKb e ell v hs).le
    (sectionNorm_le_one hKo e ell s v))

lemma sectionRate_monotone {K : Set (EuclideanSpace ℝ ι)} (hKo : IsOpen K)
    (hKb : Bornology.IsBounded K) (hKc : Convex ℝ K) (e : EuclideanSpace ℝ ι)
    (ell : ℝ) (v : ι → ℝ≥0) : MonotoneOn (sectionRate K hKo e ell v) (activeHeights K e ell) := by
  intro s hs t ht hst
  apply neg_le_neg
  apply Real.log_le_log (sectionNorm_pos hKo hKb e ell v ht)
  exact HeatL2.compressed_norm_mono_domain _ _ _ _ (section_mono hKc e ell hs.1 hst) _ _ _

lemma sectionRate_convex {K : Set (EuclideanSpace ℝ ι)} (hKo : IsOpen K)
    (hKb : Bornology.IsBounded K) (hKc : Convex ℝ K) (e : EuclideanSpace ℝ ι)
    (ell : ℝ) (v : ι → ℝ≥0) (hv : ∀ i,v i ≠ 0) :
    ConvexOn ℝ (activeHeights K e ell) (sectionRate K hKo e ell v) := by
  refine ⟨activeHeights_convex hKc e ell,?_⟩
  intro s hs r hr a b ha hb hab
  have hbe : a=1-b := by linarith
  have hb1 : b ∈ Icc (0:ℝ) 1 := ⟨hb,by linarith⟩
  have hsr := activeHeights_convex hKc e ell hs hr ha hb hab
  have hh := GaussianKernel.compressed_norm_logconcave v hv
    (section_open hKo e ell s) (section_open hKo e ell r)
    (section_open hKo e ell (a*s+b*r))
    (section_bounded hKb e hs.1) (section_bounded hKb e hr.1)
    (section_bounded hKb e hsr.1) (section_convex hKc e ell s)
    (section_convex hKc e ell r) (section_convex hKc e ell (a*s+b*r))
    hs.2 hr.2 hb1 (fun y hy z hz => by
      rw [← hbe]
      exact section_mix hKc e ell hy hz ha hb hab)
  change sectionNorm K hKo e ell s v^(1-b)*sectionNorm K hKo e ell r v^b ≤
    sectionNorm K hKo e ell (a*s+b*r) v at hh
  rw [← hbe] at hh
  have hsp := sectionNorm_pos hKo hKb e ell v hs
  have hrp := sectionNorm_pos hKo hKb e ell v hr
  have hlog := Real.log_le_log (mul_pos (Real.rpow_pos_of_pos hsp _) (Real.rpow_pos_of_pos hrp _)) hh
  rw [Real.log_mul (Real.rpow_pos_of_pos hsp a).ne' (Real.rpow_pos_of_pos hrp b).ne',
    Real.log_rpow hsp,Real.log_rpow hrp] at hlog
  change -Real.log (sectionNorm K hKo e ell (a*s+b*r) v) ≤
    a*(-Real.log (sectionNorm K hKo e ell s v))+b*(-Real.log (sectionNorm K hKo e ell r v))
  linarith

end ShiftedSections

end

end OAI

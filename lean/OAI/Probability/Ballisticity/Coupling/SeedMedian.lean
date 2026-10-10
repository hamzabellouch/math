import Mathlib
import OAI.Probability.Ballisticity.Estimates.BudgetNormalize

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def IsIntegerMedian (μ : Measure ℤ) (b : ℤ) : Prop :=
  (1/2:ℝ≥0∞) ≤ μ (Set.Iic b) ∧ (1/2:ℝ≥0∞) ≤ μ (Set.Ici b)

lemma exists_nat_integerMedian (μ : ProbabilityMeasure ℤ) :
    ∃ n : ℕ, IsIntegerMedian μ.toMeasure (Encodable.decode (α:=ℤ) n |>.getD 0) := by
  obtain ⟨b,hb⟩ := exists_integer_median μ.toMeasure
  refine ⟨Encodable.encode b, ?_⟩
  rw [Encodable.encodek]
  exact hb

noncomputable def selectedIntegerMedian (μ : ProbabilityMeasure ℤ) : ℤ :=
  (Encodable.decode (α:=ℤ) (Nat.find (exists_nat_integerMedian μ))).getD 0

lemma selectedIntegerMedian_spec (μ : ProbabilityMeasure ℤ) :
    IsIntegerMedian μ.toMeasure (selectedIntegerMedian μ) :=
  Nat.find_spec (exists_nat_integerMedian μ)

lemma measurable_selectedIntegerMedian : Measurable selectedIntegerMedian := by
  apply (measurable_of_countable (fun n => (Encodable.decode (α:=ℤ) n).getD 0)).comp
  apply measurable_find exists_nat_integerMedian
  intro n
  exact (measurableSet_le measurable_const
    ((Measure.measurable_coe (Set.to_countable _).measurableSet).comp measurable_subtype_coe)).inter
    (measurableSet_le measurable_const
      ((Measure.measurable_coe (Set.to_countable _).measurableSet).comp measurable_subtype_coe))

noncomputable def orientedIntegerLaw {d : ℕ} (f : Direction d) (s : ℤ)
    (μ : ProbabilityMeasure (Lattice d)) : ProbabilityMeasure ℤ :=
  ⟨μ.toMeasure.map (fun x => s*signedHeight f x),
    (Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable).mpr
      inferInstance⟩

lemma measurable_orientedIntegerLaw {d : ℕ} (f : Direction d) (s : ℤ) :
    Measurable (orientedIntegerLaw f s) := by
  exact ((Measure.measurable_map _ (measurable_of_countable _)).comp measurable_subtype_coe).subtype_mk

noncomputable def seedMedian {d : ℕ} (f : Direction d) (s : ℤ)
    (μ : ProbabilityMeasure (Lattice d)) : ℤ := selectedIntegerMedian (orientedIntegerLaw f s μ)

lemma measurable_seedMedian {d : ℕ} (f : Direction d) (s : ℤ) : Measurable (seedMedian f s) :=
  measurable_selectedIntegerMedian.comp (measurable_orientedIntegerLaw f s)

noncomputable def seedHalfRaw {d : ℕ} (f : Direction d) (s : ℤ) (upper : Bool)
    (μ : ProbabilityMeasure (Lattice d)) : Measure (Lattice d) :=
  μ.toMeasure.restrict {x | if upper then seedMedian f s μ ≤ s*signedHeight f x
    else s*signedHeight f x ≤ seedMedian f s μ}

lemma seedHalfRaw_mass {d : ℕ} (f : Direction d) (s : ℤ) (upper : Bool)
    (μ : ProbabilityMeasure (Lattice d)) :
    (1/2:ℝ≥0∞) ≤ seedHalfRaw f s upper μ Set.univ := by
  have h := selectedIntegerMedian_spec (orientedIntegerLaw f s μ)
  change (1/2:ℝ≥0∞) ≤ μ.toMeasure.map (fun x => s*signedHeight f x)
    (Set.Iic (seedMedian f s μ)) ∧ (1/2:ℝ≥0∞) ≤ μ.toMeasure.map (fun x => s*signedHeight f x)
    (Set.Ici (seedMedian f s μ)) at h
  rw [Measure.map_apply (measurable_of_countable _) measurableSet_Iic,
    Measure.map_apply (measurable_of_countable _) measurableSet_Ici] at h
  cases upper
  · simpa [seedHalfRaw,Set.preimage,Set.Iic] using h.1
  · simpa [seedHalfRaw,Set.preimage,Set.Ici] using h.2

lemma measurable_seedHalfRaw {d : ℕ} (f : Direction d) (s : ℤ) (upper : Bool) :
    Measurable (seedHalfRaw f s upper) := by
  apply Measure.measurable_of_measurable_coe
  intro U hU
  have hfun : Measurable (fun p : ProbabilityMeasure (Lattice d) × ℤ =>
      p.1.toMeasure (U ∩ {x | if upper then p.2 ≤ s*signedHeight f x else s*signedHeight f x ≤ p.2})) := by
    apply measurable_from_prod_countable_left
    intro j
    exact (Measure.measurable_coe (Set.to_countable
      (U ∩ {x : Lattice d | if upper then j ≤ s*signedHeight f x else s*signedHeight f x ≤ j})).measurableSet).comp measurable_subtype_coe
  simpa only [seedHalfRaw,Measure.restrict_apply hU,Function.comp_def,id_eq] using
    hfun.comp (measurable_id.prodMk (measurable_seedMedian f s))

instance seedHalfRaw_finite {d : ℕ} (f : Direction d) (s : ℤ) (upper : Bool)
    (μ : ProbabilityMeasure (Lattice d)) : IsFiniteMeasure (seedHalfRaw f s upper μ) := by
  unfold seedHalfRaw; infer_instance

noncomputable def seedHalf {d : ℕ} (f : Direction d) (s : ℤ) (upper : Bool)
    (μ : ProbabilityMeasure (Lattice d)) : ProbabilityMeasure (Lattice d) :=
  ⟨normalizeOr (seedHalfRaw f s upper μ) μ.toMeasure,normalizeOr_probability _ _⟩

lemma measurable_seedHalf {d : ℕ} (f : Direction d) (s : ℤ) (upper : Bool) :
    Measurable (seedHalf f s upper) :=
  (measurable_normalizeOr _ _ (measurable_seedHalfRaw f s upper) measurable_subtype_coe).subtype_mk

lemma seedHalf_domination {d : ℕ} (f : Direction d) (s : ℤ) (upper : Bool)
    (μ : ProbabilityMeasure (Lattice d)) :
    (1/2:ℝ≥0∞) • (seedHalf f s upper μ).toMeasure ≤ μ.toMeasure := by
  have hm := normalizeOr_mass (seedHalfRaw f s upper μ) μ.toMeasure
  calc
    _ ≤ seedHalfRaw f s upper μ Set.univ • (seedHalf f s upper μ).toMeasure :=
      by
        apply Measure.le_iff.mpr
        intro U _
        simp only [Measure.smul_apply,smul_eq_mul]
        exact mul_le_mul_left (seedHalfRaw_mass f s upper μ) _
    _ = seedHalfRaw f s upper μ := hm
    _ ≤ μ.toMeasure := Measure.restrict_le_self

lemma seedHalf_ae {d : ℕ} (f : Direction d) (s : ℤ) (upper : Bool)
    (μ : ProbabilityMeasure (Lattice d)) :
    ∀ᵐ x ∂(seedHalf f s upper μ).toMeasure,
      if upper then seedMedian f s μ ≤ s*signedHeight f x
      else s*signedHeight f x ≤ seedMedian f s μ := by
  have hm : seedHalfRaw f s upper μ Set.univ ≠ 0 := ne_of_gt
    ((by norm_num : (0:ℝ≥0∞)<1/2).trans_le (seedHalfRaw_mass f s upper μ))
  change ∀ᵐ x ∂normalizeOr (seedHalfRaw f s upper μ) μ.toMeasure, _
  rw [normalizeOr,ite_eq_right hm,normalizedMeasure]
  apply Measure.ae_smul_measure
  exact ae_restrict_mem (Set.to_countable _).measurableSet

lemma seedHalf_inherits {d : ℕ} (f : Direction d) (s : ℤ) (upper : Bool)
    (μ : ProbabilityMeasure (Lattice d)) (P : Lattice d → Prop) (hP : ∀ᵐ x ∂μ.toMeasure, P x) :
    ∀ᵐ x ∂(seedHalf f s upper μ).toMeasure, P x := by
  change ∀ᵐ x ∂normalizeOr _ _, _
  exact normalizeOr_ae _ _ _ (ae_restrict_of_ae hP) hP

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def seedEndpointRaw {d : ℕ} (e : Direction d) (H : ℕ)
    (R : Lattice d → Lattice d → Prop) (μ : Measure (Lattice d)) (ω : Environment d) : Measure (Lattice d) :=
  μ.bind (fun x => (variableHitKernel (realPosition (step e)) H (ω,x)).restrict {y | R x y})

lemma seedEndpointRaw_apply {d : ℕ} (e : Direction d) (H : ℕ)
    (R : Lattice d → Lattice d → Prop) (μ : Measure (Lattice d)) (ω : Environment d)
    (U : Set (Lattice d)) : seedEndpointRaw e H R μ ω U =
      ∫⁻ x, variableHitKernel (realPosition (step e)) H (ω,x) (U ∩ {y | R x y}) ∂μ := by
  rw [seedEndpointRaw,Measure.bind_apply (Set.to_countable _).measurableSet (measurable_of_countable _).aemeasurable]
  simp_rw [Measure.restrict_apply (Set.to_countable _).measurableSet]

lemma seedEndpointRaw_le {d : ℕ} (e : Direction d) (H : ℕ)
    (R : Lattice d → Lattice d → Prop) (μ : Measure (Lattice d)) (ω : Environment d) :
    seedEndpointRaw e H R μ ω ≤ seedEndpointRaw e H (fun _ _ => True) μ ω := by
  intro U
  simp only [seedEndpointRaw_apply,Set.ofPred_true,Set.inter_univ]
  exact lintegral_mono fun _ => measure_mono Set.inter_subset_left

lemma seedEndpointRaw_univ_le {d : ℕ} (e : Direction d) (H : ℕ)
    (R : Lattice d → Lattice d → Prop) (μ : Measure (Lattice d)) (ω : Environment d) :
    seedEndpointRaw e H R μ ω Set.univ ≤ μ Set.univ := by
  rw [seedEndpointRaw_apply]
  calc
    _ ≤ ∫⁻ _, (1:ℝ≥0∞) ∂μ := by
      apply lintegral_mono
      intro x
      exact (measure_mono (Set.subset_univ _)).trans
        (hitKernel_total_le_one (disjoint_strip_upper (realPosition (step e)) x H) (ω,x))
    _ = _ := by simp

instance seedEndpointRaw_finite {d : ℕ} (e : Direction d) (H : ℕ)
    (R : Lattice d → Lattice d → Prop) (μ : Measure (Lattice d)) [IsFiniteMeasure μ]
    (ω : Environment d) : IsFiniteMeasure (seedEndpointRaw e H R μ ω) :=
  ⟨(seedEndpointRaw_univ_le e H R μ ω).trans_lt (measure_lt_top _ _)⟩

lemma seedEndpointRaw_mono {d : ℕ} (e : Direction d) (H : ℕ)
    (R : Lattice d → Lattice d → Prop) {μ ρ : Measure (Lattice d)} (h : μ ≤ ρ) (ω : Environment d) :
    seedEndpointRaw e H R μ ω ≤ seedEndpointRaw e H R ρ ω := by
  intro U
  simp only [seedEndpointRaw_apply]
  exact lintegral_mono' h le_rfl

lemma seedEndpointRaw_smul {d : ℕ} (e : Direction d) (H : ℕ)
    (R : Lattice d → Lattice d → Prop) (μ : Measure (Lattice d)) (ω : Environment d) (c : ℝ≥0∞) :
    seedEndpointRaw e H R (c • μ) ω = c • seedEndpointRaw e H R μ ω :=
  Measure.bind_smul _ _ (measurable_of_countable _).aemeasurable

lemma seedEndpointRaw_comp_le {d : ℕ} (e : Direction d) (h H : ℕ)
    (R S : Lattice d → Lattice d → Prop) (μ : Measure (Lattice d)) (ω : Environment d) :
    seedEndpointRaw e H S (seedEndpointRaw e h R μ ω) ω ≤
      seedEndpointRaw e (h+H) (fun _ _ => True) μ ω := by
  apply le_trans (seedEndpointRaw_le e H S _ ω)
  apply le_trans (seedEndpointRaw_mono e H _ (seedEndpointRaw_le e h R μ ω) ω)
  intro U
  simp only [seedEndpointRaw,Set.ofPred_true,Measure.restrict_univ]
  rw [Measure.bind_bind (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable]
  simp_rw [Measure.bind_apply (Set.to_countable U).measurableSet (measurable_of_countable _).aemeasurable]
  apply lintegral_mono
  intro x
  change (∫⁻ y, hitKernel (Strip (realPosition (step e)) y H)
    (Upper (realPosition (step e)) y H) (ω,y) U ∂hitKernel
      (Strip (realPosition (step e)) x h) (Upper (realPosition (step e)) x h) (ω,x)) ≤
        hitKernel (Strip (realPosition (step e)) x (h+H:ℕ))
          (Upper (realPosition (step e)) x (h+H:ℕ)) (ω,x) U
  simpa only [Nat.cast_add] using coordinate_raw_kernel_comp_le e h H ω x U

lemma seedEndpointRaw_ae {d : ℕ} (e : Direction d) (H : ℕ)
    (R : Lattice d → Lattice d → Prop) (μ : Measure (Lattice d)) (ω : Environment d)
    (P : Lattice d → Prop) (hP : ∀ᵐ x ∂μ, ∀ᵐ y ∂variableHitKernel (realPosition (step e)) H (ω,x), R x y → P y) :
    ∀ᵐ y ∂seedEndpointRaw e H R μ ω, P y := by
  rw [ae_iff,seedEndpointRaw_apply]
  apply (lintegral_eq_zero_iff (measurable_of_countable _)).mpr
  filter_upwards [hP] with x hx
  exact measure_eq_zero_iff_ae_notMem.mpr (hx.mono fun y hy h => h.1 (hy h.2))

lemma seedEndpointRaw_supported {d : ℕ} (e : Direction d) (H : ℕ)
    (R : Lattice d → Lattice d → Prop) (μ : Measure (Lattice d)) (ω : Environment d)
    (a : ℤ) (ha : ∀ᵐ x ∂μ, signedHeight e x=a) :
    ∀ᵐ y ∂seedEndpointRaw e H R μ ω, signedHeight e y=a+H := by
  apply seedEndpointRaw_ae
  filter_upwards [ha] with x hx
  filter_upwards [coordinate_hitKernel_supported e x H ω] with y hy _
  simpa only [hx] using hy

lemma measurable_seedEndpointRaw {d : ℕ} (e : Direction d) (H : ℕ)
    (R : Lattice d → Lattice d → Prop) :
    Measurable (fun p : Measure (Lattice d) × Environment d => seedEndpointRaw e H R p.1 p.2) := by
  apply Measure.measurable_of_measurable_coe
  intro U _
  simp only [seedEndpointRaw_apply,lintegral_countable']
  apply Measurable.tsum
  intro x
  exact (((Kernel.measurable_coe _ (Set.to_countable _).measurableSet).comp
    (measurable_id.prodMk measurable_const)).comp measurable_snd).mul
      ((Measure.measurable_coe (measurableSet_singleton x)).comp measurable_fst)

lemma seedEndpointRaw_joint_rows {d : ℕ} (e : Direction d) {H : ℕ} (hH : 0 < H)
    (R : Lattice d → Lattice d → Prop) (C S : Set (Lattice d))
    (hS : ∀ x ∈ C, Strip (realPosition (step e)) x H ⊆ S) :
    @Measurable ({μ : Measure (Lattice d) // ∀ᵐ x ∂μ, x ∈ C} × Environment d) (Measure (Lattice d))
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S)) _
      (fun p => seedEndpointRaw e H R p.1.val p.2) := by
  let : MeasurableSpace (Environment d) := rowSigma S
  apply Measure.measurable_of_measurable_coe
  intro U _
  simp only [seedEndpointRaw_apply,lintegral_countable']
  apply Measurable.tsum
  intro x
  by_cases hx : x ∈ C
  · have hm := (measurable_hitKernel_rows (Strip (realPosition (step e)) x H)
        (Upper (realPosition (step e)) x H) x
        (show x ∈ Strip (realPosition (step e)) x H from
          ⟨le_rfl,lt_add_of_pos_right _ (by exact_mod_cast hH)⟩)).mono (rowSigma_mono (hS x hx)) le_rfl
    exact (((Measure.measurable_coe (Set.to_countable _).measurableSet).comp hm).comp measurable_snd).mul
      ((Measure.measurable_coe (measurableSet_singleton x)).comp (measurable_subtype_coe.comp measurable_fst))
  · have hz (p : {μ : Measure (Lattice d) // ∀ᵐ x ∂μ, x ∈ C}) : p.val {x}=0 :=
      measure_mono_null (show {x} ⊆ Cᶜ from fun y hy => by simpa [Set.mem_singleton_iff.mp hy] using hx)
        (ae_iff.mp p.property)
    simp only [hz,mul_zero]
    exact measurable_const

lemma seedEndpointRaw_jump_total {d : ℕ} (e f : Direction d) (H : ℕ) (b a s : ℝ)
    (μ : Measure (Lattice d)) [IsFiniteMeasure μ] (ω : Environment d) :
    (seedEndpointRaw e H (fun x y => a < s*(signedCoordinate f (y-x)-b)) μ ω Set.univ).toReal =
      ∫ x, jumpPrefixMass (realPosition (step e)) f b a s H ω x ∂μ := by
  rw [seedEndpointRaw_apply]
  simp only [Set.univ_inter]
  have he (x : Lattice d) : variableHitKernel (realPosition (step e)) H (ω,x)
      {y | a < s*(signedCoordinate f (y-x)-b)} =
        quenchedKernel (ω,x) (EndpointPrefix (realPosition (step e)) x H
          {y | a < s*(signedCoordinate f (y-x)-b)}) :=
    hitKernel_apply_eq_hit (disjoint_strip_upper (realPosition (step e)) x H) _ (ω,x)
  simp only [he,jumpPrefixMass,Measure.real]
  exact (integral_toReal (measurable_of_countable _).aemeasurable
    (ae_of_all _ fun x => measure_lt_top _ _)).symm

lemma tube_le_seedCentral {d : ℕ} (e f : Direction d) (H : ℕ)
    (θ z : ℝ) (ω : Environment d) (x : Lattice d) :
    quenchedKernel (ω,x) (TubePrefix (realPosition (step e)) f x θ z H) ≤
      variableHitKernel (realPosition (step e)) H (ω,x)
        {y | |signedCoordinate f (y-x)-(H:ℝ)*θ| ≤ z} := by
  change quenchedKernel (ω,x) _ ≤
    hitKernel (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) (ω,x) _
  rw [hitKernel_apply_eq_hit (disjoint_strip_upper (realPosition (step e)) x H)]
  apply measure_mono_ae
  filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x)] with X h0 hnn hX
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hX
  refine Set.mem_iUnion.mpr ⟨n,⟨hn.1.1,?_⟩,hn.1.2⟩
  exact tubePrefixAt_top_deviation e f x θ z H n X h0 hnn hn

end DirectionalTransience

end

end OAI

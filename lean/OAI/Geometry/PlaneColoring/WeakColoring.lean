import OAI.Geometry.PlaneColoring.Coloring

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
abbrev PlaneL2 := Lp ℝ 2 (volume : Measure ℂ)
def shiftL2 (z : ℂ) (f : PlaneL2) : PlaneL2 :=
  Lp.compMeasurePreserving (fun x => x+z) (measurePreserving_add_right volume z) f
lemma shiftL2_ae (z : ℂ) (f : PlaneL2) : shiftL2 z f =ᵐ[volume] fun x => f (x+z) :=
  Lp.coeFn_compMeasurePreserving f _
lemma shiftL2_continuous (f : PlaneL2) : Continuous (fun z => shiftL2 z f) := by
  let g : C(ℂ,C(ℂ,ℂ)) := (ContinuousMap.mk (fun p : ℂ × ℂ => p.2+p.1) (by fun_prop)).curry
  exact continuous_const.compMeasurePreservingLp g.continuous (fun z => measurePreserving_add_right volume z) (by simp)
lemma correlation_continuous (f : PlaneL2) : Continuous (fun t : ℝ => ⟪f,shiftL2 (Circle.exp t : ℂ) f⟫) := by
  exact continuous_const.inner ((shiftL2_continuous f).comp (continuous_subtype_val.comp Circle.exp.continuous))
lemma product_zero_of_inner_zero (f g : PlaneL2) (hf : ∀ᵐ x ∂volume, 0 ≤ f x)
    (hg : ∀ᵐ x ∂volume, 0 ≤ g x) (h : ⟪f,g⟫ = 0) :
    ∀ᵐ x ∂volume, f x*g x=0 := by
  have hi : Integrable (fun x : ℂ => f x*g x) volume := by
    simpa [RCLike.inner_apply,mul_comm] using (L2.integrable_inner (𝕜 := ℝ) f g)
  have hn : ∀ᵐ x ∂volume, 0 ≤ f x*g x := by
    filter_upwards [hf,hg] with x hx hy
    exact mul_nonneg hx hy
  rw [L2.inner_def] at h
  apply (integral_eq_zero_iff_of_nonneg_ae hn hi).mp
  simpa [RCLike.inner_apply,mul_comm] using h
/-- AE exclusions over any full-support parameter measure upgrade to every parameter. -/
lemma all_parameters_product_zero {T : Type*} [TopologicalSpace T] [MeasurableSpace T]
    (μ : Measure T) [μ.IsOpenPosMeasure] (d : T → ℂ) (hd : Continuous d)
    (f : PlaneL2) (hf : ∀ᵐ x ∂volume, 0 ≤ f x)
    (ho : ∀ᵐ t ∂μ, ∀ᵐ x ∂(volume : Measure ℂ), f x*f (x+d t)=0) :
    ∀ t : T, ∀ᵐ x ∂(volume : Measure ℂ), f x*f (x+d t)=0 := by
  have hc : Continuous (fun t : T => ⟪f,shiftL2 (d t) f⟫) :=
    continuous_const.inner ((shiftL2_continuous f).comp hd)
  have hz : (fun t : T => ⟪f,shiftL2 (d t) f⟫) =ᵐ[μ] fun _ => 0 := by
    filter_upwards [ho] with t ht
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [shiftL2_ae (d t) f,ht] with x hx hh
    simpa [RCLike.inner_apply,mul_comm,hx] using hh
  have he := (hc.ae_eq_iff_eq μ continuous_const).mp hz
  intro t
  have hg : ∀ᵐ x ∂volume, 0 ≤ shiftL2 (d t) f x := by
    filter_upwards [shiftL2_ae (d t) f,
      (measurePreserving_add_right volume (d t)).quasiMeasurePreserving.ae hf] with x hx hh
    simpa only [hx] using hh
  have h0 := product_zero_of_inner_zero f (shiftL2 (d t) f) hf hg (congrFun he t)
  filter_upwards [h0,shiftL2_ae (d t) f] with x hx hh
  simpa only [hh] using hx
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
def truncatedClass (i : Fin k) (n : ℕ) : Set ℂ := {z | c z=i} ∩ Metric.closedBall 0 n
include hc
lemma truncatedClass_measurable (i : Fin k) (n : ℕ) : MeasurableSet (truncatedClass c i n) :=
  (measurableSet_eq_fun hc measurable_const).inter measurableSet_closedBall
omit hc in
lemma truncatedClass_finite (i : Fin k) (n : ℕ) : volume (truncatedClass c i n) ≠ ⊤ := by
  exact ne_top_of_le_ne_top ((isCompact_closedBall (0 : ℂ) (n : ℝ)).measure_ne_top)
    (measure_mono Set.inter_subset_right)
def truncatedVector (i : Fin k) (n : ℕ) : PlaneL2 :=
  (memLp_indicator_const 2 (truncatedClass_measurable c hc i n) (1 : ℝ) (Or.inr (truncatedClass_finite c i n))).toLp _
lemma truncatedVector_ae (i : Fin k) (n : ℕ) :
    truncatedVector c hc i n =ᵐ[volume] (truncatedClass c i n).indicator (fun _ => (1 : ℝ)) :=
  MemLp.coeFn_toLp _
lemma weak_all_directions (hweak : WeakColoring k c) :
    ∀ t : Angles, ∀ᵐ z ∂(volume : Measure ℂ), c z ≠ c (z+direction t) := by
  have ho : ∀ᵐ t ∂angularMeasure, ∀ᵐ z ∂(volume : Measure ℂ), c z ≠ c (z+direction t) := by
    apply (Measure.ae_ae_comm ?_).mp (Measure.ae_ae_of_ae_prod hweak.2)
    exact (measurableSet_eq_fun (hc.comp measurable_fst)
      (hc.comp (measurable_fst.add (direction_continuous.measurable.comp measurable_snd)))).compl
  have hz (i : Fin k) (n : ℕ) : ∀ t : Angles, ∀ᵐ z ∂(volume : Measure ℂ),
      truncatedVector c hc i n z*truncatedVector c hc i n (z+direction t)=0 := by
    apply all_parameters_product_zero angularMeasure direction direction_continuous
    · filter_upwards [truncatedVector_ae c hc i n] with z hz
      rw [hz]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    · filter_upwards [ho] with t ht
      filter_upwards [ht,truncatedVector_ae c hc i n,
        (measurePreserving_add_right volume (direction t)).quasiMeasurePreserving.ae (truncatedVector_ae c hc i n)] with z hne h1 h2
      rw [h1,h2]
      by_cases h : z ∈ truncatedClass c i n
      · have hh : z+direction t ∉ truncatedClass c i n := fun hh => hne (h.1.trans hh.1.symm)
        simp [Set.indicator_of_notMem hh]
      · simp [Set.indicator_of_notMem h]
  intro t
  have hi : ∀ᵐ z ∂(volume : Measure ℂ), ∀ i : Fin k, ∀ n : ℕ,
      ((truncatedClass c i n).indicator (fun _ => (1 : ℝ)) z)*
      ((truncatedClass c i n).indicator (fun _ => (1 : ℝ)) (z+direction t))=0 := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro n
    filter_upwards [hz i n t,truncatedVector_ae c hc i n,
      (measurePreserving_add_right volume (direction t)).quasiMeasurePreserving.ae (truncatedVector_ae c hc i n)] with z h0 h1 h2
    simpa only [h1,h2] using h0
  filter_upwards [hi] with z hz
  intro he
  obtain ⟨n,hn⟩ := exists_nat_gt (max ‖z‖ ‖z+direction t‖)
  have h1 : z ∈ truncatedClass c (c z) n := ⟨rfl,by
    simpa only [Metric.mem_closedBall,dist_zero_right] using (lt_of_le_of_lt (le_max_left _ _) hn).le⟩
  have h2 : z+direction t ∈ truncatedClass c (c z) n := ⟨he.symm,by
    simpa only [Metric.mem_closedBall,dist_zero_right] using (lt_of_le_of_lt (le_max_right _ _) hn).le⟩
  have h0 := hz (c z) n
  simp [Set.indicator_of_mem h1,Set.indicator_of_mem h2] at h0
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
def DensityOne (A : Set ℂ) (x : ℂ) : Prop :=
  Tendsto (fun r : ℝ => volume (A ∩ Metric.closedBall x r) / volume (Metric.closedBall x r))
    (𝓝[>] 0) (𝓝 (1 : ENNReal))
lemma densityOne_disjoint {A B : Set ℂ} (hB : MeasurableSet B)
    (hd : AEDisjoint volume A B) {x : ℂ} (hA : DensityOne A x) : ¬ DensityOne B x := by
  intro hb
  have hh := hA.add hb
  have hle : (1 : ENNReal)+1 ≤ 1 := le_of_tendsto hh (by
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [← ENNReal.add_div,← measure_union₀ (hB.inter measurableSet_closedBall).nullMeasurableSet
      (hd.mono inter_subset_left inter_subset_left)]
    apply (ENNReal.div_le_iff (Metric.measure_closedBall_pos volume x hr).ne'
      ((isCompact_closedBall x r).measure_ne_top)).mpr
    simpa only [one_mul] using measure_mono (union_subset inter_subset_right inter_subset_right))
  norm_num at hle
lemma densityOne_translate {A : Set ℂ} {x u : ℂ} :
    DensityOne ((fun z : ℂ => z+u) ⁻¹' A) x ↔ DensityOne A (x+u) := by
  have he (r : ℝ) : (fun z : ℂ => z+u) ⁻¹' (Metric.closedBall (x+u) r) = Metric.closedBall x r := by
    ext z
    simp only [Set.mem_preimage,Metric.mem_closedBall,dist_eq_norm,add_sub_add_right_eq_sub]
  have h1 (r : ℝ) : volume (((fun z : ℂ => z+u) ⁻¹' A) ∩ Metric.closedBall x r) =
      volume (A ∩ Metric.closedBall (x+u) r) := by
    rw [← he,← Set.preimage_inter,measure_preimage_add_right]
  have h2 (r : ℝ) : volume (Metric.closedBall x r) = volume (Metric.closedBall (x+u) r) := by
    rw [← he,measure_preimage_add_right]
  simp only [DensityOne,h1,h2]
lemma direction_exists {u : ℂ} (hu : ‖u‖=1) : ∃ t, direction t=u := by
  let v : Circle := ⟨u,mem_sphere_zero_iff_norm.mpr hu⟩
  obtain ⟨t,ht⟩ := Circle.exp_surjective v
  exact ⟨(t : Angles),by simpa only [direction_real] using congrArg Subtype.val ht⟩
lemma weak_density_proper {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) (hw : WeakColoring k c)
    (i : Fin k) {x y : ℂ} (hxy : ‖x-y‖=1) (hx : DensityOne {z | c z=i} x) :
    ¬ DensityOne {z | c z=i} y := by
  let u := y-x
  obtain ⟨t,ht⟩ := direction_exists (u := u) (by simpa only [u,norm_sub_rev] using hxy)
  have hd : AEDisjoint volume {z | c z=i} ((fun z : ℂ => z+u) ⁻¹' {z | c z=i}) := by
    apply (measure_eq_zero_iff_ae_notMem).mpr
    filter_upwards [weak_all_directions c hc hw t] with z hz
    rintro ⟨h1,h2⟩
    exact hz (by simpa only [ht] using h1.trans h2.symm)
  have hh := densityOne_disjoint ((measurableSet_eq_fun hc measurable_const).preimage
    (measurable_id.add_const u)) hd hx
  simp only [id_eq] at hh
  rw [densityOne_translate] at hh
  simpa only [u,add_sub_cancel] using hh
lemma ae_density_actual {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) :
    ∀ᵐ x ∂(volume : Measure ℂ), DensityOne {z | c z=c x} x := by
  have hh : ∀ᵐ x ∂(volume : Measure ℂ), ∀ i : Fin k,
      Tendsto (fun r : ℝ => volume ({z | c z=i} ∩ Metric.closedBall x r) / volume (Metric.closedBall x r))
        (𝓝[>] 0) (𝓝 (({z | c z=i} : Set ℂ).indicator (1 : ℂ → ENNReal) x)) :=
    ae_all_iff.mpr fun i => Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume
      (measurableSet_eq_fun hc measurable_const)
  filter_upwards [hh] with x hx
  simpa only [DensityOne,Set.indicator_of_mem (show x ∈ {z | c z=c x} from rfl),Pi.one_apply] using hx (c x)
end EuclideanFiveColor
end

end OAI

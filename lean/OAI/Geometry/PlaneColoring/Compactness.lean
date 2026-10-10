import OAI.Geometry.PlaneColoring.WeakColoring

namespace OAI

noncomputable section
open Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace.SeparableSpace E]
def weakHilbert (v : E) : WeakDual ℝ E := StrongDual.toWeakDual (InnerProductSpace.toDual ℝ E v)
omit [TopologicalSpace.SeparableSpace E] in
@[simp] lemma weakHilbert_apply (v w : E) : weakHilbert v w = ⟪v,w⟫ := rfl
lemma exists_finite_weak_subseq {ι : Type*} [Finite ι] (f : ℕ → ι → E) (C : ℝ)
    (hf : ∀ n i, ‖f n i‖ ≤ C) :
    ∃ b : ι → E, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ i, ‖b i‖ ≤ C) ∧ ∀ i v, Tendsto (fun n => ⟪f (φ n) i,v⟫) atTop (𝓝 ⟪b i,v⟫) := by
  let K : Set (WeakDual ℝ E) := WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 C
  have hK : IsCompact K := WeakDual.isCompact_closedBall 0 C
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : TopologicalSpace.MetrizableSpace K := WeakDual.metrizable_of_isCompact ℝ E K hK
  let u : ℕ → ι → K := fun n i => ⟨weakHilbert (f n i), by
    simpa only [K,Set.mem_preimage,Metric.mem_closedBall,dist_zero_right,weakHilbert,
      StrongDual.toStrongDual_toWeakDual,LinearIsometryEquiv.norm_map] using hf n i⟩
  obtain ⟨b,_,φ,hφ,hb⟩ := (isCompact_univ : IsCompact (Set.univ : Set (ι → K))).isSeqCompact.subseq_of_frequently_in
    (Filter.Eventually.frequently (Filter.Eventually.of_forall (fun n => Set.mem_univ (u n))))
  refine ⟨fun i => (InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual (b i).1),φ,hφ,?_,?_⟩
  · intro i
    simpa only [LinearIsometryEquiv.norm_map,K,Set.mem_preimage,Metric.mem_closedBall,dist_zero_right] using (b i).2
  · intro i v
    have ht := ((WeakDual.eval_continuous v).comp continuous_subtype_val).tendsto (b i)
      |>.comp ((continuous_apply i).tendsto b |>.comp hb)
    change Tendsto (fun n => ⟪f (φ n) i,v⟫) atTop (𝓝 ((b i).1 v)) at ht
    simpa only [InnerProductSpace.toDual_symm_apply,WeakDual.toStrongDual_apply] using ht
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
abbrev RealL2 := Lp ℝ 2 μ
def oneL2 : RealL2 μ := indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ Set.univ) 1
lemma oneL2_ae : oneL2 μ =ᵐ[μ] (fun _ => (1 : ℝ)) := by
  simpa only [oneL2,Set.indicator_univ] using (indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ)
    (hμs := measure_ne_top μ Set.univ) (c := (1 : ℝ)))
lemma weak_limit_nonneg {f : ℕ → RealL2 μ} {b : RealL2 μ}
    (ht : ∀ v, Tendsto (fun n => ⟪f n,v⟫) atTop (𝓝 ⟪b,v⟫))
    (hf : ∀ n, 0 ≤ᵐ[μ] f n) : 0 ≤ᵐ[μ] b := by
  apply ae_nonneg_of_forall_setIntegral_nonneg (MemLp.integrable (by norm_num) (Lp.memLp b))
  intro s hs hμs
  have h := ht (indicatorConstLp 2 hs hμs.ne 1)
  have he (v : RealL2 μ) : ⟪v,indicatorConstLp 2 hs hμs.ne 1⟫ = ∫ x in s, v x ∂μ := by
    rw [real_inner_comm,L2.inner_indicatorConstLp_one]
  simp_rw [he] at h
  exact ge_of_tendsto h (Eventually.of_forall fun n => integral_nonneg_of_ae (ae_restrict_of_ae (hf n)))
lemma weak_limit_le_one {f : ℕ → RealL2 μ} {b : RealL2 μ}
    (ht : ∀ v, Tendsto (fun n => ⟪f n,v⟫) atTop (𝓝 ⟪b,v⟫))
    (hf : ∀ n, f n ≤ᵐ[μ] (fun _ => (1 : ℝ))) : b ≤ᵐ[μ] (fun _ => (1 : ℝ)) := by
  have hh : 0 ≤ᵐ[μ] (oneL2 μ-b) := weak_limit_nonneg μ
    (f := fun n => oneL2 μ-f n) (fun v => by simpa only [inner_sub_left] using tendsto_const_nhds.sub (ht v)) (fun n => by
      filter_upwards [Lp.coeFn_sub (oneL2 μ) (f n),oneL2_ae μ,hf n] with x hx h1 hn
      simpa only [hx,Pi.sub_apply,Pi.zero_apply,h1,sub_nonneg] using hn)
  filter_upwards [hh,Lp.coeFn_sub (oneL2 μ) b,oneL2_ae μ] with x hx he h1
  simpa only [he,Pi.sub_apply,Pi.zero_apply,h1,sub_nonneg] using hx
lemma weak_limit_sum {ι : Type*} [Fintype ι] {f : ℕ → ι → RealL2 μ} {b : ι → RealL2 μ}
    (ht : ∀ i v, Tendsto (fun n => ⟪f n i,v⟫) atTop (𝓝 ⟪b i,v⟫))
    (hf : ∀ n, ∑ i, f n i = oneL2 μ) : ∑ i, b i = oneL2 μ := by
  apply ext_inner_right ℝ
  intro v
  have hh := tendsto_finsetSum Finset.univ (fun i _ => ht i v)
  simp_rw [← sum_inner,hf] at hh
  exact tendsto_nhds_unique hh tendsto_const_nhds
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k)
def Typical (z : ℂ) : Prop := DensityOne {w | c w=c z} z
def TypicalSampling (y : ℂ) (r : ℝ) : Prop :=
  0 < r ∧ ∀ᵐ t ∂angularMeasure, Typical c (y+(r : ℂ)*direction t)
lemma ae_typicalSampling (hc : Measurable c) {r : ℝ} (hr : 0<r) :
    ∀ᵐ y ∂(volume : Measure ℂ), TypicalSampling c y r := by
  have hq : QuasiMeasurePreserving (fun p : ℂ × Angles => p.1+(r : ℂ)*direction p.2)
      ((volume : Measure ℂ).prod angularMeasure) volume :=
    QuasiMeasurePreserving.prod_of_left
      (measurable_fst.add (measurable_const.mul (direction_continuous.measurable.comp measurable_snd)))
      (Eventually.of_forall fun t => (measurePreserving_add_right (volume : Measure ℂ)
        ((r : ℂ)*direction t)).quasiMeasurePreserving)
  have hh : ∀ᵐ p ∂((volume : Measure ℂ).prod angularMeasure), Typical c (p.1+(r : ℂ)*direction p.2) :=
    hq.ae (ae_density_actual c hc)
  exact (Measure.ae_ae_of_ae_prod hh).mono fun y hy => ⟨hr,hy⟩
def sampleFn (y : ℂ) (r : ℝ) (i : Fin k) (t : Angles) : ℝ :=
  if c (y+(r : ℂ)*direction t)=i then 1 else 0
lemma sampleFn_measurable (hc : Measurable c) (y : ℂ) (r : ℝ) (i : Fin k) :
    Measurable (sampleFn c y r i) := by
  exact measurable_one.piecewise (measurableSet_eq_fun
    (hc.comp (measurable_const.add (measurable_const.mul direction_continuous.measurable))) measurable_const) measurable_zero
lemma sampleFn_nonneg (y : ℂ) (r : ℝ) (i : Fin k) (t : Angles) : 0 ≤ sampleFn c y r i t := by
  simp only [sampleFn]; split_ifs <;> norm_num
lemma sampleFn_le_one (y : ℂ) (r : ℝ) (i : Fin k) (t : Angles) : sampleFn c y r i t ≤ 1 := by
  simp only [sampleFn]; split_ifs <;> norm_num
lemma sampleFn_memLp (hc : Measurable c) (y : ℂ) (r : ℝ) (i : Fin k) :
    MemLp (sampleFn c y r i) 2 angularMeasure := by
  apply MemLp.of_bound (sampleFn_measurable c hc y r i).aestronglyMeasurable 1
  exact Eventually.of_forall fun t => by rw [Real.norm_eq_abs,abs_of_nonneg (sampleFn_nonneg c y r i t)]; exact sampleFn_le_one c y r i t
def sample (hc : Measurable c) (y : ℂ) (r : ℝ) (i : Fin k) : RealL2 angularMeasure :=
  (sampleFn_memLp c hc y r i).toLp _
lemma sample_ae (hc : Measurable c) (y : ℂ) (r : ℝ) (i : Fin k) :
    sample c hc y r i =ᵐ[angularMeasure] sampleFn c y r i := MemLp.coeFn_toLp _
lemma sample_norm_le (hc : Measurable c) (y : ℂ) (r : ℝ) (i : Fin k) :
    ‖sample c hc y r i‖ ≤ 1 := by
  have hh : ∀ᵐ t ∂angularMeasure, ‖sample c hc y r i t‖ ≤ 1 := by
    filter_upwards [sample_ae c hc y r i] with t ht
    rw [ht,Real.norm_eq_abs,abs_of_nonneg (sampleFn_nonneg c y r i t)]
    exact sampleFn_le_one c y r i t
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (by norm_num : (0 : ℝ) ≤ 1) hh
lemma sample_sum (hc : Measurable c) (y : ℂ) (r : ℝ) :
    ∑ i, sample c hc y r i = oneL2 angularMeasure := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => sample c hc y r i),
    ae_all_iff.mpr (sample_ae c hc y r),oneL2_ae angularMeasure] with t ht ha h1
  rw [ht,h1]
  simp only [ha,sampleFn]
  simp
lemma sampling_weak_compact (hc : Measurable c) (y : ℕ → ℂ) (r : ℕ → ℝ) :
    ∃ b : Fin k → RealL2 angularMeasure, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ i, 0 ≤ᵐ[angularMeasure] b i) ∧ (∀ i, b i ≤ᵐ[angularMeasure] (fun _ => (1 : ℝ))) ∧
      (∑ i, b i = oneL2 angularMeasure) ∧
      ∀ i v, Tendsto (fun n => ⟪sample c hc (y (φ n)) (r (φ n)) i,v⟫) atTop (𝓝 ⟪b i,v⟫) := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  obtain ⟨b,φ,hφ,_,hb⟩ := exists_finite_weak_subseq
    (fun n i => sample c hc (y n) (r n) i) 1 (fun n i => sample_norm_le c hc (y n) (r n) i)
  refine ⟨b,φ,hφ,?_,?_,?_,hb⟩
  · intro i
    apply weak_limit_nonneg angularMeasure (hb i)
    intro n
    filter_upwards [sample_ae c hc (y (φ n)) (r (φ n)) i] with t ht
    simpa only [ht,Pi.zero_apply] using sampleFn_nonneg c _ _ i t
  · intro i
    apply weak_limit_le_one angularMeasure (hb i)
    intro n
    filter_upwards [sample_ae c hc (y (φ n)) (r (φ n)) i] with t ht
    simpa only [ht] using sampleFn_le_one c _ _ i t
  · exact weak_limit_sum angularMeasure hb (fun n => sample_sum c hc (y (φ n)) (r (φ n)))
end EuclideanFiveColor
end

noncomputable section
open Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor.WeakBall
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace.SeparableSpace E]
abbrev Space := {v : WeakDual ℝ E // WeakDual.toStrongDual v ∈ Metric.closedBall 0 1}
instance : CompactSpace (Space E) := isCompact_iff_compactSpace.mp (WeakDual.isCompact_closedBall 0 1)
instance : TopologicalSpace.MetrizableSpace (Space E) :=
  WeakDual.metrizable_of_isCompact ℝ E _ (WeakDual.isCompact_closedBall 0 1)
def value (a : Space E) : E := (InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual a.1)
omit [TopologicalSpace.SeparableSpace E] in
lemma value_norm (a : Space E) : ‖value E a‖ ≤ 1 := by
  simpa only [value,LinearIsometryEquiv.norm_map,Metric.mem_closedBall,dist_zero_right] using a.2
omit [TopologicalSpace.SeparableSpace E] in
lemma value_eval (a : Space E) (v : E) : ⟪value E a,v⟫ = a.1 v := by
  simp only [value,InnerProductSpace.toDual_symm_apply,WeakDual.toStrongDual_apply]
def ofNorm (v : E) (hv : ‖v‖ ≤ 1) : Space E := ⟨weakHilbert v,by
  simpa only [weakHilbert,StrongDual.toStrongDual_toWeakDual,Metric.mem_closedBall,dist_zero_right,
    LinearIsometryEquiv.norm_map] using hv⟩
omit [TopologicalSpace.SeparableSpace E] in
@[simp] lemma value_ofNorm (v : E) (hv : ‖v‖ ≤ 1) : value E (ofNorm E v hv) = v := by
  simp only [value,ofNorm,weakHilbert,StrongDual.toStrongDual_toWeakDual,LinearIsometryEquiv.symm_apply_apply]
omit [TopologicalSpace.SeparableSpace E] in
lemma continuous_eval (v : E) : Continuous (fun a : Space E => ⟪value E a,v⟫) := by
  simp_rw [value_eval]
  exact (WeakDual.eval_continuous v).comp continuous_subtype_val
omit [TopologicalSpace.SeparableSpace E] in
lemma tendsto_iff {I : Type*} {l : Filter I} {f : I → Space E} {b : Space E} :
    Tendsto f l (𝓝 b) ↔ ∀ v : E, Tendsto (fun n => ⟪value E (f n),v⟫) l (𝓝 ⟪value E b,v⟫) := by
  simp only [value_eval]
  rw [tendsto_subtype_rng, tendsto_iff_forall_eval_tendsto_topDualPairing]
  rfl
end EuclideanFiveColor.WeakBall
end

noncomputable section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
lemma bounded_test_error {f v g : X → ℝ} (hf : AEStronglyMeasurable f μ)
    (hfb : ∀ᵐ x ∂μ, ‖f x‖ ≤ 1) (hv : Integrable v μ) (hg : Integrable g μ) :
    dist (∫ x, f x*v x ∂μ) (∫ x, f x*g x ∂μ) ≤ ∫ x, ‖v x-g x‖ ∂μ := by
  have hft : MemLp f ⊤ μ := MemLp.of_bound hf 1 hfb
  have hiv : Integrable (fun x => f x*v x) μ := hv.mul_of_top_right hft
  have hig : Integrable (fun x => f x*g x) μ := hg.mul_of_top_right hft
  rw [dist_eq_norm,← integral_sub hiv hig]
  calc
    _ ≤ ∫ x, ‖f x*v x-f x*g x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖v x-g x‖ ∂μ := by
      apply integral_mono_ae ((hv.mul_of_top_right hft).sub (hg.mul_of_top_right hft)).norm (hv.sub hg).norm
      filter_upwards [hfb] with x hx
      change ‖f x * v x - f x * g x‖ ≤ ‖v x - g x‖
      rw [← mul_sub,norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hx
lemma weak_L2_to_weakStar {f : ℕ → Lp ℝ 2 μ} {b : Lp ℝ 2 μ}
    (hf : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ 1) (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ 1)
    (ht : ∀ v : Lp ℝ 2 μ, Tendsto (fun n => ⟪f n,v⟫) atTop (𝓝 ⟪b,v⟫))
    {v : X → ℝ} (hv : Integrable v μ) :
    Tendsto (fun n => ∫ x, f n x*v x ∂μ) atTop (𝓝 (∫ x, b x*v x ∂μ)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨g,hg,hgm⟩ := (memLp_one_iff_integrable.mpr hv).exists_simpleFunc_eLpNorm_sub_lt (by simp : (1 : ENNReal) ≠ ⊤)
    (ENNReal.ofReal_ne_zero_iff.mpr (by positivity : 0 < ε/3))
  obtain ⟨C,hC⟩ := g.exists_forall_norm_le
  have hg2 : MemLp g 2 μ := MemLp.of_bound g.measurable.aestronglyMeasurable C (Eventually.of_forall hC)
  have hgi : Integrable (fun x => g x) μ := memLp_one_iff_integrable.mp hgm
  have herr : (∫ x, ‖v x-g x‖ ∂μ) < ε/3 := by
    change (∫ x, ‖(v - (fun x => g x)) x‖ ∂μ) < ε/3
    rw [integral_norm_eq_lintegral_enorm (hv.sub hgi).aestronglyMeasurable,
      ← eLpNorm_one_eq_lintegral_enorm (hv.sub hgi).aestronglyMeasurable]
    exact (ENNReal.toReal_lt_toReal (ne_top_of_lt hg) ENNReal.ofReal_ne_top).mpr hg |>.trans_eq (ENNReal.toReal_ofReal (by positivity))
  have he (w : Lp ℝ 2 μ) : ⟪w,hg2.toLp g⟫ = ∫ x, w x*g x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg2.coeFn_toLp] with x hx
    simp [hx, mul_comm]
  have htt := ht (hg2.toLp g)
  simp_rw [he] at htt
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp htt (ε/3) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have h1 := bounded_test_error (Lp.aestronglyMeasurable (f n)) (hf n) hv hgi
  have h2 := bounded_test_error (Lp.aestronglyMeasurable b) hb hv hgi
  calc
    _ ≤ dist (∫ x, f n x*v x ∂μ) (∫ x, f n x*g x ∂μ) +
        dist (∫ x, f n x*g x ∂μ) (∫ x, b x*g x ∂μ) +
        dist (∫ x, b x*g x ∂μ) (∫ x, b x*v x ∂μ) := by
      exact dist_triangle4 _ _ _ _
    _ < ε := by rw [dist_comm (∫ x, b x*g x ∂μ)]; linarith [hN n hn]
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
private instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
abbrev TraceVector (k : ℕ) := Fin k → WeakBall.Space (RealL2 angularMeasure)
def traceValue {k : ℕ} (b : TraceVector k) (i : Fin k) : RealL2 angularMeasure :=
  WeakBall.value _ (b i)
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
def sampleCode (y : ℂ) (r : ℝ) : TraceVector k :=
  fun i => WeakBall.ofNorm _ (sample c hc y r i) (sample_norm_le c hc y r i)
@[simp] lemma traceValue_sampleCode (y : ℂ) (r : ℝ) (i : Fin k) :
    traceValue (sampleCode c hc y r) i = sample c hc y r i := WeakBall.value_ofNorm _ _ _
def sampleSet : Set (ℂ × ℝ × TraceVector k) :=
  {p | TypicalSampling c p.1 p.2.1 ∧ p.2.2=sampleCode c hc p.1 p.2.1}
def IsTrace (x : ℂ) (b : TraceVector k) : Prop := (x,1,b) ∈ closure (sampleSet c hc)
lemma trace_realization {x : ℂ} {b : TraceVector k} (hb : IsTrace c hc x b) :
    ∃ y : ℕ → ℂ, ∃ r : ℕ → ℝ, (∀ n, TypicalSampling c (y n) (r n)) ∧
      Tendsto y atTop (𝓝 x) ∧ Tendsto r atTop (𝓝 1) ∧
      Tendsto (fun n => sampleCode c hc (y n) (r n)) atTop (𝓝 b) := by
  obtain ⟨p,hp,ht⟩ := mem_closure_iff_seq_limit.mp hb
  simp only [nhds_prod_eq] at ht
  refine ⟨fun n => (p n).1,fun n => (p n).2.1,fun n => (hp n).1,ht.fst,ht.snd.fst,?_⟩
  simpa only [show (fun n => (p n).2.2) = (fun n => sampleCode c hc (p n).1 (p n).2.1) from
    funext fun n => (hp n).2] using ht.snd.snd
lemma trace_of_realization {x : ℂ} {b : TraceVector k} {y : ℕ → ℂ} {r : ℕ → ℝ}
    (htr : ∀ n, TypicalSampling c (y n) (r n)) (hy : Tendsto y atTop (𝓝 x))
    (hr : Tendsto r atTop (𝓝 1))
    (hb : Tendsto (fun n => sampleCode c hc (y n) (r n)) atTop (𝓝 b)) : IsTrace c hc x b := by
  exact mem_closure_of_tendsto (hy.prodMk_nhds (hr.prodMk_nhds hb))
    (Eventually.of_forall fun n => show (y n,r n,sampleCode c hc (y n) (r n)) ∈ sampleSet c hc from ⟨htr n,rfl⟩)
lemma exists_trace (x : ℂ) : ∃ b : TraceVector k, IsTrace c hc x b := by
  have hd : Dense {y : ℂ | TypicalSampling c y 1} := Measure.dense_of_ae
    (ae_typicalSampling c hc (by norm_num : (0 : ℝ)<1))
  obtain ⟨y,hy,hyt⟩ := mem_closure_iff_seq_limit.mp (hd x)
  obtain ⟨b,_,φ,hφ,hb⟩ := (isCompact_univ : IsCompact (Set.univ : Set (TraceVector k))).isSeqCompact.subseq_of_frequently_in
    (Eventually.frequently (Eventually.of_forall fun n => Set.mem_univ (sampleCode c hc (y n) 1)))
  exact ⟨b,trace_of_realization c hc (fun n => hy (φ n)) (hyt.comp hφ.tendsto_atTop) tendsto_const_nhds hb⟩
lemma isClosed_traceGraph : IsClosed {p : ℂ × TraceVector k | IsTrace c hc p.1 p.2} := by
  exact isClosed_closure.preimage (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
lemma isCompact_traces (x : ℂ) : IsCompact {b : TraceVector k | IsTrace c hc x b} := by
  apply IsClosed.isCompact
  exact isClosed_closure.preimage (continuous_const.prodMk (continuous_const.prodMk continuous_id))
lemma trace_limit {x : ℕ → ℂ} {b : ℕ → TraceVector k} {y : ℂ} {a : TraceVector k}
    (h : ∀ n, IsTrace c hc (x n) (b n)) (hx : Tendsto x atTop (𝓝 y))
    (hb : Tendsto b atTop (𝓝 a)) : IsTrace c hc y a :=
  (isClosed_traceGraph c hc).mem_of_tendsto (hx.prodMk_nhds hb) (Eventually.of_forall h)
lemma traceCode_tendsto_iff {I : Type*} {l : Filter I} {f : I → TraceVector k} {b : TraceVector k} :
    Tendsto f l (𝓝 b) ↔ ∀ i v, Tendsto (fun n => ⟪traceValue (f n) i,v⟫) l (𝓝 ⟪traceValue b i,v⟫) := by
  rw [tendsto_pi_nhds]
  exact forall_congr' fun i => WeakBall.tendsto_iff _
lemma trace_bounds {x : ℂ} {b : TraceVector k} (hb : IsTrace c hc x b) :
    (∀ i, 0 ≤ᵐ[angularMeasure] traceValue b i) ∧
    (∀ i, traceValue b i ≤ᵐ[angularMeasure] (fun _ => (1 : ℝ))) ∧
    ∑ i, traceValue b i = oneL2 angularMeasure := by
  obtain ⟨y,r,_,_,_,ht⟩ := trace_realization c hc hb
  have hw := traceCode_tendsto_iff.mp ht
  simp only [traceValue_sampleCode] at hw
  refine ⟨?_,?_,?_⟩
  · intro i
    apply weak_limit_nonneg angularMeasure (hw i)
    intro n
    filter_upwards [sample_ae c hc (y n) (r n) i] with t he
    simpa only [he,Pi.zero_apply] using sampleFn_nonneg c (y n) (r n) i t
  · intro i
    apply weak_limit_le_one angularMeasure (hw i)
    intro n
    filter_upwards [sample_ae c hc (y n) (r n) i] with t he
    simpa only [he] using sampleFn_le_one c (y n) (r n) i t
  · exact weak_limit_sum angularMeasure hw (fun n => sample_sum c hc (y n) (r n))
lemma trace_realization_weakStar {x : ℂ} {b : TraceVector k} (hb : IsTrace c hc x b) :
    ∃ y : ℕ → ℂ, ∃ r : ℕ → ℝ, (∀ n, TypicalSampling c (y n) (r n)) ∧
      Tendsto y atTop (𝓝 x) ∧ Tendsto r atTop (𝓝 1) ∧
      ∀ i (v : Angles → ℝ), Integrable v angularMeasure →
        Tendsto (fun n => ∫ t, sampleFn c (y n) (r n) i t*v t ∂angularMeasure) atTop
          (𝓝 (∫ t, traceValue b i t*v t ∂angularMeasure)) := by
  obtain ⟨y,r,hy,hyt,hrt,hbt⟩ := trace_realization c hc hb
  refine ⟨y,r,hy,hyt,hrt,fun i v hv => ?_⟩
  have hbounds := trace_bounds c hc hb
  have hbn : ∀ᵐ t ∂angularMeasure, ‖traceValue b i t‖ ≤ 1 := by
    filter_upwards [hbounds.1 i,hbounds.2.1 i] with t ht1 ht2
    rwa [Real.norm_eq_abs,abs_of_nonneg ht1]
  have hsn (n : ℕ) : ∀ᵐ t ∂angularMeasure, ‖sample c hc (y n) (r n) i t‖ ≤ 1 := by
    filter_upwards [sample_ae c hc (y n) (r n) i] with t ht
    rw [ht,Real.norm_eq_abs,abs_of_nonneg (sampleFn_nonneg c _ _ _ t)]
    exact sampleFn_le_one c _ _ _ t
  have hw := weak_L2_to_weakStar hsn hbn
    (by simpa only [traceValue_sampleCode] using (traceCode_tendsto_iff.mp hbt) i) hv
  convert hw using 1
  ext n
  exact (integral_congr_ae ((sample_ae c hc (y n) (r n) i).mono fun t ht => congrArg (fun a => a*v t) ht)).symm
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Topology Filter Set
namespace EuclideanFiveColor
variable {X I : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
/-- A finite-measure essential union is generated by countably many members of the original family. -/
lemma exists_countable_essential_union (A : I → Set X) (hm : ∀ i, MeasurableSet (A i)) :
    ∃ J : Set I, J.Countable ∧ ∀ i, A i ≤ᵐ[μ] (⋃ j ∈ J, A j) := by
  let S : Set ENNReal := {m | ∃ J : Set I, J.Countable ∧ μ (⋃ j ∈ J, A j)=m}
  have hs : S.Nonempty := ⟨0,∅,Set.countable_empty,by simp⟩
  obtain ⟨f,_,ht,hf⟩ := exists_seq_tendsto_sSup hs (OrderTop.bddAbove S)
  choose J hJ he using hf
  let K : Set I := ⋃ n, J n
  have hK : K.Countable := Set.countable_iUnion hJ
  let D : Set X := ⋃ j ∈ K, A j
  have hD : MeasurableSet D := MeasurableSet.biUnion hK (fun j _ => hm j)
  have hS : μ D ∈ S := ⟨K,hK,rfl⟩
  have hmax : μ D = sSup S := le_antisymm (le_sSup hS) (le_of_tendsto ht (Eventually.of_forall (fun n => by
    rw [← he n]
    apply measure_mono
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨j,hj,hx⟩
    exact Set.mem_iUnion₂.mpr ⟨j,Set.mem_iUnion.mpr ⟨n,hj⟩,hx⟩)))
  refine ⟨K,hK,fun i => ?_⟩
  have hun : μ (D ∪ A i) ≤ μ D := by
    rw [hmax]
    apply le_sSup
    refine ⟨insert i K,hK.insert i,?_⟩
    congr 1
    ext x
    simp only [Set.mem_iUnion,Set.mem_insert_iff,Set.mem_union,D]
    aesop
  have heq : μ (D ∪ A i) = μ D := le_antisymm hun (measure_mono Set.subset_union_left)
  have hzero : μ ((D ∪ A i) \ D)=0 := by
    rw [measure_sdiff Set.subset_union_left hD.nullMeasurableSet (measure_ne_top μ D),heq,tsub_self]
  have hz : μ (A i \ D)=0 := measure_mono_null (by intro x hx; exact ⟨Or.inr hx.1,hx.2⟩) hzero
  simpa only [ae_le_set] using hz
end EuclideanFiveColor
end

end OAI

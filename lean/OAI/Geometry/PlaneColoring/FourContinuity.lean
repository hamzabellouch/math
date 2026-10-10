import OAI.Geometry.PlaneColoring.States

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
lemma four_avoiding_traces (hw : WeakColoring 5 c) {x : ℂ} (hx : FourCenter c x) :
    ∃ b : Fin 4 → TraceVector 5, (∀e,IsTrace c hc x (b e)) ∧
      ∀e,∀i∈fourEdge e,traceValue (b e) i=0 := by
  have hh (i j : Fin 5) (he : TransitionEdge c i j x) :
      ∃ b : TraceVector 5, IsTrace c hc x b ∧ ∀a∈({i,j} : Finset (Fin 5)),traceValue b a=0 := by
    obtain ⟨b,hb,hi,hj⟩ := transition_avoiding_trace c hc hw he
    refine ⟨b,hb,?_⟩
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl|rfl <;> assumption
  have he (e : Fin 4) : ∃ b : TraceVector 5, IsTrace c hc x b ∧ ∀i∈fourEdge e,traceValue b i=0 := by
    fin_cases e
    · exact hh 0 1 hx.1
    · exact hh 1 2 hx.2.1
    · exact hh 2 3 hx.2.2.1
    · exact hh 3 0 hx.2.2.2
  choose b hb hz using he
  exact ⟨b,hb,hz⟩
lemma four_state_trace_domination (hw : WeakColoring 5 c) {x : ℂ} (hx : FourCenter c x)
    (b : Fin 4 → TraceVector 5) (hb : ∀e,IsTrace c hc x (b e))
    (hz : ∀e,∀i∈fourEdge e,traceValue (b e) i=0) (s : Fin 3) {i : Fin 5} (hi : i∈fourGroup s) :
    {t | fourState c hc x t=s}.indicator (fun _ => (1:ℝ)) ≤ᵐ[angularMeasure]
      (fun t => ∑e,traceValue (b e) i t) := by
  have hs (e : Fin 4) : (fun t => ∑a,traceValue (b e) a t)=ᵐ[angularMeasure] (fun _ => (1:ℝ)) := by
    have hh := Lp.coeFn_fun_finsetSum Finset.univ (traceValue (b e))
    rw [(trace_bounds c hc (hb e)).2.2] at hh
    exact hh.symm.trans (oneL2_ae angularMeasure)
  have hzero (e : Fin 4) (a : Fin 5) : ∀ᵐt∂angularMeasure,a∈fourEdge e → traceValue (b e) a t=0 := by
    by_cases ha : a∈fourEdge e
    · rw [hz e a ha]
      filter_upwards [Lp.coeFn_zero ℝ 2 angularMeasure] with t ht
      exact fun _ => ht
    · exact Eventually.of_forall fun _ => fun h => (ha h).elim
  filter_upwards [four_palette_admissible c hc hw hx,
    ae_all_iff.mpr (fun e => ae_all_iff.mpr fun a => (trace_bounds c hc (hb e)).1 a),
    ae_all_iff.mpr hs,ae_all_iff.mpr (fun e => ae_all_iff.mpr (hzero e)),
    ae_all_iff.mpr (fun e => ae_all_iff.mpr fun a => tracePositive_le_palette c hc x a ⟨b e,hb e⟩)]
    with t hadm hnon hsum hzero hpal
  by_cases hts : fourState c hc x t=s
  · rw [Set.indicator_of_mem (show t∈{t | fourState c hc x t=s} from hts)]
    obtain ⟨e,_,hep⟩ := four_trace_edge (palette c hc x t) hadm i (by simpa only [← hts, fourState] using hi)
    have hj (a : Fin 5) (ha : a≠i) : traceValue (b e) a t=0 := by
      by_cases he : a∈fourEdge e
      · exact hzero e a he
      · apply le_antisymm _ (hnon e a)
        by_contra! hpos
        have hp := (mem_palette c hc x t a).mpr (hpal e a hpos)
        exact he (hep (Finset.mem_sdiff.mpr ⟨hp,by simpa using ha⟩))
    have heq : traceValue (b e) i t=1 := by
      rw [← hsum e,Finset.sum_eq_single i _ (by simp)]
      intro a _ hai
      exact hj a hai
    rw [← heq]
    exact Finset.single_le_sum (fun j _ => hnon j i) (Finset.mem_univ e)
  · rw [Set.indicator_of_notMem (show t∉{t | fourState c hc x t=s} from hts)]
    exact Finset.sum_nonneg (fun e _ => hnon e i)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} [IsProbabilityMeasure μ]
def indL2 (A : Set Y) (hA : MeasurableSet A) : RealL2 μ :=
  indicatorConstLp 2 hA (measure_ne_top μ A) 1
lemma indL2_ae (A : Set Y) (hA : MeasurableSet A) :
    indL2 (μ := μ) A hA =ᵐ[μ] A.indicator (fun _ => (1:ℝ)) := indicatorConstLp_coeFn
lemma indL2_nonneg (A : Set Y) (hA : MeasurableSet A) : 0≤ᵐ[μ] indL2 (μ := μ) A hA := by
  filter_upwards [indL2_ae (μ := μ) A hA] with t ht
  rw [ht]
  exact indicator_nonneg (fun _ _ => zero_le_one) _
lemma indL2_le_one (A : Set Y) (hA : MeasurableSet A) : indL2 (μ := μ) A hA≤ᵐ[μ] (fun _ => (1:ℝ)) := by
  filter_upwards [indL2_ae (μ := μ) A hA] with t ht
  rw [ht]
  exact indicator_le_self' (fun _ _ => zero_le_one) _
lemma indL2_norm (A : Set Y) (hA : MeasurableSet A) : ‖indL2 (μ := μ) A hA‖≤1 := by
  have hh : ∀ᵐt∂μ,‖indL2 (μ := μ) A hA t‖≤1 := by
    filter_upwards [indL2_nonneg (μ := μ) A hA,indL2_le_one (μ := μ) A hA] with t ht hu
    rwa [Real.norm_eq_abs,abs_of_nonneg ht]
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (by norm_num : (0:ℝ)≤1) hh
lemma indL2_sum {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {s : Y → ι} (hs : Measurable s) :
    ∑ i, indL2 (μ := μ) {t | s t=i} (measurableSet_eq_fun hs measurable_const)=oneL2 μ := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => indL2 (μ := μ) {t | s t=i} (measurableSet_eq_fun hs measurable_const)),
    ae_all_iff.mpr (fun i => indL2_ae (μ := μ) {t | s t=i} (measurableSet_eq_fun hs measurable_const)),oneL2_ae μ] with t ht ha hu
  rw [ht,hu]
  simp only [ha,Set.indicator_apply,mem_ofPred_eq]
  simp
lemma weak_limit_le {f g : ℕ → RealL2 μ} {a b : RealL2 μ}
    (hf : ∀v,Tendsto (fun n => ⟪f n,v⟫) atTop (𝓝 ⟪a,v⟫))
    (hg : ∀v,Tendsto (fun n => ⟪g n,v⟫) atTop (𝓝 ⟪b,v⟫))
    (hle : ∀n,f n≤ᵐ[μ] g n) : a≤ᵐ[μ] b := by
  have hh : 0≤ᵐ[μ] b-a := weak_limit_nonneg μ (f := fun n => g n-f n)
    (fun v => by simpa only [inner_sub_left] using (hg v).sub (hf v)) (fun n => by
      filter_upwards [Lp.coeFn_sub (g n) (f n),hle n] with t ht hh
      simpa only [ht,Pi.sub_apply,Pi.zero_apply,sub_nonneg] using hh)
  filter_upwards [hh,Lp.coeFn_sub b a] with t ht he
  simpa only [he,Pi.sub_apply,Pi.zero_apply,sub_nonneg] using ht
lemma indL2_weak_L1 {A : ℕ → Set Y} (hA : ∀n,MeasurableSet (A n)) {B : Set Y} (hB : MeasurableSet B)
    (hw : ∀v : RealL2 μ,Tendsto (fun n => ⟪indL2 (A n) (hA n),v⟫) atTop (𝓝 ⟪indL2 B hB,v⟫)) :
    Tendsto (fun n => ∫t,‖(A n).indicator (fun _ => (1:ℝ)) t-B.indicator (fun _ => (1:ℝ)) t‖ ∂μ) atTop (𝓝 0) := by
  have hone (w : RealL2 μ) : ⟪w,oneL2 μ⟫=∫t,w t ∂μ := by
    rw [real_inner_comm]
    simpa only [oneL2,setIntegral_univ] using
      L2.inner_indicatorConstLp_one MeasurableSet.univ (measure_ne_top μ univ) w
  have hBB : ⟪indL2 (μ := μ) B hB,indL2 B hB⟫=⟪indL2 (μ := μ) B hB,oneL2 μ⟫ := by
    rw [hone,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [indL2_ae (μ := μ) B hB] with t ht
    rw [ht]
    by_cases hb : t∈B <;> simp [hb]
  have he (n : ℕ) : (∫t,‖(A n).indicator (fun _ => (1:ℝ)) t-B.indicator (fun _ => (1:ℝ)) t‖ ∂μ) =
      ⟪indL2 (μ := μ) (A n) (hA n),oneL2 μ⟫+⟪indL2 (μ := μ) B hB,oneL2 μ⟫-
      2*⟪indL2 (μ := μ) (A n) (hA n),indL2 (μ := μ) B hB⟫ := by
    rw [hone,hone,L2.inner_def,← integral_const_mul,← integral_add,
      ← integral_sub]
    · apply integral_congr_ae
      filter_upwards [indL2_ae (μ := μ) (A n) (hA n),indL2_ae (μ := μ) B hB] with t ht hu
      rw [ht,hu]
      by_cases ha : t∈A n <;> by_cases hb : t∈B <;> norm_num [ha,hb]
    · exact ((Lp.memLp _).integrable (by norm_num)).add ((Lp.memLp _).integrable (by norm_num))
    · exact (L2.integrable_inner _ _).const_mul 2
    · exact (Lp.memLp _).integrable (by norm_num)
    · exact (Lp.memLp _).integrable (by norm_num)
  simp_rw [he]
  have ht := ((hw (oneL2 μ)).add_const ⟪indL2 (μ := μ) B hB,oneL2 μ⟫).sub
    ((hw (indL2 (μ := μ) B hB)).const_mul 2)
  rw [hBB,show ⟪indL2 (μ := μ) B hB, oneL2 μ⟫+⟪indL2 (μ := μ) B hB,oneL2 μ⟫-
    2*⟪indL2 (μ := μ) B hB,oneL2 μ⟫=0 by ring] at ht
  exact ht
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
def fourStateL2 (x : ℂ) (s : Fin 3) : RealL2 angularMeasure :=
  indL2 {t | fourState c hc x t=s} (measurableSet_eq_fun (fourState_measurable c hc x) measurable_const)
lemma four_weak_limit_identify (hw : WeakColoring 5 c)
    {x : ℕ → ℂ} {y : ℂ} (hx : ∀n,FourCenter c (x n)) (hy : FourCenter c y)
    (hxt : Tendsto x atTop (𝓝 y)) {f : Fin 3 → RealL2 angularMeasure}
    (hf : ∀s v,Tendsto (fun n => ⟪fourStateL2 c hc (x n) s,v⟫) atTop (𝓝 ⟪f s,v⟫))
    (b : ℕ → Fin 4 → TraceVector 5) (a : Fin 4 → TraceVector 5)
    (hb : ∀n e,IsTrace c hc (x n) (b n e))
    (hz : ∀n e,∀i∈fourEdge e,traceValue (b n e) i=0)
    (ht : ∀e,Tendsto (fun n => b n e) atTop (𝓝 (a e))) :
    ∀s,f s=fourStateL2 c hc y s := by
  have hat (e : Fin 4) : IsTrace c hc y (a e) := trace_limit c hc (fun n => hb n e) hxt (ht e)
  have hdom (s : Fin 3) (i : Fin 5) (hi : i∈fourGroup s) :
      f s≤ᵐ[angularMeasure] (∑e,traceValue (a e) i : RealL2 angularMeasure) := by
    apply weak_limit_le (hf s) (f := fun n => fourStateL2 c hc (x n) s)
      (g := fun n => ∑e,traceValue (b n e) i)
      (fun v => ?_) (fun n => ?_)
    · simpa only [sum_inner] using tendsto_finsetSum Finset.univ
        (fun e _ => traceCode_tendsto_iff.mp (ht e) i v)
    · filter_upwards [indL2_ae (μ := angularMeasure) {t | fourState c hc (x n) t=s}
        (measurableSet_eq_fun (fourState_measurable c hc (x n)) measurable_const),
        Lp.coeFn_fun_finsetSum Finset.univ (fun e => traceValue (b n e) i),
        four_state_trace_domination c hc hw (hx n) (b n) (hb n) (hz n) s hi] with t h₁ h₂ h₃
      simpa only [fourStateL2,h₁,h₂] using h₃
  have hnon (s : Fin 3) : 0≤ᵐ[angularMeasure] f s :=
    weak_limit_nonneg angularMeasure (hf s) (fun n => indL2_nonneg _ _)
  have hsumf : ∑s,f s=oneL2 angularMeasure :=
    weak_limit_sum angularMeasure hf (fun n => indL2_sum (fourState_measurable c hc (x n)))
  have hsupport (s : Fin 3) : ∀ᵐt∂angularMeasure,0<f s t → fourGroup s⊆palette c hc y t := by
    have hdom' (i : Fin 5) : ∀ᵐt∂angularMeasure,i∈fourGroup s → f s t≤∑e,traceValue (a e) i t := by
      by_cases hi : i∈fourGroup s
      · filter_upwards [hdom s i hi,Lp.coeFn_fun_finsetSum Finset.univ (fun e => traceValue (a e) i)] with t ht he
        exact fun _ => by simpa only [he] using ht
      · exact Eventually.of_forall fun _ h => (hi h).elim
    filter_upwards [ae_all_iff.mpr hdom',
      ae_all_iff.mpr (fun e => ae_all_iff.mpr fun i => tracePositive_le_palette c hc y i ⟨a e,hat e⟩)] with t hdom hpal hp i hi
    have hsum : 0<∑e,traceValue (a e) i t := hp.trans_le (hdom i hi)
    have hex : ∃e,0<traceValue (a e) i t := by
      by_contra! hh
      exact hsum.not_ge (Finset.sum_nonpos fun e _ => hh e)
    obtain ⟨e,he⟩ := hex
    exact (mem_palette c hc y t i).mpr (hpal e i he)
  intro s
  apply Lp.ext
  have hsumae : (fun t => ∑s,f s t)=ᵐ[angularMeasure] (fun _ => (1:ℝ)) := by
    have hh := Lp.coeFn_fun_finsetSum Finset.univ f
    rw [hsumf] at hh
    exact hh.symm.trans (oneL2_ae angularMeasure)
  filter_upwards [ae_all_iff.mpr hnon,ae_all_iff.mpr hsupport,hsumae,
    four_palette_admissible c hc hw hy,
    indL2_ae (μ := angularMeasure) {t | fourState c hc y t=s}
      (measurableSet_eq_fun (fourState_measurable c hc y) measurable_const)] with t hn hp hsum hadm hi
  change f s t=indL2 (μ := angularMeasure) {t | fourState c hc y t=s} _ t
  rw [hi]
  have hz (v : Fin 3) (hv : v≠fourState c hc y t) : f v t=0 := by
    apply le_antisymm _ (hn v)
    by_contra! hh
    have he := (four_admissible_character (palette c hc y t) hadm v).mp (hp v hh)
    exact hv he.symm
  by_cases he : fourState c hc y t=s
  · rw [Set.indicator_of_mem (show t∈{t | fourState c hc y t=s} from he)]
    rw [← hsum,Finset.sum_eq_single s _ (by simp)]
    intro v _ hvs
    exact hz v (by simpa only [he] using hvs)
  · rw [Set.indicator_of_notMem (show t∉{t | fourState c hc y t=s} from he)]
    exact hz s (Ne.symm he)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
def fourStateDistance (x y : ℂ) (s : Fin 3) : ℝ :=
  ∫t,‖{t | fourState c hc x t=s}.indicator (fun _ => (1:ℝ)) t-
    {t | fourState c hc y t=s}.indicator (fun _ => (1:ℝ)) t‖ ∂angularMeasure
lemma four_state_subseq_continuity (hw : WeakColoring 5 c)
    {x : ℕ → ℂ} {y : ℂ} (hx : ∀n,FourCenter c (x n)) (hy : FourCenter c y)
    (hxt : Tendsto x atTop (𝓝 y)) :
    ∃φ : ℕ → ℕ,StrictMono φ ∧ ∀s,Tendsto (fun n => fourStateDistance c hc (x (φ n)) y s) atTop (𝓝 0) := by
  obtain ⟨f,φ,hφ,_,hf⟩ := exists_finite_weak_subseq (fun n s => fourStateL2 c hc (x n) s) 1
    (fun _ _ => indL2_norm _ _)
  choose b hb hz using fun n => four_avoiding_traces c hc hw (hx (φ n))
  obtain ⟨a,_,ψ,hψ,ha⟩ := (isCompact_univ : IsCompact (univ : Set (Fin 4 → TraceVector 5))).isSeqCompact
    (fun n => mem_univ (b n))
  have hid := four_weak_limit_identify c hc hw (fun n => hx (φ (ψ n))) hy
    (hxt.comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop))
    (fun s v => (hf s v).comp hψ.tendsto_atTop) (fun n => b (ψ n)) a
    (fun n => hb (ψ n)) (fun n => hz (ψ n))
    (fun e => (continuous_apply e).tendsto a |>.comp ha)
  refine ⟨φ∘ψ,hφ.comp hψ,?_⟩
  intro s
  apply indL2_weak_L1 (fun n => measurableSet_eq_fun (fourState_measurable c hc (x (φ (ψ n)))) measurable_const)
    (measurableSet_eq_fun (fourState_measurable c hc y) measurable_const)
  intro v
  have hh := (hf s v).comp hψ.tendsto_atTop
  rw [hid s] at hh
  exact hh
lemma four_state_continuity (hw : WeakColoring 5 c)
    {x : ℕ → ℂ} {y : ℂ} (hx : ∀n,FourCenter c (x n)) (hy : FourCenter c y)
    (hxt : Tendsto x atTop (𝓝 y)) (s : Fin 3) :
    Tendsto (fun n => fourStateDistance c hc (x n) y s) atTop (𝓝 0) := by
  by_contra hn
  rw [Metric.tendsto_atTop] at hn
  push Not at hn
  obtain ⟨ε,hε,he⟩ := hn
  choose m hm using he
  have hmt : Tendsto m atTop atTop := tendsto_atTop_mono (fun n => (hm n).1) tendsto_id
  obtain ⟨φ,hφ,ht⟩ := four_state_subseq_continuity c hc hw (fun n => hx (m n)) hy (hxt.comp hmt)
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (ht s) ε hε
  exact (hm (φ N)).2.not_gt (hN N le_rfl)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal
namespace EuclideanFiveColor
lemma angleMk_compact_bound {E : Set ℝ} (hE : IsCompact E) :
    ∃ C : ℝ≥0, (volume.restrict E).map ((↑) : ℝ → Angles)≤(C:ENNReal) • angularMeasure := by
  obtain ⟨F,hF⟩ := hE.elim_finite_subcover (fun a : ℝ => Ioo (a-Real.pi) (a+Real.pi))
    (fun _ => isOpen_Ioo) (fun a _ => mem_iUnion.mpr ⟨a,by constructor <;> linarith [Real.pi_pos]⟩)
  let C : ℝ≥0 := ⟨(F.card:ℝ)*(2*Real.pi),by positivity⟩
  refine ⟨C,Measure.le_iff.mpr (fun A hA => ?_)⟩
  rw [Measure.map_apply angleMk_quasiMeasurePreserving.measurable hA,
    Measure.restrict_apply (angleMk_quasiMeasurePreserving.measurable hA),Measure.smul_apply,smul_eq_mul]
  have hsub : ((↑) : ℝ → Angles) ⁻¹' A∩E ⊆
      ⋃a∈F,((↑) : ℝ → Angles) ⁻¹' A∩Ioc (a-Real.pi) ((a-Real.pi)+2*Real.pi) := by
    intro t ht
    obtain ⟨a,ha,h₁,h₂⟩ := mem_iUnion₂.mp (hF ht.2)
    exact mem_iUnion₂.mpr ⟨a,ha,ht.1,h₁,by linarith⟩
  calc
    _ ≤ volume (⋃a∈F,((↑) : ℝ → Angles) ⁻¹' A∩Ioc (a-Real.pi) ((a-Real.pi)+2*Real.pi)) := measure_mono hsub
    _ ≤ ∑a∈F,volume (((↑) : ℝ → Angles) ⁻¹' A∩Ioc (a-Real.pi) ((a-Real.pi)+2*Real.pi)) := measure_biUnion_finset_le F _
    _ = ∑_a∈F,(volume : Measure Angles) A := by
      apply Finset.sum_congr rfl
      intro a _
      exact (AddCircle.add_projection_respects_measure (2*Real.pi) (a-Real.pi) hA).symm
    _ = (C:ENNReal)*angularMeasure A := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]
      simp only [Measure.smul_apply,smul_eq_mul,Finset.sum_const,nsmul_eq_mul]
      change (F.card:ENNReal)*(ENNReal.ofReal (2*Real.pi)*angularMeasure A)=_
      rw [← mul_assoc]
      congr 1
      rw [show (C:ENNReal)=ENNReal.ofReal ((F.card:ℝ)*(2*Real.pi)) from ENNReal.ofReal_coe_nnreal.symm]
      rw [ENNReal.ofReal_mul (by positivity : 0≤(F.card:ℝ)),ENNReal.ofReal_natCast]
lemma angular_compact_L1 {f : ℕ → Angles → ℝ} {g : Angles → ℝ}
    (hf : ∀n,Integrable (f n) angularMeasure) (hg : Integrable g angularMeasure)
    (ht : Tendsto (fun n => ∫t,‖f n t-g t‖ ∂angularMeasure) atTop (𝓝 0))
    {E : Set ℝ} (hE : IsCompact E) :
    Tendsto (fun n => ∫t in E,‖f n (t : Angles)-g (t : Angles)‖) atTop (𝓝 0) := by
  obtain ⟨C,hC⟩ := angleMk_compact_bound hE
  apply squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (fun n => integral_norm_comp_le angleMk_quasiMeasurePreserving.measurable hC ((hf n).sub hg))
  simpa only [mul_zero,Pi.sub_apply] using ht.const_mul (C:ℝ)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma support_lower_semicontinuity {A : Set ℝ} {B : ℕ → Set ℝ}
    (hA : MeasurableSet A) (hB : ∀n,MeasurableSet (B n))
    (ht : ∀E : Set ℝ,IsCompact E → Tendsto
      (fun n => ∫t in E,‖(B n).indicator (fun _ => (1:ℝ)) t-A.indicator (fun _ => (1:ℝ)) t‖) atTop (𝓝 0))
    {b : ℝ} (hb : b∈(volume.restrict A).support) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠn in atTop,∃v∈(volume.restrict (B n)).support,dist v b<ε := by
  let E := Metric.closedBall b (ε/2)
  have hp : 0<(volume.restrict E) A := by
    have hh := (Measure.mem_support_iff_forall b).mp hb (Metric.ball b (ε/2))
      (Metric.ball_mem_nhds b (by positivity))
    rw [Measure.restrict_apply measurableSet_ball] at hh
    rw [Measure.restrict_apply hA]
    apply hh.trans_le (measure_mono _)
    exact fun t ht => ⟨ht.2,Metric.ball_subset_closedBall ht.1⟩
  let : IsFiniteMeasure (volume.restrict E) := ⟨by simpa [E] using (isCompact_closedBall b (ε/2)).measure_lt_top (μ := (volume : Measure ℝ))⟩
  have hpos := indicator_inter_positive (μ := volume.restrict E) hA hB (fun _ => hA) hp
    (ht E (isCompact_closedBall _ _)) (by simp)
  filter_upwards [hpos] with n hn
  have hpB : (volume.restrict (B n)) E≠0 := by
    apply ne_of_gt
    rw [Measure.restrict_apply measurableSet_closedBall]
    rw [Measure.restrict_apply ((hB n).inter hA)] at hn
    exact hn.trans_le (measure_mono (fun t ht => ⟨ht.2,ht.1.1⟩))
  obtain ⟨v,hv,hs⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpB (ae_restrict_of_ae (volume.restrict (B n)).support_mem_ae)
  exact ⟨v,hs,(show dist v b≤ε/2 from hv).trans_lt (by linarith)⟩
lemma support_sequence_continuity {A : Set ℝ} {B : ℕ → Set ℝ}
    (hA : MeasurableSet A) (hB : ∀n,MeasurableSet (B n)) (hpB : ∀n,0<volume (B n))
    (ht : ∀E : Set ℝ,IsCompact E → Tendsto
      (fun n => ∫t in E,‖(B n).indicator (fun _ => (1:ℝ)) t-A.indicator (fun _ => (1:ℝ)) t‖) atTop (𝓝 0))
    {b : ℝ} (hb : b∈(volume.restrict A).support) :
    ∃v : ℕ → ℝ,(∀n,v n∈(volume.restrict (B n)).support) ∧ Tendsto v atTop (𝓝 b) := by
  have hne (n : ℕ) : (volume.restrict (B n)).support.Nonempty := by
    apply Measure.nonempty_support
    intro he
    have hz := congrArg (fun μ : Measure ℝ => μ univ) he
    exact (hpB n).ne' (by simpa using hz)
  choose v hv hd using fun n => (volume.restrict (B n)).isClosed_support.exists_infDist_eq_dist (hne n) b
  refine ⟨v,hv,Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (support_lower_semicontinuity hA hB ht hb hε)
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨w,hw,hwb⟩ := hN n hn
  rw [dist_comm,← hd n]
  exact (Metric.infDist_le_dist_of_mem hw).trans_lt (by simpa only [dist_comm] using hwb)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma strict_state_uniform_on_compact {k : ℕ} {c : ℂ → Fin k}
    (hc : Measurable c) (hw : WeakColoring k c)
    (x : ℕ → ℂ) (J K : Finset (Fin k)) (X : Fin k)
    (hlabels : ∀i, i∉J∪K ↔ i=X)
    (A B : ℕ → Set ℝ) (D : Set ℝ) (hD : MeasurableSet D) (hp : 0<volume D)
    (hA : ∀n,RealState hc (x n) (A n) J) (hB : ∀n,RealState hc (x n) (B n) K)
    (hL1 : ∀ E : Set ℝ, IsCompact E →
      Tendsto (fun n => ∫ v in E, ‖(A n).indicator (fun _ => (1:ℝ)) v-D.indicator (fun _ => (1:ℝ)) v‖)
        atTop (𝓝 0))
    {C : Set ℝ} (hC : IsCompact C) :
    ∃ ε>0, ∀ᶠ n in atTop, ∀b∈C, ∀d∈C,
      b∈(volume.restrict (B n)).support → d∈(volume.restrict (B n)).support →
      ε≤|‖direction (b : Angles)-direction (d : Angles)‖-1| := by
  by_contra! hbad
  have hex (N : ℕ) : ∃ n≥N, ∃ b∈C, ∃ d∈C,
      b∈(volume.restrict (B n)).support ∧ d∈(volume.restrict (B n)).support ∧
      |‖direction (b : Angles)-direction (d : Angles)‖-1|<1/(N+1) := by
    have hh := hbad (1/((N:ℝ)+1)) (by positivity)
    simpa only [and_assoc] using (frequently_atTop.mp hh) N
  choose f hf b hb d hd hbs hds hsmall using hex
  have hft : Tendsto f atTop atTop := tendsto_atTop_mono hf tendsto_id
  obtain ⟨q,_hq,φ,hφ,hqt⟩ := (hC.prod hC).isSeqCompact
    (fun n => show (b n,d n)∈C×ˢC from ⟨hb n,hd n⟩)
  have hqb : Tendsto (b∘φ) atTop (𝓝 q.1) := (continuous_fst.tendsto q).comp hqt
  have hqd : Tendsto (d∘φ) atTop (𝓝 q.2) := (continuous_snd.tendsto q).comp hqt
  have hdir : Continuous (fun v : ℝ => direction (v : Angles)) :=
    direction_continuous.comp (AddCircle.continuous_mk' (2*Real.pi))
  have he : ‖direction (q.1 : Angles)-direction (q.2 : Angles)‖=1 := by
    have hn : Tendsto (fun N => |‖direction (b N : Angles)-direction (d N : Angles)‖-1|) atTop (𝓝 0) := by
      exact squeeze_zero (fun _ => abs_nonneg _) (fun N => (hsmall N).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hl := (((hdir.tendsto q.1).comp hqb).sub ((hdir.tendsto q.2).comp hqd)).norm.sub_const 1 |>.abs
    have he := tendsto_nhds_unique hl (hn.comp hφ.tendsto_atTop)
    exact sub_eq_zero.mp (abs_eq_zero.mp he)
  apply strict_state_sequence_false hc hw (fun n => x (f (φ n))) J K X hlabels
    (fun n => A (f (φ n))) (fun n => B (f (φ n))) D hD hp
    (fun n => hA (f (φ n))) (fun n => hB (f (φ n)))
    (b∘φ) (d∘φ) q.1 q.2 hqb hqd (fun n => hbs (φ n)) (fun n => hds (φ n)) he
  intro E hE
  exact (hL1 E hE).comp (hft.comp hφ.tendsto_atTop)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma angle_preimage_positive {A : Set Angles} (hA : MeasurableSet A) (hp : 0<angularMeasure A) :
    0<volume (((↑) : ℝ → Angles) ⁻¹' A) := by
  by_contra! hn
  have hz := measure_eq_zero_iff_ae_notMem.mp (le_antisymm hn zero_le)
  have ha : ∀ᵐt∂angularMeasure,t∉A := ae_angular_of_ae_line hA.compl hz
  exact hp.ne' (measure_eq_zero_iff_ae_notMem.mpr ha)
variable (c : ℂ → Fin 5) (hc : Measurable c)
def fourRealState (x : ℂ) (s : Fin 3) : Set ℝ := {t | fourState c hc x (t : Angles)=s}
def fourSupport (x : ℂ) (s : Fin 3) : Set ℝ := (volume.restrict (fourRealState c hc x s)).support
lemma four_realState_measurable (x : ℂ) (s : Fin 3) : MeasurableSet (fourRealState c hc x s) :=
  (measurableSet_eq_fun (fourState_measurable c hc x) measurable_const).preimage
    angleMk_quasiMeasurePreserving.measurable
lemma four_realState_positive (hw : WeakColoring 5 c) {x : ℂ} (hx : FourCenter c x)
    {s : Fin 3} (hs : s≠0) : 0<volume (fourRealState c hc x s) :=
  angle_preimage_positive (measurableSet_eq_fun (fourState_measurable c hc x) measurable_const)
    (fourState_diagonal_positive c hc hw hx s hs)
lemma four_realState_continuity (hw : WeakColoring 5 c)
    {x : ℕ → ℂ} {y : ℂ} (hx : ∀n,FourCenter c (x n)) (hy : FourCenter c y)
    (hxt : Tendsto x atTop (𝓝 y)) (s : Fin 3) {E : Set ℝ} (hE : IsCompact E) :
    Tendsto (fun n => ∫t in E,‖(fourRealState c hc (x n) s).indicator (fun _ => (1:ℝ)) t-
      (fourRealState c hc y s).indicator (fun _ => (1:ℝ)) t‖) atTop (𝓝 0) := by
  exact angular_compact_L1
    (fun n => (integrable_const (1:ℝ)).indicator (measurableSet_eq_fun (fourState_measurable c hc (x n)) measurable_const))
    ((integrable_const (1:ℝ)).indicator (measurableSet_eq_fun (fourState_measurable c hc y) measurable_const))
    (four_state_continuity c hc hw hx hy hxt s) hE
lemma four_support_continuity (hw : WeakColoring 5 c)
    {x : ℕ → ℂ} {y : ℂ} (hx : ∀n,FourCenter c (x n)) (hy : FourCenter c y)
    (hxt : Tendsto x atTop (𝓝 y)) {s : Fin 3} (hs : s≠0) {b : ℝ}
    (hb : b∈fourSupport c hc y s) :
    ∃v : ℕ → ℝ,(∀n,v n∈fourSupport c hc (x n) s) ∧ Tendsto v atTop (𝓝 b) :=
  support_sequence_continuity (four_realState_measurable c hc y s)
    (fun n => four_realState_measurable c hc (x n) s)
    (fun n => four_realState_positive c hc hw (hx n) hs)
    (fun _ hE => four_realState_continuity c hc hw hx hy hxt s hE) hb
lemma four_support_sequence_no_unit (hw : WeakColoring 5 c)
    {x : ℕ → ℂ} {y : ℂ} (hx : ∀n,FourCenter c (x n)) (hy : FourCenter c y)
    (hxt : Tendsto x atTop (𝓝 y)) {s : Fin 3} (hs : s≠0)
    {b d : ℕ → ℝ} {b₀ d₀ : ℝ} (hb : Tendsto b atTop (𝓝 b₀)) (hd : Tendsto d atTop (𝓝 d₀))
    (hbs : ∀n,b n∈fourSupport c hc (x n) s) (hds : ∀n,d n∈fourSupport c hc (x n) s) :
    ‖direction (b₀ : Angles)-direction (d₀ : Angles)‖≠1 := by
  let r : Fin 3 := if s=1 then 2 else 1
  have hr : r≠0 := by dsimp [r]; split <;> decide
  have hl : ∀i : Fin 5,i∉fourGroup r∪fourGroup s ↔ i=4 := by
    exact (show ∀s : Fin 3,s≠0 → ∀i : Fin 5,i∉fourGroup (if s=1 then 2 else 1)∪fourGroup s ↔ i=4 from by decide) s hs
  intro hu
  exact strict_state_sequence_false hc hw x (fourGroup r) (fourGroup s) 4 hl
    (fun n => fourRealState c hc (x n) r) (fun n => fourRealState c hc (x n) s)
    (fourRealState c hc y r) (four_realState_measurable c hc y r)
    (four_realState_positive c hc hw hy hr)
    (fun n => fourState_represents c hc hw (hx n) r) (fun n => fourState_represents c hc hw (hx n) s)
    b d b₀ d₀ hb hd hbs hds hu (fun _ hE => four_realState_continuity c hc hw hx hy hxt r hE)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal
namespace EuclideanFiveColor
lemma plane_antilipschitz_qmp {F : RealPlane → RealPlane} (hF : Measurable F)
    {V : Set RealPlane} {K : ℝ≥0} (hK : AntilipschitzWith K (V.domRestrict F)) :
    Measure.QuasiMeasurePreserving F (volume.restrict V) volume := by
  refine ⟨hF,?_⟩
  have hh := map_restrict_volume_le hF MeasurableSet.univ hK (mapsTo_univ F V)
  rw [Measure.restrict_univ] at hh
  exact Measure.absolutelyContinuous_of_le_smul hh
lemma support_prod_real {μ ν : Measure ℝ} [SFinite μ] [SFinite ν]
    {a b : ℝ} (ha : a∈μ.support) (hb : b∈ν.support) : (a,b)∈(μ.prod ν).support := by
  apply (Measure.mem_support_iff_forall _).mpr
  intro S hS
  obtain ⟨I,hI,J,hJ,hIJ⟩ := mem_nhds_prod_iff.mp hS
  apply (ENNReal.mul_pos ((Measure.mem_support_iff_forall _).mp ha I hI).ne'
    ((Measure.mem_support_iff_forall _).mp hb J hJ).ne').trans_le
  rw [← Measure.prod_prod]
  exact measure_mono hIJ
lemma continuousAt_maps_support_closed {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] {μ : Measure X} {F : X → Y} {C : Set Y} {p : X}
    (hp : p∈μ.support) (hF : ContinuousAt F p) (hC : IsClosed C)
    (hae : ∀ᵐq∂μ,F q∈C) : F p∈C := by
  by_contra hnot
  have hh : {q | F q∉C}∈𝓝 p := hF (hC.isOpen_compl.mem_nhds hnot)
  exact ((Measure.mem_support_iff_forall _).mp hp _ hh).ne' hae
lemma state_support_transport {k : ℕ} {c : ℂ → Fin k}
    (hc : Measurable c) (hw : WeakColoring k c) {x y : ℂ}
    {A B C : Set ℝ} {J K : Finset (Fin k)} {X : Fin k}
    (hA : RealState hc x A J) (hB : RealState hc x B K) (hC : RealState hc y C {X})
    (hlabels : ∀i,i∉J∪K ↔ i=X)
    {a b : ℝ} (ha : a∈(volume.restrict A).support) (hb : b∈(volume.restrict B).support)
    {F : RealPlane → RealPlane} (hF : Measurable F) (hFc : ContinuousAt F (a,b))
    {V : Set RealPlane} (hV : IsOpen V) (hab : (a,b)∈V) {L : ℝ≥0}
    (hL : AntilipschitzWith L (V.domRestrict F))
    (hi : ∀q∈V,Real.sin (q.2-q.1)≠0)
    (ho : ∀q∈V,Real.sin ((F q).2-(F q).1)≠0)
    (heq : ∀q∈V,angularSum x 1 (angleChart q)=angularSum y 1 (angleChart (F q))) :
    F (a,b)∈(volume.restrict Cᶜ).support ×ˢ (volume.restrict Cᶜ).support := by
  have hdA : ∀ᵐq : RealPlane∂volume,q.1∈A → LineDensityZero Aᶜ q.1 := by
    simpa only [Measure.volume_eq_prod] using
      (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).ae (ae_lineDensityZero_compl hA.1)
  have hdB : ∀ᵐq : RealPlane∂volume,q.2∈B → LineDensityZero Bᶜ q.2 := by
    simpa only [Measure.volume_eq_prod] using
      (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).ae (ae_lineDensityZero_compl hB.1)
  have hdC : ∀ᵐt : ℝ∂volume,t∉(volume.restrict Cᶜ).support → LineDensityZero Cᶜ t := by
    have hs : ∀ᵐt : ℝ∂volume,t∈Cᶜ → t∈(volume.restrict Cᶜ).support := by
      exact (ae_restrict_iff' hC.1.compl).mp (volume.restrict Cᶜ).support_mem_ae
    filter_upwards [hs,ae_lineDensityZero_compl hC.1] with t ht hd hn
    apply hd
    by_contra htC
    exact hn (ht htC)
  have hdpair : ∀ᵐq : RealPlane∂volume,
      (q.1∉(volume.restrict Cᶜ).support → LineDensityZero Cᶜ q.1) ∧
      (q.2∉(volume.restrict Cᶜ).support → LineDensityZero Cᶜ q.2) := by
    have h₁ := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).ae hdC
    have h₂ := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).ae hdC
    simpa only [Measure.volume_eq_prod] using h₁.and h₂
  have hforced : ∀ᵐq∂volume.restrict V,q∈A×ˢB →
      F q∈(volume.restrict Cᶜ).support ×ˢ (volume.restrict Cᶜ).support := by
    filter_upwards [ae_restrict_of_ae hdA,ae_restrict_of_ae hdB,
      (plane_antilipschitz_qmp hF hL).ae hdpair,ae_restrict_mem hV.measurableSet] with q hqa hqb hqc hq hAB
    have hOne : DensityOne {z | c z=X} (angularSum x 1 (angleChart q)) := by
      simpa only [hlabels] using states_densityOne hc hw hA hB (hqa hAB.1) (hqb hAB.2) (hi q hq)
    have hnot (hZero : DensityZero {z | c z=X} (angularSum y 1 (angleChart (F q)))) : False := by
      rw [heq q hq] at hOne
      have hh := tendsto_nhds_unique hOne hZero
      exact one_ne_zero hh
    constructor
    · by_contra hn
      exact hnot (state_densityZero hc hw hC (hqc.1 hn) (ho q hq) (Finset.mem_singleton_self _))
    · by_contra hn
      apply hnot
      rw [← angularSum_swap y (F q).1 (F q).2]
      apply state_densityZero hc hw hC (hqc.2 hn) _ (Finset.mem_singleton_self _)
      simpa only [← neg_sub (F q).2 (F q).1,Real.sin_neg,neg_ne_zero] using ho q hq
  have hp : (a,b)∈(volume.restrict (A×ˢB)).support := by
    rw [Measure.volume_eq_prod,← Measure.prod_restrict]
    exact support_prod_real ha hb
  have hpV : (a,b)∈((volume.restrict (A×ˢB)).restrict V).support :=
    Measure.interior_inter_support ⟨hV.interior_eq.symm ▸ hab,hp⟩
  apply continuousAt_maps_support_closed hpV hFc
    ((volume.restrict Cᶜ).isClosed_support.prod (volume.restrict Cᶜ).isClosed_support)
  filter_upwards [hforced.filter_mono (ae_mono (Measure.restrict_mono_measure Measure.restrict_le_self V)),
    ae_restrict_of_ae (ae_restrict_mem (hA.1.prod hB.1))] with q hq hAB
  exact hq hAB
end EuclideanFiveColor
end

end OAI

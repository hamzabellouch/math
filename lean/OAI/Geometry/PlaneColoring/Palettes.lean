import OAI.Geometry.PlaneColoring.Transitions

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
abbrev Traces (x : ℂ) := {b : TraceVector k // IsTrace c hc x b}
def tracePositive (x : ℂ) (i : Fin k) (b : Traces c hc x) : Set Angles :=
  {t | 0 < traceValue b.1 i t}
lemma tracePositive_measurable (x : ℂ) (i : Fin k) (b : Traces c hc x) :
    MeasurableSet (tracePositive c hc x i b) :=
  measurableSet_lt measurable_const (Lp.stronglyMeasurable _).measurable
def paletteGenerators (x : ℂ) (i : Fin k) : Set (Traces c hc x) :=
  (exists_countable_essential_union angularMeasure (tracePositive c hc x i) (tracePositive_measurable c hc x i)).choose
lemma paletteGenerators_countable (x : ℂ) (i : Fin k) : (paletteGenerators c hc x i).Countable :=
  (exists_countable_essential_union angularMeasure (tracePositive c hc x i) (tracePositive_measurable c hc x i)).choose_spec.1
def paletteSet (x : ℂ) (i : Fin k) : Set Angles :=
  ⋃ b ∈ paletteGenerators c hc x i, tracePositive c hc x i b
lemma paletteSet_measurable (x : ℂ) (i : Fin k) : MeasurableSet (paletteSet c hc x i) :=
  MeasurableSet.biUnion (paletteGenerators_countable c hc x i) (fun b _ => tracePositive_measurable c hc x i b)
lemma tracePositive_le_palette (x : ℂ) (i : Fin k) (b : Traces c hc x) :
    tracePositive c hc x i b ≤ᵐ[angularMeasure] paletteSet c hc x i :=
  (exists_countable_essential_union angularMeasure (tracePositive c hc x i) (tracePositive_measurable c hc x i)).choose_spec.2 b
lemma paletteSet_minimal (x : ℂ) (i : Fin k) {A : Set Angles}
    (hA : ∀ b : Traces c hc x, tracePositive c hc x i b ≤ᵐ[angularMeasure] A) :
    paletteSet c hc x i ≤ᵐ[angularMeasure] A := by
  have hh : ∀ᵐ t ∂angularMeasure, ∀ b ∈ paletteGenerators c hc x i, t ∈ tracePositive c hc x i b → t ∈ A :=
    (ae_ball_iff (paletteGenerators_countable c hc x i)).mpr (fun b _ => hA b)
  filter_upwards [hh] with t ht
  intro hm
  rcases Set.mem_iUnion₂.mp hm with ⟨b,hb,hbt⟩
  exact ht b hb hbt
def palette (x : ℂ) (t : Angles) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter (fun i => t ∈ paletteSet c hc x i)
@[simp] lemma mem_palette (x : ℂ) (t : Angles) (i : Fin k) :
    i ∈ palette c hc x t ↔ t ∈ paletteSet c hc x i := by simp [palette]
lemma palette_nonempty (x : ℂ) : ∀ᵐ t ∂angularMeasure, (palette c hc x t).Nonempty := by
  obtain ⟨b,hb⟩ := exists_trace c hc x
  let B : Traces c hc x := ⟨b,hb⟩
  have hsum := (trace_bounds c hc hb).2.2
  have hs : (fun t => ∑ i, traceValue b i t) =ᵐ[angularMeasure] (fun _ => (1 : ℝ)) := by
    have hh := Lp.coeFn_fun_finsetSum Finset.univ (traceValue b)
    rw [hsum] at hh
    exact hh.symm.trans (oneL2_ae angularMeasure)
  filter_upwards [hs,ae_all_iff.mpr (fun i => tracePositive_le_palette c hc x i B)] with t ht hP
  have he : ∃ i : Fin k, 0 < traceValue b i t := by
    by_contra! hh
    have hz : (∑ i, traceValue b i t) ≤ 0 := Finset.sum_nonpos (fun i _ => hh i)
    linarith
  obtain ⟨i,hi⟩ := he
  exact ⟨i,(mem_palette c hc x t i).mpr ((hP i) hi)⟩
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma inner_oneL2_integral (f : RealL2 angularMeasure) :
    ⟪f,oneL2 angularMeasure⟫ = ∫ t, f t ∂angularMeasure := by
  rw [real_inner_comm]
  exact (L2.inner_indicatorConstLp_one MeasurableSet.univ (measure_ne_top angularMeasure Set.univ) f).trans
    (by simp)
lemma sample_inner_one (i : Fin k) (q : ℂ) :
    ⟪sample c hc q 1 i,oneL2 angularMeasure⟫ = colorMass c i q := by
  rw [inner_oneL2_integral]
  exact integral_congr_ae (sample_ae c hc q 1 i)
lemma transition_avoiding_trace (hw : WeakColoring k c) {i j : Fin k} {x : ℂ}
    (he : TransitionEdge c i j x) :
    ∃ b : TraceVector k, IsTrace c hc x b ∧ traceValue b i=0 ∧ traceValue b j=0 := by
  obtain ⟨q,hq⟩ := Classical.axiomOfChoice (fun n : ℕ => transition_small_mass c hc hw he
    (R := 1/((n:ℝ)+1)) (ε := 1/((n:ℝ)+1)) (by positivity) (by positivity))
  have hqt : Tendsto q atTop (𝓝 x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (fun n => dist_nonneg)
      (fun n => (hq n).1.le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨b,_,φ,hφ,hb⟩ := (isCompact_univ : IsCompact (Set.univ : Set (TraceVector k))).isSeqCompact.subseq_of_frequently_in
    (Eventually.frequently (Eventually.of_forall fun n => Set.mem_univ (sampleCode c hc (q n) 1)))
  have htrace : IsTrace c hc x b := trace_of_realization c hc
    (fun n => (hq (φ n)).2.1) (hqt.comp hφ.tendsto_atTop) tendsto_const_nhds hb
  have hmass (a : Fin k) (ha : a=i ∨ a=j) : ∫ t, traceValue b a t ∂angularMeasure = 0 := by
    have ht := (traceCode_tendsto_iff.mp hb) a (oneL2 angularMeasure)
    simp only [Function.comp_apply,traceValue_sampleCode,sample_inner_one] at ht
    rw [inner_oneL2_integral] at ht
    have ht' : Tendsto (fun n => colorMass c a (q n)) atTop (𝓝 0) := by
      apply squeeze_zero (fun n => colorMass_nonneg c a (q n)) (fun n => ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      rcases ha with rfl | rfl
      · exact (le_add_of_nonneg_right (colorMass_nonneg c j (q n))).trans (hq n).2.2.le
      · exact (le_add_of_nonneg_left (colorMass_nonneg c i (q n))).trans (hq n).2.2.le
    exact tendsto_nhds_unique ht (ht'.comp hφ.tendsto_atTop)
  have hzero (a : Fin k) (ha : a=i ∨ a=j) : traceValue b a=0 := by
    apply Lp.ext
    have hi : Integrable (traceValue b a) angularMeasure := (Lp.memLp _).integrable (by norm_num)
    have hz := (integral_eq_zero_iff_of_nonneg_ae ((trace_bounds c hc htrace).1 a) hi).mp (hmass a ha)
    exact hz.trans (Lp.coeFn_zero ℝ 2 angularMeasure).symm
  exact ⟨b,htrace,hzero i (Or.inl rfl),hzero j (Or.inr rfl)⟩
lemma edge_palette_not_pair (hw : WeakColoring k c) {i j : Fin k} {x : ℂ}
    (he : TransitionEdge c i j x) : ∀ᵐ t ∂angularMeasure, ¬ palette c hc x t ⊆ {i,j} := by
  obtain ⟨b,hb,hi,hj⟩ := transition_avoiding_trace c hc hw he
  have hs : (fun t => ∑ a, traceValue b a t) =ᵐ[angularMeasure] (fun _ => (1 : ℝ)) := by
    have hh := Lp.coeFn_fun_finsetSum Finset.univ (traceValue b)
    rw [(trace_bounds c hc hb).2.2] at hh
    exact hh.symm.trans (oneL2_ae angularMeasure)
  have hzi : traceValue b i =ᵐ[angularMeasure] (fun _ => (0:ℝ)) := by rw [hi]; exact Lp.coeFn_zero _ _ _
  have hzj : traceValue b j =ᵐ[angularMeasure] (fun _ => (0:ℝ)) := by rw [hj]; exact Lp.coeFn_zero _ _ _
  filter_upwards [hs,hzi,hzj,ae_all_iff.mpr (fun a => tracePositive_le_palette c hc x a ⟨b,hb⟩)] with t ht hi0 hj0 hp hsub
  have hnon : ∀ a : Fin k, traceValue b a t ≤ 0 := by
    intro a
    by_contra! ha
    have ham := hsub ((mem_palette c hc x t a).mpr (hp a ha))
    simp only [Finset.mem_insert,Finset.mem_singleton] at ham
    rcases ham with rfl | rfl <;> linarith
  have hh := Finset.sum_nonpos (s := Finset.univ) (fun a _ => hnon a)
  linarith
end EuclideanFiveColor
end

end OAI

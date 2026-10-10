import OAI.Probability.DirectionalWalk.RegenerativeTapes

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

noncomputable def runningMax {Ω : Type*} (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (n+1)).sup' Finset.nonempty_range_add_one (fun i => f i ω)

lemma runningMax_nonneg {Ω : Type*} (f : ℕ → Ω → ℝ) (hf : ∀ n ω, 0 ≤ f n ω)
    (n : ℕ) (ω : Ω) : 0 ≤ runningMax f n ω := by
  exact (hf 0 ω).trans (Finset.le_sup' (fun i => f i ω) (Finset.mem_range.mpr (Nat.succ_pos _)))

lemma runningMax_le {Ω : Type*} (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (B : ℝ)
    (hf : ∀ i ≤ n, f i ω ≤ B) : runningMax f n ω ≤ B := by
  exact Finset.sup'_le _ _ (fun i hi => hf i (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hi))

lemma measurable_runningMax {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → ℝ)
    (hf : ∀ i, Measurable (f i)) (n : ℕ) : Measurable (runningMax f n) :=
  Finset.measurable_range_sup'' (fun i _ => hf i)

lemma dyadic_cover (x : ℝ) (hx : x ≤ 1) (L : ℕ) :
    x ≤ (1/2 : ℝ)^L + ∑ j ∈ Finset.range L, if (1/2 : ℝ)^(j+1) ≤ x then (1/2 : ℝ)^(j+1) else 0 := by
  induction L with
  | zero => simpa using hx
  | succ L ih =>
    rw [Finset.sum_range_succ]
    by_cases h : (1/2 : ℝ)^(L+1) ≤ x
    · rw [ite_eq_left h]
      have hh : (1/2 : ℝ)^(L+1) + (1/2 : ℝ)^(L+1) = (1/2 : ℝ)^L := by rw [pow_succ]; ring
      linarith
    · rw [ite_eq_right h,add_zero]
      exact (le_of_lt (lt_of_not_ge h)).trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => by positivity)))

lemma martingale_maximal_real {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (f : ℕ → Ω → ℝ) (hf : Martingale f ℱ μ)
    (hpos : ∀ i ω, 0 ≤ f i ω) (n : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    a * μ.real {ω | a ≤ runningMax f n ω} ≤ ∫ ω, f 0 ω ∂μ := by
  have hc := maximal_ineq hf.submartingale hpos (ε := ⟨a,ha⟩) n
  have hle : (∫ ω in {ω | a ≤ runningMax f n ω}, f n ω ∂μ) ≤ ∫ ω, f n ω ∂μ :=
    setIntegral_le_integral (hf.integrable n) (Filter.Eventually.of_forall (hpos n))
  have hnon : 0 ≤ ∫ ω in {ω | a ≤ runningMax f n ω}, f n ω ∂μ := integral_nonneg (hpos n)
  have hh := ENNReal.toReal_mono (ENNReal.ofReal_ne_top : ENNReal.ofReal
    (∫ ω in {ω | a ≤ runningMax f n ω}, f n ω ∂μ) ≠ ⊤) hc
  have he := hf.setIntegral_eq (Nat.zero_le n) (s := Set.univ) MeasurableSet.univ
  simp only [setIntegral_univ] at he
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hnon] at hh
  exact hh.trans (hle.trans_eq he.symm)

lemma integrable_runningMax {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : ℕ → Ω → ℝ) (hf : ∀ i, Measurable (f i)) (hpos : ∀ i ω, 0 ≤ f i ω)
    (hle : ∀ i ω, f i ω ≤ 1) (n : ℕ) : Integrable (runningMax f n) μ := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_runningMax f hf n).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg (runningMax_nonneg f hpos n ω)]
    exact runningMax_le f n ω 1 (fun i _ => hle i ω))

lemma integral_runningMax_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (f : ℕ → Ω → ℝ) (hf : Martingale f ℱ μ)
    (hpos : ∀ i ω, 0 ≤ f i ω) (hle : ∀ i ω, f i ω ≤ 1)
    (E : Set Ω) (hE : MeasurableSet E) (hzero : ∀ i ω, ω ∉ E → f i ω = 0)
    (n L : ℕ) :
    (∫ ω, runningMax f n ω ∂μ) ≤ (1/2 : ℝ)^L * μ.real E + L * ∫ ω, f 0 ω ∂μ := by
  classical
  let A (j : ℕ) : Set Ω := {ω | (1/2 : ℝ)^(j+1) ≤ runningMax f n ω}
  have hfm (i : ℕ) : Measurable (f i) := (hf.stronglyMeasurable i).measurable.mono (ℱ.le i) le_rfl
  have hA (j : ℕ) : MeasurableSet (A j) := measurableSet_le measurable_const (measurable_runningMax f hfm n)
  have hI (j : ℕ) : Integrable ((A j).indicator (fun _ => (1/2 : ℝ)^(j+1))) μ :=
    (integrable_const _).indicator (hA j)
  have hB : Integrable (E.indicator (fun _ => (1/2 : ℝ)^L)) μ := (integrable_const _).indicator hE
  have hCv := integral_mono (integrable_runningMax μ f hfm hpos hle n)
    (hB.add (integrable_finsetSum _ (fun j _ => hI j)))
    (show ∀ ω, runningMax f n ω ≤ E.indicator (fun _ => (1/2 : ℝ)^L) ω +
      ∑ j ∈ Finset.range L, (A j).indicator (fun _ => (1/2 : ℝ)^(j+1)) ω from by
      intro ω
      by_cases hω : ω ∈ E
      · simp only [Set.indicator_of_mem hω]
        simpa only [Set.indicator_apply,Set.mem_ofPred_eq,A] using dyadic_cover
          (runningMax f n ω) (runningMax_le f n ω 1 (fun i _ => hle i ω)) L
      · have hz : runningMax f n ω = 0 := le_antisymm
          (runningMax_le f n ω 0 (fun i _ => le_of_eq (hzero i ω hω))) (runningMax_nonneg f hpos n ω)
        rw [hz,Set.indicator_of_notMem hω,zero_add]
        exact Finset.sum_nonneg (fun j _ => Set.indicator_nonneg (fun _ _ => by positivity) _))
  simp only [Pi.add_apply] at hCv
  rw [integral_add hB (integrable_finsetSum _ (fun j _ => hI j)),integral_finsetSum _ (fun j _ => hI j),
    integral_indicator_const _ hE,smul_eq_mul,mul_comm (μ.real E)] at hCv
  refine hCv.trans (add_le_add le_rfl ?_)
  calc
    (∑ j ∈ Finset.range L, ∫ ω, (A j).indicator (fun _ => (1/2 : ℝ)^(j+1)) ω ∂μ) ≤
        ∑ _j ∈ Finset.range L, ∫ ω, f 0 ω ∂μ := by
      apply Finset.sum_le_sum
      intro j _
      rw [integral_indicator_const _ (hA j),smul_eq_mul,mul_comm]
      exact martingale_maximal_real μ ℱ f hf hpos n _ (by positivity)
    _ = L * ∫ ω, f 0 ω ∂μ := by simp

noncomputable def posteriorMax {Ω ι : Type*} [Fintype ι] (w : ι → ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : ℝ := ∑ e, runningMax (w e) n ω

lemma posterior_coord_le_one {Ω ι : Type*} [Fintype ι] (w : ι → ℕ → Ω → ℝ)
    (hpos : ∀ e i ω, 0 ≤ w e i ω) (hsum : ∀ i ω, ∑ e, w e i ω ≤ 1)
    (e : ι) (i : ℕ) (ω : Ω) : w e i ω ≤ 1 := by
  classical
  exact (Finset.single_le_sum (fun e _ => hpos e i ω) (Finset.mem_univ e)).trans (hsum i ω)

lemma integral_posteriorMax_bound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (w : ι → ℕ → Ω → ℝ) (hw : ∀ e, Martingale (w e) ℱ μ)
    (hpos : ∀ e i ω, 0 ≤ w e i ω) (hsum : ∀ i ω, ∑ e, w e i ω ≤ 1)
    (E : Set Ω) (hE : MeasurableSet E) (hzero : ∀ e i ω, ω ∉ E → w e i ω = 0)
    (n L : ℕ) :
    (∫ ω, posteriorMax w n ω ∂μ) ≤ ((Fintype.card ι : ℝ) * (1/2 : ℝ)^L + L) * μ.real E := by
  classical
  have hfm (e : ι) (i : ℕ) : Measurable (w e i) :=
    ((hw e).stronglyMeasurable i).measurable.mono (ℱ.le i) le_rfl
  have hInt (e : ι) := integrable_runningMax μ (w e) (hfm e) (hpos e) (posterior_coord_le_one w hpos hsum e) n
  have hs : (∑ e, ∫ ω, w e 0 ω ∂μ) ≤ μ.real E := by
    rw [← integral_finsetSum _ (fun e _ => (hw e).integrable 0)]
    have hi := integral_mono (integrable_finsetSum _ (fun e _ => (hw e).integrable 0))
      ((integrable_const (1 : ℝ)).indicator hE) (show ∀ ω, (∑ e, w e 0 ω) ≤ E.indicator (fun _ => (1 : ℝ)) ω from by
        intro ω
        by_cases hω : ω ∈ E
        · simpa only [Set.indicator_of_mem hω] using hsum 0 ω
        · simp [Set.indicator_of_notMem hω,hzero _ _ _ hω])
    simpa only [integral_indicator_const _ hE,smul_eq_mul,mul_one] using hi
  calc
    (∫ ω, posteriorMax w n ω ∂μ) = ∑ e, ∫ ω, runningMax (w e) n ω ∂μ :=
      integral_finsetSum _ (fun e _ => hInt e)
    _ ≤ ∑ e, ((1/2 : ℝ)^L * μ.real E + L * ∫ ω, w e 0 ω ∂μ) :=
      Finset.sum_le_sum (fun e _ => integral_runningMax_bound μ ℱ (w e) (hw e) (hpos e)
        (posterior_coord_le_one w hpos hsum e) E hE (hzero e) n L)
    _ = (Fintype.card ι : ℝ) * (1/2 : ℝ)^L * μ.real E + L * ∑ e, ∫ ω, w e 0 ω ∂μ := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum]
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      rw [← Finset.mul_sum]
      ring
    _ ≤ (Fintype.card ι : ℝ) * (1/2 : ℝ)^L * μ.real E + L * μ.real E :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _))
    _ = _ := by ring

noncomputable def shiftedFiltration {Ω : Type*} [m : MeasurableSpace Ω]
    (ℱ : Filtration ℕ m) (s : ℕ) : Filtration ℕ m where
  seq i := ℱ (s+i)
  mono' _i _j hij := ℱ.mono (Nat.add_le_add_left hij s)
  le' i := ℱ.le (s+i)

lemma martingale_shift_indicator {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ m)
    (f : ℕ → Ω → ℝ) (hf : Martingale f ℱ μ) (s : ℕ)
    (E : Set Ω) (hE : MeasurableSet[ℱ s] E) :
    Martingale (fun i => E.indicator (f (s+i))) (shiftedFiltration ℱ s) μ := by
  have hE' (i : ℕ) : MeasurableSet[ℱ (s+i)] E := ℱ.mono (Nat.le_add_right s i) E hE
  refine ⟨fun i => (hf.stronglyMeasurable (s+i)).indicator (hE' i),fun i j hij => ?_⟩
  refine (condExp_indicator (hf.integrable (s+j)) (hE' i)).trans ?_
  filter_upwards [hf.condExp_ae_eq (Nat.add_le_add_left hij s)] with ω hω
  by_cases h : ω ∈ E
  · simp only [Set.indicator_of_mem h,hω]
  · simp only [Set.indicator_of_notMem h]

lemma runningMax_future_bound {Ω : Type*} (f : ℕ → Ω → ℝ) (hpos : ∀ i ω, 0 ≤ f i ω)
    (n N : ℕ) (ω : Ω) :
    runningMax f N ω - runningMax f n ω ≤ runningMax (fun i => f (n+i)) N ω := by
  apply sub_le_iff_le_add.mpr
  apply runningMax_le
  intro i hi
  by_cases hin : i ≤ n
  · exact (Finset.le_sup' (fun j => f j ω) (Finset.mem_range.mpr (by omega))).trans
      (le_add_of_nonneg_left (runningMax_nonneg (fun j => f (n+j)) (fun j => hpos (n+j)) N ω))
  · have hi' : i-n < N+1 := by omega
    have hh := Finset.le_sup' (fun j => f (n+j) ω) (Finset.mem_range.mpr hi')
    have he : n+(i-n) = i := by omega
    rw [he] at hh
    exact hh.trans (le_add_of_nonneg_right (runningMax_nonneg f hpos n ω))

lemma posterior_future_energy {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (w : ι → ℕ → Ω → ℝ) (hw : ∀ e, Martingale (w e) ℱ μ)
    (hpos : ∀ e i ω, 0 ≤ w e i ω) (hsum : ∀ i ω, ∑ e, w e i ω ≤ 1)
    (L : ℕ) (hL : (Fintype.card ι : ℝ) * (1/2 : ℝ)^L ≤ 1)
    (n N : ℕ) (E : Set Ω) (hE : MeasurableSet[ℱ n] E) :
    (∫ ω in E, (posteriorMax w N ω - posteriorMax w n ω) ∂μ) ≤ (L+1 : ℝ) * μ.real E := by
  classical
  let g : ι → ℕ → Ω → ℝ := fun e i => E.indicator (w e (n+i))
  have hg (e : ι) := martingale_shift_indicator μ ℱ (w e) (hw e) n E hE
  have hgp (e : ι) (i : ℕ) (ω : Ω) : 0 ≤ g e i ω :=
    Set.indicator_nonneg (fun ω _ => hpos e (n+i) ω) ω
  have hgs (i : ℕ) (ω : Ω) : ∑ e, g e i ω ≤ 1 := by
    by_cases hω : ω ∈ E
    · simpa only [g,Set.indicator_of_mem hω] using hsum (n+i) ω
    · simp only [g,Set.indicator_of_notMem hω,Finset.sum_const_zero]; norm_num
  have hgz (e : ι) (i : ℕ) (ω : Ω) (hω : ω ∉ E) : g e i ω = 0 := Set.indicator_of_notMem hω _
  have hE0 := ℱ.le n E hE
  have hb := integral_posteriorMax_bound μ (shiftedFiltration ℱ n) g hg hgp hgs E hE0 hgz N L
  have hfm (e : ι) (i : ℕ) : Measurable (w e i) := ((hw e).stronglyMeasurable i).measurable.mono (ℱ.le i) le_rfl
  have hpm (i : ℕ) : Integrable (posteriorMax w i) μ :=
    integrable_finsetSum _ (fun e _ => integrable_runningMax μ (w e) (hfm e) (hpos e)
      (posterior_coord_le_one w hpos hsum e) i)
  have hgfm (e : ι) (i : ℕ) : Measurable (g e i) :=
    ((hg e).stronglyMeasurable i).measurable.mono ((shiftedFiltration ℱ n).le i) le_rfl
  have hpg : Integrable (posteriorMax g N) μ := integrable_finsetSum _ (fun e _ =>
    integrable_runningMax μ (g e) (hgfm e) (hgp e) (posterior_coord_le_one g hgp hgs e) N)
  have hi := integral_mono (((hpm N).sub (hpm n)).indicator hE0) hpg
    (show ∀ ω, E.indicator (fun ω => posteriorMax w N ω - posteriorMax w n ω) ω ≤ posteriorMax g N ω from by
      intro ω
      by_cases hω : ω ∈ E
      · rw [Set.indicator_of_mem hω]
        simp only [posteriorMax,← Finset.sum_sub_distrib]
        apply Finset.sum_le_sum
        intro e _

        have hr : runningMax (g e) N ω = runningMax (fun i => w e (n+i)) N ω := by
          unfold runningMax
          congr 1
          funext i
          exact Set.indicator_of_mem hω _
        rw [hr]
        exact runningMax_future_bound (w e) (hpos e) n N ω
      · rw [Set.indicator_of_notMem hω]
        exact Finset.sum_nonneg (fun e _ => runningMax_nonneg (g e) (hgp e) N ω))
  rw [integral_indicator hE0] at hi
  exact hi.trans (hb.trans (mul_le_mul_of_nonneg_right (by linarith : (Fintype.card ι : ℝ) * (1/2 : ℝ)^L + L ≤ L+1) measureReal_nonneg))

def crossingEvent {Ω : Type*} (A : ℕ → Ω → ℝ) (x : ℝ) (i : ℕ) : Set Ω :=
  {ω | x < A i ω ∧ ∀ j < i, A j ω ≤ x}

lemma crossingEvent_measurable {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℕ m)
    (A : ℕ → Ω → ℝ) (hA : ∀ i, Measurable[ℱ i] (A i)) (x : ℝ) (i : ℕ) :
    MeasurableSet[ℱ i] (crossingEvent A x i) := by
  apply MeasurableSet.inter (measurableSet_lt measurable_const (hA i))
  change MeasurableSet[ℱ i] {ω | ∀ j < i, A j ω ≤ x}
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun hj =>
    measurableSet_le ((hA j).mono (ℱ.mono (Nat.le_of_lt hj)) le_rfl) measurable_const))

lemma crossingEvent_disjoint {Ω : Type*} (A : ℕ → Ω → ℝ) (x : ℝ) :
    Pairwise (fun i j => Disjoint (crossingEvent A x i) (crossingEvent A x j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro ω ⟨hi,hi'⟩ ⟨hj,hj'⟩
  rcases lt_or_gt_of_ne hij with h | h
  · exact (not_lt_of_ge (hj' i h)) hi
  · exact (not_lt_of_ge (hi' j h)) hj

lemma union_crossingEvent {Ω : Type*} (A : ℕ → Ω → ℝ) (hmono : ∀ ω, Monotone (fun i => A i ω))
    (x : ℝ) (N : ℕ) : (⋃ i ∈ Finset.range (N+1), crossingEvent A x i) = {ω | x < A N ω} := by
  ext ω
  simp only [Set.mem_iUnion,Finset.mem_range,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i,hi,hai⟩
    exact hai.1.trans_le (hmono ω (by omega))
  · intro hN
    have he : ∃ i, x < A i ω := ⟨N,hN⟩
    refine ⟨Nat.find he,by have h := Nat.find_min' he hN; omega,Nat.find_spec he,?_⟩
    intro j hj
    exact le_of_not_gt (Nat.find_min he hj)

lemma crossingEvent_overshoot {Ω : Type*} (A : ℕ → Ω → ℝ)
    (h0 : ∀ ω, A 0 ω ≤ 1) (hj : ∀ i ω, A (i+1) ω ≤ A i ω + 1)
    (x : ℝ) (hx : 1 ≤ x) (i : ℕ) (ω : Ω) (hω : ω ∈ crossingEvent A x i) :
    A i ω ≤ x+1 := by
  cases i with
  | zero => exact ((hω.1.not_ge ((h0 ω).trans hx))).elim
  | succ i => exact (hj i ω).trans (add_le_add (hω.2 i (Nat.lt_succ_self i)) le_rfl)

lemma increasing_energy_tail_step {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ m)
    (A : ℕ → Ω → ℝ) (hA : ∀ i, Measurable[ℱ i] (A i)) (hI : ∀ i, Integrable (A i) μ)
    (hmono : ∀ ω, Monotone (fun i => A i ω)) (h0 : ∀ ω, A 0 ω ≤ 1)
    (hj : ∀ i ω, A (i+1) ω ≤ A i ω + 1) (C : ℝ) (hC : 0 < C)
    (henergy : ∀ i N E, MeasurableSet[ℱ i] E →
      (∫ ω in E, (A N ω - A i ω) ∂μ) ≤ C * μ.real E)
    (N : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    μ.real {ω | x+(2*C+1) < A N ω} ≤ (1/2 : ℝ) * μ.real {ω | x < A N ω} := by
  classical
  let V : Set Ω := {ω | x+(2*C+1) < A N ω}
  have hV : MeasurableSet V := measurableSet_lt measurable_const ((hA N).mono (ℱ.le N) le_rfl)
  have hEm (i : ℕ) := crossingEvent_measurable ℱ A hA x i
  have hEm0 (i : ℕ) : MeasurableSet (crossingEvent A x i) := ℱ.le i _ (hEm i)
  have hEi (i : ℕ) (hi : i ∈ Finset.range (N+1)) :
      μ.real (crossingEvent A x i ∩ V) ≤ (1/2 : ℝ) * μ.real (crossingEvent A x i) := by
    have hiN : i ≤ N := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hi
    have hbound := integral_mono ((integrable_const (2*C)).indicator ((hEm0 i).inter hV))
      (((hI N).sub (hI i)).indicator (hEm0 i))
      (show ∀ ω, (crossingEvent A x i ∩ V).indicator (fun _ => 2*C) ω ≤
          (crossingEvent A x i).indicator (fun ω => A N ω - A i ω) ω from by
        intro ω
        by_cases hω : ω ∈ crossingEvent A x i
        · rw [Set.indicator_of_mem hω]
          by_cases hωV : ω ∈ V
          · rw [Set.indicator_of_mem (show ω ∈ crossingEvent A x i ∩ V from ⟨hω,hωV⟩)]
            have hov := crossingEvent_overshoot A h0 hj x hx i ω hω
            change x+(2*C+1) < A N ω at hωV
            linarith
          · rw [Set.indicator_of_notMem (show ω ∉ crossingEvent A x i ∩ V from fun h => hωV h.2)]
            exact sub_nonneg.mpr (hmono ω hiN)
        · rw [Set.indicator_of_notMem hω,Set.indicator_of_notMem
            (show ω ∉ crossingEvent A x i ∩ V from fun h => hω h.1)])
    rw [integral_indicator_const _ ((hEm0 i).inter hV),smul_eq_mul,
      integral_indicator (hEm0 i)] at hbound
    have he := hbound.trans (henergy i N _ (hEm i))
    nlinarith
  have hsub : V ⊆ {ω | x < A N ω} := by intro ω hω; change x+(2*C+1) < A N ω at hω; dsimp; linarith
  have heV : V = ⋃ i ∈ Finset.range (N+1), crossingEvent A x i ∩ V := by
    ext ω
    simp only [Set.mem_iUnion,Set.mem_inter_iff]
    constructor
    · intro hω
      have hm : ω ∈ ⋃ i ∈ Finset.range (N+1), crossingEvent A x i := by
        rw [union_crossingEvent A hmono x N]
        exact hsub hω
      obtain ⟨i,hi,hh⟩ := Set.mem_iUnion₂.mp hm
      exact ⟨i,hi,hh,hω⟩
    · rintro ⟨i,hi,hh,hω⟩
      exact hω
  have hd : (↑(Finset.range (N+1)) : Set ℕ).PairwiseDisjoint (crossingEvent A x) :=
    fun _ _ _ _ hij => crossingEvent_disjoint A x hij
  calc
    μ.real V = ∑ i ∈ Finset.range (N+1), μ.real (crossingEvent A x i ∩ V) := by
      calc
        μ.real V = μ.real (⋃ i ∈ Finset.range (N+1), crossingEvent A x i ∩ V) := congrArg μ.real heV
        _ = _ := measureReal_biUnion_finset (μ := μ)
          (fun _ hi _ hj hij => (hd hi hj hij).mono inf_le_left inf_le_left)
          (fun i _ => (hEm0 i).inter hV) (fun i _ => measure_ne_top μ _)
    _ ≤ ∑ i ∈ Finset.range (N+1), (1/2 : ℝ) * μ.real (crossingEvent A x i) := Finset.sum_le_sum hEi
    _ = (1/2 : ℝ) * μ.real {ω | x < A N ω} := by
      rw [← Finset.mul_sum,← measureReal_biUnion_finset (μ := μ) hd (fun i _ => hEm0 i),union_crossingEvent A hmono]

lemma increasing_energy_geometric_tail {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m)
    (A : ℕ → Ω → ℝ) (hA : ∀ i, Measurable[ℱ i] (A i)) (hI : ∀ i, Integrable (A i) μ)
    (hmono : ∀ ω, Monotone (fun i => A i ω)) (h0 : ∀ ω, A 0 ω ≤ 1)
    (hj : ∀ i ω, A (i+1) ω ≤ A i ω + 1) (C : ℝ) (hC : 0 < C)
    (henergy : ∀ i N E, MeasurableSet[ℱ i] E →
      (∫ ω in E, (A N ω - A i ω) ∂μ) ≤ C * μ.real E)
    (N k : ℕ) : μ.real {ω | 1+k*(2*C+1) < A N ω} ≤ (1/2 : ℝ)^k := by
  induction k with
  | zero => simpa only [Nat.cast_zero,zero_mul,add_zero,pow_zero] using measureReal_le_one (μ := μ) (s := {ω | 1 < A N ω})
  | succ k ih =>
    have hEq : (1 + (k+1 : ℕ)*(2*C+1) : ℝ) = 1 + k*(2*C+1) + (2*C+1) := by push_cast; ring
    rw [hEq]
    have ht := increasing_energy_tail_step μ ℱ A hA hI hmono h0 hj C hC henergy N
      (1+k*(2*C+1)) (by
        have h : 0 ≤ (k : ℝ)*(2*C+1) := by positivity
        linarith)
    exact ht.trans (by rw [pow_succ]; nlinarith)

lemma runningMax_mono {Ω : Type*} (f : ℕ → Ω → ℝ) (ω : Ω) : Monotone (fun n => runningMax f n ω) := by
  intro n N hnN
  apply runningMax_le
  intro i hi
  exact Finset.le_sup' (fun j => f j ω) (Finset.mem_range.mpr (by omega))

lemma runningMax_step {Ω : Type*} (f : ℕ → Ω → ℝ) (hpos : ∀ i ω, 0 ≤ f i ω)
    (n : ℕ) (ω : Ω) : runningMax f (n+1) ω ≤ runningMax f n ω + f (n+1) ω := by
  apply runningMax_le
  intro i hi
  by_cases hin : i ≤ n
  · have hh := Finset.le_sup' (fun j => f j ω) (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hin))
    exact hh.trans (le_add_of_nonneg_right (hpos (n+1) ω))
  · have he : i = n+1 := by omega
    rw [he]
    exact le_add_of_nonneg_left (runningMax_nonneg f hpos n ω)

lemma posteriorMax_mono {Ω ι : Type*} [Fintype ι] (w : ι → ℕ → Ω → ℝ) (ω : Ω) :
    Monotone (fun n => posteriorMax w n ω) := by
  intro n N hnN
  exact Finset.sum_le_sum (fun e _ => runningMax_mono (w e) ω hnN)

lemma posteriorMax_step {Ω ι : Type*} [Fintype ι] (w : ι → ℕ → Ω → ℝ)
    (hpos : ∀ e i ω, 0 ≤ w e i ω) (hsum : ∀ i ω, ∑ e, w e i ω ≤ 1) (n : ℕ) (ω : Ω) :
    posteriorMax w (n+1) ω ≤ posteriorMax w n ω + 1 := by
  calc
    _ ≤ ∑ e, (runningMax (w e) n ω + w e (n+1) ω) :=
      Finset.sum_le_sum (fun e _ => runningMax_step (w e) (hpos e) n ω)
    _ = posteriorMax w n ω + ∑ e, w e (n+1) ω := Finset.sum_add_distrib
    _ ≤ _ := add_le_add le_rfl (hsum (n+1) ω)

lemma posteriorMax_adapted {Ω ι : Type*} [m : MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (ℱ : Filtration ℕ m) (w : ι → ℕ → Ω → ℝ)
    (hw : ∀ e, Martingale (w e) ℱ μ) (n : ℕ) : Measurable[ℱ n] (posteriorMax w n) := by
  let : MeasurableSpace Ω := ℱ n
  apply Finset.measurable_sum
  intro e _
  exact Finset.measurable_range_sup'' (fun i hi =>
    ((hw e).stronglyMeasurable i).measurable.mono (ℱ.mono hi) le_rfl)

lemma posteriorMax_integrable {Ω ι : Type*} [m : MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ m) (w : ι → ℕ → Ω → ℝ)
    (hw : ∀ e, Martingale (w e) ℱ μ) (hpos : ∀ e i ω, 0 ≤ w e i ω)
    (hsum : ∀ i ω, ∑ e, w e i ω ≤ 1) (n : ℕ) : Integrable (posteriorMax w n) μ := by
  apply integrable_finsetSum
  intro e _
  exact integrable_runningMax μ (w e)
    (fun i => ((hw e).stronglyMeasurable i).measurable.mono (ℱ.le i) le_rfl)
    (hpos e) (posterior_coord_le_one w hpos hsum e) n

lemma posteriorMax_geometric_tail {Ω ι : Type*} [m : MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m)
    (w : ι → ℕ → Ω → ℝ) (hw : ∀ e, Martingale (w e) ℱ μ)
    (hpos : ∀ e i ω, 0 ≤ w e i ω) (hsum : ∀ i ω, ∑ e, w e i ω ≤ 1)
    (L : ℕ) (hL : (Fintype.card ι : ℝ) * (1/2 : ℝ)^L ≤ 1) (N k : ℕ) :
    μ.real {ω | 1+k*(2*(L+1)+1) < posteriorMax w N ω} ≤ (1/2 : ℝ)^k := by
  apply increasing_energy_geometric_tail μ ℱ (posteriorMax w)
    (posteriorMax_adapted μ ℱ w hw) (posteriorMax_integrable μ ℱ w hw hpos hsum)
    (posteriorMax_mono w) _ (posteriorMax_step w hpos hsum) (L+1) (by positivity)
    (posterior_future_energy μ ℱ w hw hpos hsum L hL) N k
  intro ω
  apply (Finset.sum_le_sum (fun e _ => runningMax_le (w e) 0 ω (w e 0 ω) (by
    intro i hi
    have : i = 0 := by omega
    subst i
    exact le_rfl))).trans
  exact hsum 0 ω

lemma energy_exp_cover (b x : ℝ) (hb : 0 < b) (M : ℕ) (hx : x ≤ 1+M*b) :
    Real.exp (Real.log (3/2) * (x-1) / b) ≤
      1 + ∑ k ∈ Finset.range M, if 1+k*b < x then (3/2 : ℝ)^(k+1) else 0 := by
  have hl : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
  induction M with
  | zero =>
    simp only [Nat.cast_zero,zero_mul,add_zero] at hx
    simp only [Finset.range_zero,Finset.sum_empty,add_zero]
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hl.le (by linarith)) hb.le
  | succ M ih =>
    rw [Finset.sum_range_succ]
    by_cases h : x ≤ 1+M*b
    · exact (ih h).trans (by
        have hh : 0 ≤ if 1+(M : ℝ)*b < x then (3/2 : ℝ)^(M+1) else 0 := by positivity
        linarith)
    · rw [ite_eq_left (lt_of_not_ge h)]
      have hv : Real.log (3/2) * (x-1) / b ≤ (M+1 : ℕ)*Real.log (3/2) := by
        apply (div_le_iff₀ hb).mpr
        have := mul_le_mul_of_nonneg_left (show x-1 ≤ (M+1 : ℕ)*b by linarith) hl.le
        nlinarith
      have he := Real.exp_le_exp.mpr hv
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ) < 3/2)] at he
      exact he.trans (by
        have hs : 0 ≤ ∑ k ∈ Finset.range M, if 1+(k : ℝ)*b < x then (3/2 : ℝ)^(k+1) else 0 :=
          Finset.sum_nonneg (fun k _ => by positivity)
        linarith)

lemma geometric_three_quarter_sum (M : ℕ) : ∑ k ∈ Finset.range M, (3/4 : ℝ)^k ≤ 4 := by
  have he : (∑ k ∈ Finset.range M, (3/4 : ℝ)^k) + 4*(3/4 : ℝ)^M = 4 := by
    induction M with
    | zero => simp
    | succ M ih => rw [Finset.sum_range_succ,pow_succ]; nlinarith
  have hp : 0 ≤ (3/4 : ℝ)^M := by positivity
  linarith

lemma geometric_tail_exponential {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X) (M : ℕ)
    (hbound : ∀ ω, X ω ≤ M)
    (b : ℝ) (hb : 1 ≤ b)
    (htail : ∀ k : ℕ, μ.real {ω | 1+k*b < X ω} ≤ (1/2 : ℝ)^k) :
    (∫ ω, Real.exp (Real.log (3/2) / b * X ω) ∂μ) ≤ 12 := by
  classical
  have hb0 : 0 < b := by linarith
  have hl : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
  let c := Real.log (3/2) / b
  have hc : 0 < c := div_pos hl hb0
  have hEint : Integrable (fun ω => Real.exp (c * (X ω-1))) μ := by
    apply (integrable_const (Real.exp (c*(M : ℝ)))).mono' ((hX.sub measurable_const).const_mul c).exp.aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    change c * (X ω-1) ≤ c * (M : ℝ)
    exact mul_le_mul_of_nonneg_left (by have := hbound ω; linarith) hc.le
  let A (k : ℕ) : Set Ω := {ω | 1+k*b < X ω}
  have hA (k : ℕ) : MeasurableSet (A k) := measurableSet_lt measurable_const hX
  have hI (k : ℕ) : Integrable ((A k).indicator (fun _ => (3/2 : ℝ)^(k+1))) μ :=
    (integrable_const _).indicator (hA k)
  have hi := integral_mono hEint ((integrable_const (1 : ℝ)).add
    (integrable_finsetSum _ (fun k _ => hI k))) (show ∀ ω, Real.exp (c*(X ω-1)) ≤
        1 + ∑ k ∈ Finset.range M, (A k).indicator (fun _ => (3/2 : ℝ)^(k+1)) ω from by
      intro ω
      have hB : X ω ≤ 1 + (M : ℝ)*b := by
        have hh : (M : ℝ) ≤ M*b := by nlinarith [Nat.cast_nonneg (α := ℝ) M]
        linarith [hbound ω]
      have hh := energy_exp_cover b (X ω) hb0 M hB
      simpa only [c,div_mul_eq_mul_div,Set.indicator_apply,Set.mem_ofPred_eq,A] using hh)
  simp only [Pi.add_apply] at hi
  rw [integral_add (integrable_const _) (integrable_finsetSum _ (fun k _ => hI k)),
    integral_const,probReal_univ,one_smul,integral_finsetSum _ (fun k _ => hI k)] at hi
  have hb7 : (∫ ω, Real.exp (c*(X ω-1)) ∂μ) ≤ 7 := by
    apply hi.trans
    have hh : (∑ k ∈ Finset.range M, ∫ ω, (A k).indicator (fun _ => (3/2 : ℝ)^(k+1)) ω ∂μ) ≤ 6 := by
      calc
        _ ≤ ∑ k ∈ Finset.range M, (3/2 : ℝ)^(k+1) * (1/2 : ℝ)^k := by
          apply Finset.sum_le_sum
          intro k _
          rw [integral_indicator_const _ (hA k),smul_eq_mul,mul_comm]
          exact mul_le_mul_of_nonneg_left (htail k) (by positivity)
        _ = (3/2 : ℝ) * ∑ k ∈ Finset.range M, (3/4 : ℝ)^k := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          rw [pow_succ]
          calc (3/2 : ℝ)^k * (3/2) * (1/2)^k = (3/2) * ((3/2)^k*(1/2)^k) := by ring
               _ = _ := by rw [← mul_pow]; norm_num
        _ ≤ 6 := by nlinarith [geometric_three_quarter_sum M]
    linarith
  have hc_bound : Real.exp c ≤ 3/2 := by
    apply (Real.exp_le_exp.mpr (show c ≤ Real.log (3/2) from (div_le_iff₀ hb0).mpr (by nlinarith))) |>.trans_eq
    exact Real.exp_log (by norm_num)
  have hfun : (fun ω => Real.exp (c * X ω)) = fun ω => Real.exp c * Real.exp (c*(X ω-1)) := by
    funext ω
    rw [← Real.exp_add]
    congr 1
    ring
  rw [show (fun ω => Real.exp (Real.log (3/2) / b * X ω)) = (fun ω => Real.exp (c * X ω)) from rfl,hfun,integral_const_mul]
  have hmul := mul_le_mul_of_nonneg_left hb7 (Real.exp_nonneg c)
  nlinarith

lemma integrable_exp_of_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (X : Ω → ℝ) (hX : Measurable X) (B c : ℝ)
    (hbound : ∀ ω, X ω ≤ B) (hc : 0 ≤ c) : Integrable (fun ω => Real.exp (c*X ω)) μ := by
  apply (integrable_const (Real.exp (c*B))).mono' (hX.const_mul c).exp.aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hbound ω) hc)

lemma posteriorMax_nonneg {Ω ι : Type*} [Fintype ι] (w : ι → ℕ → Ω → ℝ)
    (hpos : ∀ e i ω, 0 ≤ w e i ω) (n : ℕ) (ω : Ω) : 0 ≤ posteriorMax w n ω :=
  Finset.sum_nonneg (fun e _ => runningMax_nonneg (w e) (hpos e) n ω)

lemma posteriorMax_le_card {Ω ι : Type*} [Fintype ι] (w : ι → ℕ → Ω → ℝ)
    (hpos : ∀ e i ω, 0 ≤ w e i ω) (hsum : ∀ i ω, ∑ e, w e i ω ≤ 1) (n : ℕ) (ω : Ω) :
    posteriorMax w n ω ≤ Fintype.card ι := by
  calc
    _ ≤ ∑ _e : ι, (1 : ℝ) := Finset.sum_le_sum (fun e _ =>
      runningMax_le (w e) n ω 1 (fun i _ => posterior_coord_le_one w hpos hsum e i ω))
    _ = _ := by simp

end DirectionalZeroOne

end OAI

import Mathlib

namespace OAI

noncomputable section

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal
universe u

namespace SeparableQuotient.Positive.Rows
abbrev ContinuumIndex : Type := Cardinal.continuum.ord.ToType
instance continuumMeasurableSpace : MeasurableSpace ContinuumIndex := ⊤
def ContinuumAdditive (μ : Measure ContinuumIndex) : Prop :=
  ∀ (ι : Type) (_ : Cardinal.mk ι < Cardinal.continuum)
    (A : ι → Set ContinuumIndex), Pairwise (fun i j => Disjoint (A i) (A j)) →
      μ (⋃ i, A i) = ∑' i, μ (A i)



theorem small_null_union (μ : Measure ContinuumIndex) (hadd : ContinuumAdditive μ)
    {ι : Type} (hι : Cardinal.mk ι < Cardinal.continuum)
    (A : ι → Set ContinuumIndex) (hA : ∀ i, μ (A i) = 0) :
    μ (⋃ i, A i) = 0 := by
  classical
  let U := ⋃ i, A i
  let pick : U → ι := fun x => Classical.choose (Set.mem_iUnion.mp x.property)
  have hpick (x : U) : x.val ∈ A (pick x) :=
    Classical.choose_spec (Set.mem_iUnion.mp x.property)
  let B : ι → Set ContinuumIndex := fun i => {x | ∃ hx : x ∈ U, pick ⟨x, hx⟩ = i}
  have hBA (i : ι) : B i ⊆ A i := by
    rintro x ⟨hx, hi⟩
    simpa only [← hi] using hpick ⟨x, hx⟩
  have hdisj : Pairwise (fun i j => Disjoint (B i) (B j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    rintro x ⟨hx, hi⟩ ⟨hx', hj⟩
    exact hij (hi.symm.trans hj)
  have hUn : (⋃ i, B i) = U := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hx, _⟩
      exact hx
    · intro hx
      exact ⟨pick ⟨x, hx⟩, hx, rfl⟩
  rw [show (⋃ i, A i) = ⋃ i, B i from hUn.symm, hadd ι hι B hdisj]
  have hz (i : ι) : μ (B i) = 0 := measure_mono_null (hBA i) (hA i)
  simp only [hz, tsum_zero]

theorem small_set_null (μ : Measure ContinuumIndex) (hadd : ContinuumAdditive μ)
    (hsingle : ∀ i, μ {i} = 0) (A : Set ContinuumIndex)
    (hA : Cardinal.mk A < Cardinal.continuum) : μ A = 0 := by
  have h := small_null_union μ hadd hA (fun i : A => {i.val}) (fun i => hsingle i.val)
  simpa using h

theorem continuum_regular (μ : Measure ContinuumIndex) [IsProbabilityMeasure μ]
    (hadd : ContinuumAdditive μ) (hsingle : ∀ i, μ {i} = 0) :
    Cardinal.IsRegular Cardinal.continuum.{0} := by
  refine ⟨Cardinal.aleph0_le_continuum, ?_⟩
  by_contra! h
  obtain ⟨s, hs, hcard⟩ := Order.exists_cof_eq ContinuumIndex
  have hsmall : Cardinal.mk s < Cardinal.continuum := by
    rw [hcard, Ordinal.cof_toType]
    exact h
  have hcover : (⋃ i : s, Set.Iic i.val) = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    obtain ⟨i, hi, hxi⟩ := hs x
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  have hnull (i : s) : μ (Set.Iic i.val) = 0 := by
    rw [← Set.Iio_union_right]
    exact measure_union_null
      (small_set_null μ hadd hsingle _ (by simpa using Cardinal.mk_Iio_lt i.val (by simp [ContinuumIndex])))
      (hsingle i.val)
  have := small_null_union μ hadd hsmall (fun i : s => Set.Iic i.val) hnull
  rw [hcover, measure_univ] at this
  exact one_ne_zero this



theorem continuous_cdf_of_null_singletons (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] : Continuous (ProbabilityTheory.cdf ν) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let f := ProbabilityTheory.cdf ν
  apply f.mono.continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [f.rightLim_eq]
  apply le_antisymm (f.mono.leftLim_le (le_refl x))
  have h : ENNReal.ofReal (f x - leftLim f x) = 0 := by
    rw [← StieltjesFunction.measure_singleton, ProbabilityTheory.measure_cdf]
    exact measure_singleton x
  exact sub_nonpos.mp (ENNReal.ofReal_eq_zero.mp h)

theorem exists_cdf_value (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    {t : ℝ} (ht : 0 < t) (ht' : t < 1) : ∃ x, ProbabilityTheory.cdf ν x = t := by
  exact intermediate_value_univ₂_eventually₂ (continuous_cdf_of_null_singletons ν)
    continuous_const ((ProbabilityTheory.tendsto_cdf_atBot ν).eventually_le_const ht)
    ((ProbabilityTheory.tendsto_cdf_atTop ν).eventually_const_le ht')



theorem exists_subset_measure_of_real_embedding
    {I : Type*} [MeasurableSpace I] [DiscreteMeasurableSpace I]
    (μ : Measure I) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (b : I ↪ ℝ) (A : Set I) {t : ℝ} (ht : 0 ≤ t) (htA : t ≤ μ.real A) :
    ∃ B ⊆ A, μ B = ENNReal.ofReal t := by
  classical
  by_cases ht0 : t = 0
  · exact ⟨∅, empty_subset _, by simp [ht0]⟩
  by_cases htEq : t = μ.real A
  · exact ⟨A, Subset.rfl, by simp [htEq, measureReal_def]⟩
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have htlt : t < μ.real A := lt_of_le_of_ne htA htEq
  have hApos : 0 < (μ A).toReal := htpos.trans htlt
  have hA0 : μ A ≠ 0 := by
    intro h
    simp only [h, ENNReal.toReal_zero, lt_self_iff_false] at hApos
  let p : Measure I := (μ A)⁻¹ • μ.restrict A
  have hp : IsProbabilityMeasure p := by
    constructor
    simp [p, Measure.smul_apply, ENNReal.inv_mul_cancel hA0 (measure_ne_top μ A)]
  have hpn : NullSingletonClass p := by
    constructor
    intro i
    simp [p, Measure.smul_apply, measure_singleton]
  let q : Measure ℝ := p.map b
  have hq : IsProbabilityMeasure q := inferInstance
  have hqn : NullSingletonClass q := by
    constructor
    intro x
    rw [show q = p.map b from rfl,
      Measure.map_apply Measurable.of_discrete (measurableSet_singleton x)]
    exact (Set.subsingleton_singleton.preimage b.injective).measure_zero p
  obtain ⟨x, hx⟩ := exists_cdf_value q (div_pos htpos hApos)
    ((div_lt_one hApos).mpr htlt)
  refine ⟨b ⁻¹' Iic x ∩ A, inter_subset_right, ?_⟩
  calc
    μ (b ⁻¹' Iic x ∩ A) = μ A * q (Iic x) := by
      rw [show q = p.map b from rfl,
        Measure.map_apply Measurable.of_discrete measurableSet_Iic]
      simp only [p, Measure.smul_apply, smul_eq_mul,
        Measure.restrict_apply MeasurableSet.of_discrete]
      rw [ENNReal.mul_inv_cancel_left hA0 (measure_ne_top μ A)]
    _ = μ A * ENNReal.ofReal (t / (μ A).toReal) := by
      rw [← ProbabilityTheory.ofReal_cdf q x, hx]
    _ = ENNReal.ofReal t := by
      rw [ENNReal.ofReal_div_of_pos hApos, ENNReal.ofReal_toReal (measure_ne_top μ A)]
      rw [div_eq_mul_inv, mul_left_comm, ENNReal.mul_inv_cancel (hA0) (measure_ne_top μ A), mul_one]


theorem atomless_of_real_embedding
    {I : Type*} [MeasurableSpace I] [DiscreteMeasurableSpace I]
    (μ : Measure I) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (b : I ↪ ℝ) (A : Set I) (hA : 0 < μ A) :
    ∃ B ⊆ A, 0 < μ B ∧ μ B < μ A := by
  have hp : 0 < μ.real A := ENNReal.toReal_pos hA.ne' (measure_ne_top μ A)
  obtain ⟨B, hBA, hB⟩ := exists_subset_measure_of_real_embedding μ b A
    (t := μ.real A / 2) (by positivity) (by linarith)
  refine ⟨B, hBA, ?_, ?_⟩
  · rw [hB]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  · rw [hB, ← ENNReal.ofReal_toReal (measure_ne_top μ A)]
    apply (ENNReal.ofReal_lt_ofReal_iff hp).mpr
    linarith


theorem exists_subset_measure_ennreal
    {I : Type*} [MeasurableSpace I] [DiscreteMeasurableSpace I]
    (μ : Measure I) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (b : I ↪ ℝ) (A : Set I) {t : ℝ≥0∞} (htA : t ≤ μ A) :
    ∃ B ⊆ A, μ B = t := by
  have htfin : t ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top μ A) htA
  obtain ⟨B, hB, hμB⟩ := exists_subset_measure_of_real_embedding μ b A
    (t := t.toReal) ENNReal.toReal_nonneg (ENNReal.toReal_mono (measure_ne_top μ A) htA)
  exact ⟨B, hB, by simpa only [ENNReal.ofReal_toReal htfin] using hμB⟩



theorem exists_equal_partition
    {I : Type*} [MeasurableSpace I] [DiscreteMeasurableSpace I]
    (μ : Measure I) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (b : I ↪ ℝ) (n : ℕ) (A : Set I) (t : ℝ≥0∞)
    (hA : μ A = (n + 1 : ℕ) * t) :
    ∃ P : Fin (n + 1) → Set I,
      Pairwise (fun i j => Disjoint (P i) (P j)) ∧
      (⋃ i, P i) = A ∧ ∀ i, μ (P i) = t := by
  classical
  induction n generalizing A with
  | zero =>
    have : Nonempty (Fin (0 + 1)) := ⟨⟨0, by decide⟩⟩
    refine ⟨fun _ => A, ?_, ?_, ?_⟩
    · intro i j hij
      exact (hij (Fin.ext (by omega))).elim
    · ext x
      simp only [Set.mem_iUnion]
      exact ⟨fun ⟨i, hi⟩ => hi, fun hx => ⟨⟨0, by decide⟩, hx⟩⟩
    · intro i
      simpa using hA
  | succ n ih =>
    have htA : t ≤ μ A := by
      rw [hA]
      exact le_mul_of_one_le_left' (by norm_cast; omega)
    obtain ⟨B, hBA, hB⟩ := exists_subset_measure_ennreal μ b A htA
    have htfin : t ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top μ A) htA
    have hrem : μ (A \ B) = (n + 1 : ℕ) * t := by
      rw [measure_sdiff hBA MeasurableSet.of_discrete.nullMeasurableSet (measure_ne_top μ B), hA, hB]
      have hcast : ((n + 1 + 1 : ℕ) : ℝ≥0∞) = (n + 1 : ℕ) + 1 := by simp
      rw [show n.succ + 1 = n + 1 + 1 from rfl, hcast, add_mul, one_mul]
      exact ENNReal.add_sub_cancel_right htfin
    obtain ⟨P, hdisj, hcover, hmass⟩ := ih (A \ B) hrem
    have hPB (i) : P i ⊆ A \ B := by
      rw [← hcover]
      exact Set.subset_iUnion P i
    refine ⟨Fin.cons B P, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro hij
          exact (hij rfl).elim
        · intro _
          simpa using (disjoint_sdiff_right.mono_right (hPB j) : Disjoint B (P j))
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro _
          simpa using (disjoint_sdiff_right.mono_right (hPB i)).symm
        · intro hij
          simpa using hdisj (fun h => hij (congrArg Fin.succ h))
    · have hunion : (⋃ i, (Fin.cons B P : Fin (n + 2) → Set I) i) = B ∪ ⋃ i, P i := by
        ext x
        simp only [Set.mem_iUnion, Fin.exists_fin_succ, Fin.cons_zero,
          Fin.cons_succ, Set.mem_union]
      rw [hunion, hcover]
      exact union_sdiff_cancel hBA
    · intro i
      exact Fin.cases (by simpa using hB) (fun j => by simpa using hmass j) i


theorem exists_uniform_finite_map
    {I : Type*} [MeasurableSpace I] [DiscreteMeasurableSpace I]
    (μ : Measure I) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (b : I ↪ ℝ) (N : ℕ) (hN : 0 < N) :
    ∃ j : I → Fin N, ∀ i, μ (j ⁻¹' {i}) = (N : ℝ≥0∞)⁻¹ := by
  classical
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  obtain ⟨P, hdisj, hcover, hmass⟩ := exists_equal_partition μ b n Set.univ
    ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ (by
      rw [measure_univ]
      symm
      exact ENNReal.mul_inv_cancel (by simp) (by simp))
  have hex (x : I) : ∃ i, x ∈ P i := by
    apply Set.mem_iUnion.mp
    rw [hcover]
    exact Set.mem_univ x
  let j : I → Fin (n + 1) := fun x => Classical.choose (hex x)
  have hj (x : I) : x ∈ P (j x) := Classical.choose_spec (hex x)
  refine ⟨j, fun i => ?_⟩
  have hfiber : j ⁻¹' {i} = P i := by
    ext x
    constructor
    · intro hx
      have : j x = i := hx
      simpa only [← this] using hj x
    · intro hx
      change j x = i
      by_contra hne
      exact Set.disjoint_left.mp (hdisj hne) (hj x) hx
  rw [hfiber]
  exact hmass i


def RealValuedMeasurableContinuum : Prop :=
  ∃ μ : Measure ContinuumIndex,
    μ Set.univ = 1 ∧ (∀ i, μ {i} = 0) ∧ ContinuumAdditive μ

noncomputable def continuumRealEmbedding : ContinuumIndex ↪ ℝ :=
  (Classical.choice (Cardinal.eq.mp (by
    simp [ContinuumIndex, Cardinal.mk_real]))).toEmbedding



theorem continuum_measure_prerequisites (μ : Measure ContinuumIndex)
    [IsProbabilityMeasure μ] (hadd : ContinuumAdditive μ)
    (hsingle : ∀ i, μ {i} = 0) :
    Cardinal.IsRegular Cardinal.continuum.{0} ∧
    (∀ A : Set ContinuumIndex, 0 < μ A →
      ∃ B ⊆ A, 0 < μ B ∧ μ B < μ A) ∧
    (∀ N : ℕ, 0 < N → ∃ j : ContinuumIndex → Fin N,
      ∀ i, μ (j ⁻¹' {i}) = (N : ℝ≥0∞)⁻¹) := by
  let : NullSingletonClass μ := ⟨hsingle⟩
  exact ⟨continuum_regular μ hadd hsingle,
    atomless_of_real_embedding μ continuumRealEmbedding,
    exists_uniform_finite_map μ continuumRealEmbedding⟩



theorem small_null_union_lift {ι : Type u} (μ : Measure ContinuumIndex)
    (hadd : ContinuumAdditive μ) (hι : Cardinal.mk ι < Cardinal.continuum.{u})
    (A : ι → Set ContinuumIndex) (hA : ∀ i, μ (A i) = 0) :
    μ (⋃ i, A i) = 0 := by
  classical
  have hc : HasCardinalLT ι Cardinal.continuum.{0} := by
    simpa only [HasCardinalLT, Cardinal.lift_uzero, Cardinal.lift_continuum] using hι
  let : Small.{0} ι := hc.small
  have hs : Cardinal.mk (Shrink.{0} ι) < Cardinal.continuum.{0} := by
    have ht : Cardinal.lift.{u} (Cardinal.mk (Shrink.{0} ι)) < Cardinal.continuum.{u} := by
      simpa only [Cardinal.lift_mk_shrink', Cardinal.lift_uzero] using hι
    exact Cardinal.lift_lt_continuum.mp ht
  have hz := small_null_union μ hadd hs (fun j : Shrink.{0} ι => A ((equivShrink ι).symm j))
    (fun j => hA _)
  rwa [(equivShrink ι).symm.surjective.iUnion_comp A] at hz


theorem small_ae_all {ι : Type u} (μ : Measure ContinuumIndex)
    (hadd : ContinuumAdditive μ) (hι : Cardinal.mk ι < Cardinal.continuum.{u})
    (P : ι → ContinuumIndex → Prop) (hP : ∀ i, ∀ᵐ x ∂μ, P i x) :
    ∀ᵐ x ∂μ, ∀ i, P i x := by
  rw [ae_iff]
  have hz := small_null_union_lift μ hadd hι (fun i => {x | ¬ P i x})
    (fun i => ae_iff.mp (hP i))
  convert hz using 2
  ext x
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_forall]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


lemma row_sum_abs_le {N : ℕ} (u : Fin N → E)
    (hu : ∀ c : Fin N → ℝ, ‖∑ j, c j • u j‖ ≤ 2 * Real.sqrt (∑ j, (c j)^2))
    (y : StrongDual ℝ E) (hy : ‖y‖ ≤ 1) :
    ∑ j, |y (u j)| ≤ 2 * Real.sqrt N := by
  let b (j : Fin N) := y (u j)
  let S : ℝ := ∑ j, (b j)^2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hv : S ≤ 2 * Real.sqrt S := by
    calc
      S = y (∑ j, b j • u j) := by simp [S, b, sq, map_sum, map_smul]
      _ ≤ ‖y (∑ j, b j • u j)‖ := le_abs_self _
      _ ≤ ‖∑ j, b j • u j‖ := by
        exact (y.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hy (norm_nonneg _)).trans_eq (one_mul _))
      _ ≤ 2 * Real.sqrt S := hu b
  have hsqrt : Real.sqrt S ≤ 2 := by
    nlinarith [Real.sq_sqrt hS, Real.sqrt_nonneg S]
  have hS4 : S ≤ 4 := by nlinarith [Real.sq_sqrt hS, Real.sqrt_nonneg S]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N))
    (fun _ => (1 : ℝ)) (fun j => |b j|)
  have hc' : (∑ j, |b j|)^2 ≤ (N : ℝ) * S := by
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, sq_abs, S] using hc
  have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hsum : 0 ≤ ∑ j, |b j| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hh : (N : ℝ) * S ≤ (N : ℝ) * 4 := mul_le_mul_of_nonneg_left hS4 hn
  change (∑ j, |b j|) ≤ _
  nlinarith [Real.sq_sqrt hn, Real.sqrt_nonneg (N : ℝ)]

lemma lintegral_uniform_finite
    {I : Type*} [MeasurableSpace I] [DiscreteMeasurableSpace I]
    (μ : Measure I) {N : ℕ} (hN : 0 < N) (j : I → Fin N)
    (hj : ∀ i, μ (j ⁻¹' {i}) = (N : ℝ≥0∞)⁻¹)
    (b : Fin N → ℝ) (hb : ∀ i, 0 ≤ b i) :
    (∫⁻ α, ENNReal.ofReal (b (j α)) ∂μ) = ENNReal.ofReal ((∑ i, b i) / N) := by
  rw [← lintegral_map (f := fun i => ENNReal.ofReal (b i)) Measurable.of_discrete (Measurable.of_discrete (f := j)), lintegral_fintype]
  simp only [Measure.map_apply (Measurable.of_discrete (f := j)) (measurableSet_singleton _), hj]
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hb i)]
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hN), ENNReal.ofReal_natCast, div_eq_mul_inv]



lemma ae_summable_of_expected_bound
    {I : Type*} [MeasurableSpace I] [DiscreteMeasurableSpace I] (μ : Measure I)
    (v : ℕ → I → ℝ) (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n) (hs : Summable b)
    (hv : ∀ n, (∫⁻ α, ENNReal.ofReal |v n α| ∂μ) ≤ ENNReal.ofReal (b n)) :
    ∀ᵐ α ∂μ, Summable (fun n => |v n α|) := by
  have hfin : (∫⁻ α, ∑' n, ENNReal.ofReal |v n α| ∂μ) ≠ ⊤ := by
    rw [lintegral_tsum (fun n => Measurable.of_discrete.aemeasurable)]
    apply ne_of_lt
    exact lt_of_le_of_lt (ENNReal.tsum_le_tsum hv)
      (by rw [← ENNReal.ofReal_tsum_of_nonneg hb hs]; exact ENNReal.ofReal_lt_top)
  filter_upwards [ae_lt_top Measurable.of_discrete hfin] with α hα
  have hz : (∑' n, ‖v n α‖ₑ) ≠ ⊤ := by
    simpa only [← ofReal_norm, Real.norm_eq_abs] using hα.ne
  simpa only [Real.norm_eq_abs] using tsum_enorm_ne_top_iff_summable_norm.mp hz


lemma row_geometric_identity (n : ℕ) :
    2 * Real.sqrt ((16 ^ (n+1) : ℕ) : ℝ) / (16 ^ (n+1) : ℕ) =
      (1 / 2 : ℝ) * (1 / 4) ^ n := by
  have hN : ((16 ^ (n+1) : ℕ) : ℝ) = ((4 : ℝ) ^ (n+1)) ^ 2 := by
    push_cast
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  rw [hN, Real.sqrt_sq (by positivity)]
  rw [pow_succ, div_pow]
  field_simp
  ring



theorem select_rows_from_small_set {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure ContinuumIndex) [IsProbabilityMeasure μ]
    (hadd : ContinuumAdditive μ) (hsingle : ∀ i, μ {i} = 0)
    (u : ∀ n : ℕ, Fin (16 ^ (n+1)) → E)
    (hu : ∀ n (c : Fin (16 ^ (n+1)) → ℝ),
      ‖∑ j, c j • u n j‖ ≤ 2 * Real.sqrt (∑ j, (c j)^2))
    (A : Set (StrongDual ℝ E)) (hA : Cardinal.mk A < Cardinal.continuum.{u})
    (hy : ∀ y ∈ A, ‖y‖ ≤ 1) :
    ∃ j : ∀ n : ℕ, Fin (16 ^ (n+1)), ∀ y ∈ A, Summable (fun n => |y (u n (j n))|) := by
  have hN (n : ℕ) : 0 < 16 ^ (n+1) := pow_pos (by norm_num) _
  have hm (n : ℕ) := (continuum_measure_prerequisites μ hadd hsingle).2.2 _ (hN n)
  choose j hj using hm
  let b (n : ℕ) : ℝ := (1 / 2) * (1 / 4) ^ n
  have hb : Summable b :=
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 4) (by norm_num)).mul_left _
  have hsum (y : A) : ∀ᵐ α ∂μ, Summable (fun n => |y.val (u n (j n α))|) := by
    apply ae_summable_of_expected_bound μ _ b (fun n => by dsimp [b]; positivity) hb
    intro n
    rw [lintegral_uniform_finite μ (hN n) (j n) (hj n)
      (fun i => |y.val (u n i)|) (fun _ => abs_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    calc
      (∑ i, |y.val (u n i)|) / (16 ^ (n+1) : ℕ) ≤
          (2 * Real.sqrt ((16 ^ (n+1) : ℕ) : ℝ)) / (16 ^ (n+1) : ℕ) :=
        div_le_div_of_nonneg_right (row_sum_abs_le (u n) (hu n) y.val (hy y.val y.property)) (by positivity)
      _ = b n := row_geometric_identity n
  have hall := small_ae_all μ hadd hA (fun y : A => fun α =>
    Summable (fun n => |y.val (u n (j n α))|)) hsum
  obtain ⟨α, hα⟩ := hall.exists
  exact ⟨fun n => j n α, fun y hy => hα ⟨y, hy⟩⟩

end SeparableQuotient.Positive.Rows

end

end

end OAI

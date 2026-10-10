import OAI.Probability.DirectionalWalk.Records

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

noncomputable def slabRecords {d : ℕ} (v : Fin d → ℝ) (γ : Word d) : ℕ :=
  recordCount v (wordPath γ) γ.1

def slabWidth {d : ℕ} (v : Fin d → ℝ) (γ : Word d) : ℝ :=
  height v (wordPath γ γ.1)

lemma slabRecords_firstWord {d : ℕ} (v : Fin d → ℝ) (X : Path d) :
    slabRecords v (firstWord v X) = recordCount v X (firstCutTime v X) := by
  apply recordCount_prefix
  intro i hi
  exact wordPath_prefixWord _ X hi

lemma slabRecords_tail {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (j : ℕ) :
    slabLaw μ v {γ | j < slabRecords v γ} = conditioned μ v (noCutBeforeRecord v j) := by
  rw [slabLaw, Measure.map_apply (measurable_firstWord v)
    (measurableSet_lt measurable_const (measurable_of_countable (slabRecords v)))]
  apply measure_congr
  filter_upwards [ae_conditioned_firstWord μ hell v hv hp] with X hX
  apply propext
  change (j < slabRecords v (firstWord v X)) ↔ X ∈ noCutBeforeRecord v j
  rw [slabRecords_firstWord]
  have hc : ∃ n, trueCut v X n := by
    by_contra hh
    have hz := (firstCutTime_eq_zero_iff v X).mpr hh
    have hpos : 0 < firstCutTime v X := hX.1
    omega
  exact (noCutBeforeRecord_iff v X hc j).symm

lemma lintegral_slabRecords_le {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    (∫⁻ γ, (slabRecords v γ : ℝ≥0∞) ∂slabLaw μ v) ≤
      (annealed μ 0 (nonBacktracking v))⁻¹ := by
  rw [lintegral_nat_tail _ _ (measurable_of_countable _)]
  simp_rw [slabRecords_tail μ hell v hv hp]
  apply ENNReal.tsum_le_of_sum_range_le
  intro n
  cases n with
  | zero => simp
  | succ N =>
    have h := record_tail_sum_bound μ hell v hv hp N
    have hreflect := Finset.sum_range_reflect
      (fun j => conditioned μ v (noCutBeforeRecord v j)) (N+1)
    simp only [Nat.add_sub_cancel] at hreflect
    rw [hreflect] at h
    have hb := (ENNReal.mul_le_iff_le_inv hp.ne' (measure_ne_top _ _)).mp h
    simpa only [mul_one] using hb

lemma integrable_slabRecords {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    Integrable (fun γ => (slabRecords v γ : ℝ)) (slabLaw μ v) := by
  refine ⟨(measurable_of_countable _).aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
    (fun γ => Nat.cast_nonneg (slabRecords v γ)))).mpr
  simp_rw [ENNReal.ofReal_natCast]
  exact (lintegral_slabRecords_le μ hell v hv hp).trans_lt
    (ENNReal.inv_lt_top.mpr hp)

lemma height_stepVector_le_one {d : ℕ} (v : Fin d → ℝ)
    (hv : ∀ i, |v i| ≤ 1) (e : Step d) : height v (stepVector e) ≤ 1 := by
  rw [height_stepVector]
  have hi := abs_le.mp (hv e.1)
  split <;> linarith [hi.1,hi.2]

lemma height_le_recordCount {d : ℕ} (v : Fin d → ℝ) (X : Path d) (n : ℕ)
    (h0 : height v (X 0) = 0)
    (hs : ∀ i < n, height v (X (i+1)) ≤ height v (X i) + 1) :
    ∀ i ≤ n, height v (X i) ≤ (recordCount v X n : ℝ) := by
  classical
  induction n with
  | zero =>
    intro i hi
    have hi0 : i = 0 := by omega
    simp [hi0,h0,recordCount_zero]
  | succ n ih =>
    have ih' := ih (fun i hi => hs i (by omega))
    intro i hi
    by_cases hin : i ≤ n
    · exact (ih' i hin).trans (Nat.cast_le.mpr (recordCount_mono v X (by omega)))
    · have hin : i = n+1 := by omega
      subst i
      by_cases hr : strictRecord v X (n+1)
      · rw [recordCount_succ,ite_eq_left hr,Nat.cast_add,Nat.cast_one]
        linarith [hs n (by omega),ih' n le_rfl]
      · have hex : ∃ j < n+1, height v (X (n+1)) ≤ height v (X j) := by
          have hn : ¬∀ j < n+1, height v (X j) < height v (X (n+1)) :=
            fun hh => hr ⟨by omega,hh⟩
          push Not at hn
          exact hn
        obtain ⟨j,hj,hbound⟩ := hex
        exact hbound.trans ((ih' j (by omega)).trans
          (Nat.cast_le.mpr (recordCount_mono v X (by omega))))

lemma slabWidth_bounds {d : ℕ} (v : Fin d → ℝ) (hv : ∀ i, |v i| ≤ 1)
    (γ : Word d) (hγ : RegenerationWord v γ) :
    0 < slabWidth v γ ∧ slabWidth v γ ≤ (slabRecords v γ : ℝ) := by
  have hz : height v (wordPath γ 0) = 0 := by rw [hγ.2.1,height_zero]
  refine ⟨?_,height_le_recordCount v (wordPath γ) γ.1 hz ?_ γ.1 le_rfl⟩
  · have h := (hγ.2.2.2.1 0 hγ.1).2
    rwa [hz] at h
  · intro i hi
    obtain ⟨e,he⟩ := hγ.2.2.1 i hi
    rw [he,height_add]
    linarith [height_stepVector_le_one v hv e]

lemma integrable_slabWidth {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hvnorm : ∀ i, |v i| ≤ 1) (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    Integrable (slabWidth v) (slabLaw μ v) := by
  apply (integrable_slabRecords μ hell v hv hp).mono'
    (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [ae_slabLaw_regeneration μ hell v hv hp] with γ hγ
  have hb := slabWidth_bounds v hvnorm γ hγ
  simpa only [Real.norm_eq_abs,abs_of_pos hb.1] using hb.2

lemma lintegral_slabWidth_le {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hvnorm : ∀ i, |v i| ≤ 1) (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    (∫⁻ γ, ENNReal.ofReal (slabWidth v γ) ∂slabLaw μ v) ≤
      (annealed μ 0 (nonBacktracking v))⁻¹ := by
  apply le_trans (lintegral_mono_ae ?_) (lintegral_slabRecords_le μ hell v hv hp)
  filter_upwards [ae_slabLaw_regeneration μ hell v hv hp] with γ hγ
  simpa only [ENNReal.ofReal_natCast] using
    ENNReal.ofReal_le_ofReal (slabWidth_bounds v hvnorm γ hγ).2

lemma integral_slabWidth_pos {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hvnorm : ∀ i, |v i| ≤ 1) (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    0 < ∫ γ, slabWidth v γ ∂slabLaw μ v := by
  let := slabLaw_probability μ v hp
  have hpos : ∀ᵐ γ ∂slabLaw μ v, 0 < slabWidth v γ :=
    (ae_slabLaw_regeneration μ hell v hv hp).mono (fun γ hγ =>
      (slabWidth_bounds v hvnorm γ hγ).1)
  apply (integral_pos_iff_support_of_nonneg_ae (hpos.mono (fun _ h => h.le))
    (integrable_slabWidth μ hell v hv hvnorm hp)).mpr
  have hfull : slabLaw μ v (Function.support (slabWidth v)) = 1 := by
    apply (mem_ae_iff_prob_eq_one (measurableSet_support (measurable_of_countable _))).mp
    exact hpos.mono (fun _ h => h.ne')
  rw [hfull]
  exact zero_lt_one

lemma nonneg_sum_range_mono (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) {m n : ℕ}
    (h : m ≤ n) : ∑ j ∈ Finset.range m, f j ≤ ∑ j ∈ Finset.range n, f j := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun j _ _ => hf j)

lemma greedy_interval_bound (f b : ℕ → ℝ) (n : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (hf : ∀ j, 0 ≤ f j) (hb : ∀ j, b j ≤ 1)
    (hw : ∀ s, b s ≠ 0 → ∃ k : ℕ, 0 < k ∧ k ≤ n ∧
      a * (k : ℝ) ≤ ∑ j ∈ Finset.range k, f (s+j)) (M : ℕ) :
    a * ∑ s ∈ Finset.range M, b s ≤ ∑ j ∈ Finset.range (M+n), f j := by
  induction M using Nat.strong_induction_on generalizing f b with
  | h M ih =>
    by_cases hM : M = 0
    · subst M
      simpa using Finset.sum_nonneg (fun j _ => hf j)
    by_cases hb0 : b 0 = 0
    · obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM
      have hh := ih m (by omega) (fun j => f (j+1)) (fun j => b (j+1))
        (fun j => hf (j+1)) (fun j => hb (j+1)) (by
          intro s hs
          obtain ⟨k,hk,hkn,hkw⟩ := hw (s+1) hs
          refine ⟨k,hk,hkn,?_⟩
          simpa only [Nat.add_right_comm] using hkw)
      rw [Finset.sum_range_succ',hb0,add_zero]
      have hsum : ∑ j ∈ Finset.range (m+1+n), f j =
          (∑ j ∈ Finset.range (m+n), f (j+1)) + f 0 := by
        rw [show m+1+n = m+n+1 by omega,Finset.sum_range_succ']
      rw [hsum]
      linarith [hf 0]
    · obtain ⟨k,hk,hkn,hkw⟩ := hw 0 hb0
      simp only [Nat.zero_add] at hkw
      have hbfirst (r : ℕ) : ∑ j ∈ Finset.range r, b j ≤ (r : ℝ) := by
        have hh := Finset.sum_le_sum (s := Finset.range r) (fun j _ => hb j)
        simpa using hh
      by_cases hMk : M ≤ k
      · calc
          _ ≤ a * (M : ℝ) := mul_le_mul_of_nonneg_left (hbfirst M) ha
          _ ≤ a * (k : ℝ) := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hMk) ha
          _ ≤ ∑ j ∈ Finset.range k, f j := hkw
          _ ≤ _ := nonneg_sum_range_mono f hf (by omega)
      · have hkm : k < M := by omega
        have hh := ih (M-k) (by omega) (fun j => f (k+j)) (fun j => b (k+j))
          (fun j => hf (k+j)) (fun j => hb (k+j)) (by
            intro s hs
            obtain ⟨r,hr,hrn,hrw⟩ := hw (k+s) hs
            exact ⟨r,hr,hrn,by simpa only [Nat.add_assoc] using hrw⟩)
        have hsplit : ∑ j ∈ Finset.range M, b j =
            (∑ j ∈ Finset.range k, b j) + ∑ j ∈ Finset.range (M-k), b (k+j) := by
          rw [← Finset.sum_range_add, Nat.add_sub_of_le hkm.le]
        have hsplitf : ∑ j ∈ Finset.range (M+n), f j =
            (∑ j ∈ Finset.range k, f j) + ∑ j ∈ Finset.range (M-k+n), f (k+j) := by
          rw [← Finset.sum_range_add]
          exact congrArg (fun r => ∑ j ∈ Finset.range r, f j) (by omega)
        rw [hsplit,hsplitf,mul_add]
        exact add_le_add ((mul_le_mul_of_nonneg_left (hbfirst k) ha).trans hkw) hh

def initialAverageBad {Ω : Type*} (T : Ω → Ω) (f : Ω → ℝ) (a : ℝ) (n : ℕ) : Set Ω :=
  {x | ∃ k : ℕ, 0 < k ∧ k ≤ n ∧ a * (k : ℝ) < ∑ j ∈ Finset.range k, f (T^[j] x)}

lemma measurableSet_initialAverageBad {Ω : Type*} [MeasurableSpace Ω]
    (T : Ω → Ω) (hT : Measurable T) (f : Ω → ℝ) (hf : Measurable f)
    (a : ℝ) (n : ℕ) : MeasurableSet (initialAverageBad T f a n) := by
  unfold initialAverageBad
  simp only [Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.iUnion
  intro k
  exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    (measurableSet_lt measurable_const (Finset.measurable_sum _ (fun j _ => hf.comp (hT.iterate j)))))

lemma integral_comp_preserving {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (T : Ω → Ω) (hT : MeasurePreserving T P P) (f : Ω → ℝ)
    (hf : AEStronglyMeasurable f P) : (∫ x, f (T x) ∂P) = ∫ x, f x ∂P := by
  have hh := integral_map hT.measurable.aemeasurable (hT.map_eq.symm ▸ hf)
  rw [hT.map_eq] at hh
  exact hh.symm

lemma stationary_initial_average_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : Ω → Ω)
    (hT : MeasurePreserving T P P) (f : Ω → ℝ) (hfm : Measurable f)
    (hfi : Integrable f P) (hf : ∀ x, 0 ≤ f x) (a : ℝ) (ha : 0 < a) (n : ℕ) :
    P.real (initialAverageBad T f a n) ≤ (∫ x, f x ∂P) / a := by
  classical
  let B := initialAverageBad T f a n
  have hB : MeasurableSet B := measurableSet_initialAverageBad T hT.measurable f hfm a n
  let b : Ω → ℝ := B.indicator (fun _ => 1)
  have hbi : Integrable b P := (integrable_const (1 : ℝ)).indicator hB
  have hbe : (∫ x, b x ∂P) = P.real B := integral_indicator_one hB
  have hshiftf (j : ℕ) : Integrable (fun x => f (T^[j] x)) P :=
    (hT.iterate j).integrable_comp_of_integrable hfi
  have hshiftb (j : ℕ) : Integrable (fun x => b (T^[j] x)) P :=
    (hT.iterate j).integrable_comp_of_integrable hbi
  have hM (M : ℕ) : a * ((M : ℝ) * P.real B) ≤ ((M+n : ℕ) : ℝ) * (∫ x, f x ∂P) := by
    have hpoint (x : Ω) :
        a * ∑ s ∈ Finset.range M, b (T^[s] x) ≤
          ∑ j ∈ Finset.range (M+n), f (T^[j] x) := by
      apply greedy_interval_bound (fun j => f (T^[j] x)) (fun j => b (T^[j] x)) n a ha.le
        (fun j => hf _) (fun j => ?_) (fun s hs => ?_) M
      · simp only [b, Set.indicator_apply]
        split_ifs <;> norm_num
      · have hx : T^[s] x ∈ B := by
          by_contra hnot
          exact hs (Set.indicator_of_notMem hnot _)
        obtain ⟨k,hk,hkn,hkw⟩ := hx
        refine ⟨k,hk,hkn,hkw.le.trans_eq ?_⟩
        apply Finset.sum_congr rfl
        intro j hj
        rw [← Function.iterate_add_apply, Nat.add_comm j s]
    have hle := integral_mono
      ((integrable_finsetSum _ (fun j _ => hshiftb j)).const_mul a)
      (integrable_finsetSum _ (fun j _ => hshiftf j)) hpoint
    rw [integral_const_mul,integral_finsetSum _ (fun j _ => hshiftb j),
      integral_finsetSum _ (fun j _ => hshiftf j)] at hle
    simp_rw [integral_comp_preserving P _ (hT.iterate _) b hbi.aestronglyMeasurable,
      integral_comp_preserving P _ (hT.iterate _) f hfi.aestronglyMeasurable,hbe] at hle
    simpa using hle
  apply (le_div_iff₀ ha).mpr
  by_contra hnot
  have hpos : 0 < a * P.real B - (∫ x, f x ∂P) := by linarith
  obtain ⟨M,hMbig⟩ := exists_nat_gt (((n : ℝ) * (∫ x, f x ∂P)) /
    (a * P.real B - (∫ x, f x ∂P)))
  have hh := (div_lt_iff₀ hpos).mp hMbig
  have hh' := hM M
  push_cast at hh'
  nlinarith

end DirectionalZeroOne

end OAI

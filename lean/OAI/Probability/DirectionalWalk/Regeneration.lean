import OAI.Probability.DirectionalWalk.Columns

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

def strictRecord {d : ℕ} (v : Fin d → ℝ) (X : Path d) (n : ℕ) : Prop :=
  0 < n ∧ ∀ i < n, height v (X i) < height v (X n)

def trueCut {d : ℕ} (v : Fin d → ℝ) (X : Path d) (n : ℕ) : Prop :=
  strictRecord v X n ∧ ∀ j, height v (X n) ≤ height v (X (n+j))

lemma measurableSet_strictRecord {d : ℕ} (v : Fin d → ℝ) (n : ℕ) :
    MeasurableSet {X : Path d | strictRecord v X n} := by
  simp only [strictRecord, Set.ofPred_and, Set.ofPred_forall]
  exact (MeasurableSet.const _).inter (MeasurableSet.iInter (fun i =>
    MeasurableSet.iInter (fun _ => measurableSet_lt
      ((measurable_of_countable (height v)).comp (measurable_pi_apply i))
      ((measurable_of_countable (height v)).comp (measurable_pi_apply n)))))

lemma measurableSet_trueCut {d : ℕ} (v : Fin d → ℝ) (n : ℕ) :
    MeasurableSet {X : Path d | trueCut v X n} := by
  simp only [trueCut, Set.ofPred_and, Set.ofPred_forall]
  exact (measurableSet_strictRecord v n).inter (MeasurableSet.iInter (fun j =>
    measurableSet_le ((measurable_of_countable (height v)).comp (measurable_pi_apply n))
      ((measurable_of_countable (height v)).comp (measurable_pi_apply (n+j)))))

lemma strictRecord_prefix {d : ℕ} (v : Fin d → ℝ) {X Y : Path d} {n : ℕ}
    (hX : strictRecord v X n) (hY : Y ∈ pathCylinder n X) : strictRecord v Y n := by
  refine ⟨hX.1,fun i hi => ?_⟩
  rw [hY i hi.le, hY n le_rfl]
  exact hX.2 i hi

lemma unbounded_has_later_strictRecord {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (hX : ¬∃ b : ℝ, ∀ n, height v (X n) ≤ b) (N : ℕ) :
    ∃ n, N < n ∧ strictRecord v X n := by
  classical
  let b := (Finset.range (N+1)).sup' (by simp) (fun n => height v (X n))
  have hex : ∃ n, b < height v (X n) := by
    by_contra h
    push Not at h
    exact hX ⟨b,h⟩
  refine ⟨Nat.find hex, ?_, ?_⟩
  · by_contra h
    have hn : Nat.find hex ∈ Finset.range (N+1) := Finset.mem_range.mpr (by omega)
    exact (not_le_of_gt (Nat.find_spec hex)) (Finset.le_sup' (fun n => height v (X n)) hn)
  · refine ⟨?_,fun i hi => ?_⟩
    · have hzero : height v (X 0) ≤ b := Finset.le_sup' (fun n => height v (X n)) (Finset.mem_range.mpr (Nat.succ_pos N))
      by_contra h
      have hn : Nat.find hex = 0 := by omega
      have hh := Nat.find_spec hex
      rw [hn] at hh
      linarith
    · exact (le_of_not_gt (Nat.find_min hex hi)).trans_lt (Nat.find_spec hex)

lemma measurableSet_boundedHeight {d : ℕ} (v : Fin d → ℝ) :
    MeasurableSet {X : Path d | ∃ b : ℝ, ∀ n, height v (X n) ≤ b} := by
  have heq : {X : Path d | ∃ b : ℝ, ∀ n, height v (X n) ≤ b} =
      ⋃ b : ℤ, alwaysBelow v (b : ℝ) := by
    ext X
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨b,hb⟩
      exact ⟨⌈b⌉,fun n => (hb n).trans (Int.le_ceil b)⟩
    · rintro ⟨b,hb⟩; exact ⟨b,hb⟩
  rw [heq]
  exact MeasurableSet.iUnion (fun b => measurableSet_alwaysBelow v b)

lemma no_later_trueCut_null {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (y : Site d) (v : Fin d → ℝ) (hp : 0 < annealed μ 0 (nonBacktracking v)) (N : ℕ) :
    annealed μ y {X | (¬∃ b : ℝ, ∀ n, height v (X n) ≤ b) ∧
      ∀ n, N < n → ¬trueCut v X n} = 0 := by
  let p := (annealed μ 0 (nonBacktracking v)).toReal
  have hp' : 0 < p := ENNReal.toReal_pos (ne_of_gt hp) (measure_ne_top _ _)
  have hE : MeasurableSet {X : Path d | (¬∃ b : ℝ, ∀ n, height v (X n) ≤ b) ∧
      ∀ n, N < n → ¬trueCut v X n} := by
    simp only [Set.ofPred_and, Set.ofPred_forall]
    exact (measurableSet_boundedHeight v).compl.inter (MeasurableSet.iInter (fun n =>
      MeasurableSet.iInter (fun _ => (measurableSet_trueCut v n).compl)))
  apply null_of_prefix_contraction (annealed μ y) hE (1-p) (by linarith)
  intro X hX
  have hf : ∃ᶠ n in atTop, N < n ∧ strictRecord v X n := by
    apply frequently_atTop.mpr
    intro k
    obtain ⟨n,hn,hr⟩ := unbounded_has_later_strictRecord v X hX.1 (max k N)
    exact ⟨n,(le_max_left k N).trans hn.le,(le_max_right k N).trans_lt hn,hr⟩
  apply hf.mono
  rintro n ⟨hn,hr⟩
  refine real_contraction_of_disjoint_success (annealed μ y) (measurableSet_pathCylinder n X)
    ((measurable_tailPath n) (measurableSet_neverBelow v (height v (X n)))) ?_ p ?_
  · apply Set.disjoint_left.mpr
    rintro Y ⟨hY,hYC⟩ ⟨_,hS⟩
    apply hY.2 n hn
    refine ⟨strictRecord_prefix v hr hYC,fun j => ?_⟩
    rw [hYC n le_rfl]
    exact hS j
  · change (annealed μ y (pathCylinder n X ∩ tailPath n ⁻¹'
        neverBelow v (height v (X n)))).toReal = _
    rw [annealed_record_tail μ v y n X hr.2 (measurableSet_neverBelow v (height v (X n)))
      (fun _ h => h), annealed_neverBelow_start, ENNReal.toReal_mul, mul_comm]
    rfl

lemma ae_infinitely_trueCuts {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (y : Site d) (v : Fin d → ℝ) (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    ∀ᵐ X ∂annealed μ y, (¬∃ b : ℝ, ∀ n, height v (X n) ≤ b) →
      ∀ N, ∃ n, N < n ∧ trueCut v X n := by
  have hN (N : ℕ) : ∀ᵐ X ∂annealed μ y,
      ¬((¬∃ b : ℝ, ∀ n, height v (X n) ≤ b) ∧ ∀ n, N < n → ¬trueCut v X n) :=
    (measure_eq_zero_iff_ae_notMem).mp (no_later_trueCut_null μ y v hp N)
  filter_upwards [ae_all_iff.mpr hN] with X hX
  intro hu N
  by_contra h
  push Not at h
  exact hX N ⟨hu,h⟩

lemma escape_of_infinitely_trueCuts {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (hu : ¬∃ b : ℝ, ∀ n, height v (X n) ≤ b)
    (hcuts : ∀ N, ∃ n, N < n ∧ trueCut v X n) : X ∈ escape v := by
  apply tendsto_atTop.mpr
  intro b
  have hex : ∃ k, b < height v (X k) := by
    by_contra h; push Not at h; exact hu ⟨b,h⟩
  obtain ⟨k,hk⟩ := hex
  obtain ⟨n,hn,hr,ht⟩ := hcuts k
  apply eventually_atTop.mpr
  refine ⟨n,fun m hm => ?_⟩
  have ht' := ht (m-n)
  rw [Nat.add_sub_of_le hm] at ht'
  exact (hk.trans (hr.2 k hn)).le.trans ht'

lemma height_neg_direction {d : ℕ} (v : Fin d → ℝ) (x : Site d) :
    height (-v) x = -height v x := by simp [height, Finset.sum_neg_distrib]

lemma ae_escape_or_opposite {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (y : Site d) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) :
    ∀ᵐ X ∂annealed μ y, X ∈ escape v ∨ X ∈ escape (-v) := by
  filter_upwards [finite_supremum μ hell y v hv, ae_infinitely_trueCuts μ y v hp] with X hfin hcut
  by_cases hb : ∃ b : ℝ, ∀ n, height v (X n) ≤ b
  · right
    have ht := tendsto_neg_atBot_atTop.comp (hfin hb)
    change Tendsto (fun n => height (-v) (X n)) atTop atTop
    simpa only [height_neg_direction, Function.comp_def] using ht
  · exact Or.inl (escape_of_infinitely_trueCuts v X hb (hcut hb))

def nearestNeighbour {d : ℕ} (X : Path d) : Prop :=
  ∀ n, ∃ e : Step d, X (n+1) = X n + stepVector e

lemma ae_start_and_nearestNeighbour {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (y : Site d) : ∀ᵐ X ∂annealed μ y, X 0 = y ∧ nearestNeighbour X := by
  classical
  filter_upwards [ae_pathCylinder_ne_zero (annealed μ y)] with X hX
  constructor
  · by_contra h
    have hh := hX 0
    rw [annealed_cylinder, ite_eq_right (Ne.symm h)] at hh
    exact hh rfl
  · intro n
    by_contra h
    have hw (ω : Environment d) : entryWeight ω (X n) (X (n+1)) = 0 := by
      unfold entryWeight
      apply Finset.sum_eq_zero
      intro e _
      have he : X (n+1) ≠ X n + stepVector e := fun he => h ⟨e,he⟩
      simp [Ne.symm he]
    have hh := hX (n+1)
    rw [annealed_cylinder] at hh
    split_ifs at hh
    · simp only [pathWeight_succ, hw, mul_zero, lintegral_zero] at hh
      exact hh rfl
    · exact hh rfl

end DirectionalZeroOne

end OAI

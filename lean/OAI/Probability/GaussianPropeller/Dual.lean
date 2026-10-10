import OAI.Probability.GaussianPropeller.Moments

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaussianPropeller
open scoped RealInnerProductSpace

namespace Reduction

abbrev Tuple (d k : ℕ) := PiLp 2 (fun _ : Fin k => Space d)

variable {d k : ℕ} [NeZero k]

noncomputable def scoreMax (v : Fin k → Space d) (x : Space d) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => ⟪v i, x⟫)

noncomputable def width (v : Tuple d k) : ℝ := ∫ x, scoreMax v.ofLp x ∂gaussian d

theorem le_scoreMax (v : Fin k → Space d) (i : Fin k) (x : Space d) :
    ⟪v i, x⟫ ≤ scoreMax v x := by
  exact Finset.le_sup' (fun j => ⟪v j, x⟫) (Finset.mem_univ i)

theorem scoreMax_le_iff (v : Fin k → Space d) (x : Space d) (b : ℝ) :
    scoreMax v x ≤ b ↔ ∀ i, ⟪v i, x⟫ ≤ b := by
  simp only [scoreMax, Finset.sup'_le_iff, Finset.mem_univ, forall_const]

theorem exists_scoreMax (v : Fin k → Space d) (x : Space d) :
    ∃ i, ⟪v i, x⟫ = scoreMax v x := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => ⟪v i, x⟫)
  exact ⟨i, hi.symm⟩

theorem continuous_scoreMax (v : Fin k → Space d) : Continuous (scoreMax v) := by
  exact Continuous.finset_sup'_apply Finset.univ_nonempty (fun _ _ => by fun_prop)

theorem norm_scoreMax_le (v : Tuple d k) (x : Space d) :
    ‖scoreMax v.ofLp x‖ ≤ ‖v‖ * ‖x‖ := by
  obtain ⟨i, hi⟩ := exists_scoreMax v.ofLp x
  rw [← hi]
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (PiLp.norm_apply_le v i) (norm_nonneg x))

theorem integrable_scoreMax (v : Tuple d k) :
    Integrable (scoreMax v.ofLp) (gaussian d) := by
  apply ((integrable_id_gaussian d).norm.const_mul ‖v‖).mono'
    (continuous_scoreMax v.ofLp).aestronglyMeasurable
  exact Filter.Eventually.of_forall (norm_scoreMax_le v)

theorem scoreMax_sub_le (v w : Tuple d k) (x : Space d) :
    scoreMax v.ofLp x - scoreMax w.ofLp x ≤ ‖v - w‖ * ‖x‖ := by
  rw [sub_le_iff_le_add]
  apply (scoreMax_le_iff _ _ _).mpr
  intro i
  have hinner := real_inner_le_norm (v.ofLp i - w.ofLp i) x
  have hcoord : ‖v.ofLp i - w.ofLp i‖ ≤ ‖v - w‖ := PiLp.norm_apply_le (v - w) i
  have hmul := mul_le_mul_of_nonneg_right hcoord (norm_nonneg x)
  rw [inner_sub_left] at hinner
  linarith [le_scoreMax w.ofLp i x]

theorem norm_scoreMax_sub_le (v w : Tuple d k) (x : Space d) :
    ‖scoreMax v.ofLp x - scoreMax w.ofLp x‖ ≤ ‖v - w‖ * ‖x‖ := by
  rw [Real.norm_eq_abs, abs_le]
  have h := scoreMax_sub_le w v x
  rw [norm_sub_rev] at h
  exact ⟨by linarith, scoreMax_sub_le v w x⟩

theorem width_lipschitz_bound (v w : Tuple d k) :
    ‖width v - width w‖ ≤ (∫ x : Space d, ‖x‖ ∂gaussian d) * ‖v - w‖ := by
  rw [width, width, ← integral_sub (integrable_scoreMax v) (integrable_scoreMax w)]
  calc
    ‖∫ x, scoreMax v.ofLp x - scoreMax w.ofLp x ∂gaussian d‖ ≤
        ∫ x : Space d, ‖v - w‖ * ‖x‖ ∂gaussian d :=
      norm_integral_le_of_norm_le ((integrable_id_gaussian d).norm.const_mul _)
        (Filter.Eventually.of_forall (norm_scoreMax_sub_le v w))
    _ = (∫ x : Space d, ‖x‖ ∂gaussian d) * ‖v - w‖ := by
      rw [integral_const_mul, mul_comm]

theorem continuous_width : Continuous (width : Tuple d k → ℝ) := by
  let K : NNReal := ⟨∫ x : Space d, ‖x‖ ∂gaussian d,
    integral_nonneg (fun x => norm_nonneg x)⟩
  apply (LipschitzWith.of_dist_le_mul (K := K) ?_).continuous
  intro v w
  change ‖width v - width w‖ ≤ (∫ x : Space d, ‖x‖ ∂gaussian d) * ‖v - w‖
  exact width_lipschitz_bound v w

def scoreCell (v : Fin k → Space d) (i : Fin k) : Set (Space d) :=
  {x | (∀ j, ⟪v j, x⟫ ≤ ⟪v i, x⟫) ∧ (∀ j, j < i → ⟪v j, x⟫ < ⟪v i, x⟫)}

omit [NeZero k] in
theorem measurable_scoreCell (v : Fin k → Space d) (i : Fin k) :
    MeasurableSet (scoreCell v i) := by
  change MeasurableSet ({x | ∀ j, ⟪v j, x⟫ ≤ ⟪v i, x⟫} ∩
    {x | ∀ j, j < i → ⟪v j, x⟫ < ⟪v i, x⟫})
  apply MeasurableSet.inter
  · simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => measurableSet_le (by fun_prop) (by fun_prop)
  · simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    by_cases h : j < i
    · simpa [h] using
        (measurableSet_lt (show Measurable (fun x : Space d => ⟪v j, x⟫) by fun_prop)
          (show Measurable (fun x : Space d => ⟪v i, x⟫) by fun_prop))
    · simp [h]

theorem exists_unique_scoreCell (v : Fin k → Space d) (x : Space d) :
    ∃! i, x ∈ scoreCell v i := by
  classical
  let s := Finset.univ.filter (fun i => ⟪v i, x⟫ = scoreMax v x)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := exists_scoreMax v x
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let i := s.min' hs
  have hmax : ⟪v i, x⟫ = scoreMax v x := (Finset.mem_filter.mp (s.min'_mem hs)).2
  have hi : x ∈ scoreCell v i := by
    constructor
    · intro j
      rw [hmax]
      exact le_scoreMax v j x
    · intro j hji
      have hle : ⟪v j, x⟫ ≤ ⟪v i, x⟫ := hmax ▸ le_scoreMax v j x
      apply lt_of_le_of_ne hle
      intro heq
      have hmem : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ j, heq.trans hmax⟩
      exact (not_lt_of_ge (s.min'_le j hmem)) hji
  refine ⟨i, hi, ?_⟩
  intro j hj
  apply le_antisymm
  · by_contra h
    have hlt : i < j := lt_of_not_ge h
    exact (not_lt_of_ge (hi.1 j)) (hj.2 i hlt)
  · by_contra h
    have hlt : j < i := lt_of_not_ge h
    exact (not_lt_of_ge (hj.1 i)) (hi.2 j hlt)

theorem scoreCell_partition (v : Fin k → Space d) : IsPartition (scoreCell v) :=
  ⟨measurable_scoreCell v, Filter.Eventually.of_forall (exists_unique_scoreCell v)⟩

theorem scoreCell_score (v : Fin k → Space d) {i : Fin k} {x : Space d}
    (hx : x ∈ scoreCell v i) : ⟪v i, x⟫ = scoreMax v x := by
  exact le_antisymm (le_scoreMax v i x) ((scoreMax_le_iff _ _ _).mpr hx.1)

noncomputable def moments (A : Fin k → Set (Space d)) : Tuple d k :=
  WithLp.toLp 2 (fun i => centroid (A i))

omit [NeZero k] in
theorem norm_moments_sq (A : Fin k → Set (Space d)) : ‖moments A‖ ^ 2 = value A :=
  PiLp.norm_sq_eq_of_L2 _ _

omit [NeZero k] in
theorem pairing_integral {A : Fin k → Set (Space d)} (hA : IsPartition A)
    (v : Tuple d k) :
    ⟪v, moments A⟫ = ∫ x, ∑ i, (A i).indicator (fun x => ⟪v.ofLp i, x⟫) x
      ∂gaussian d := by
  rw [PiLp.inner_apply, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_indicator (hA.1 i), integral_inner (integrable_id_restrict d (A i))]
    rfl
  · intro i _
    exact ((integrable_id_gaussian d).const_inner (v.ofLp i)).indicator (hA.1 i)

theorem pairing_le_width {A : Fin k → Set (Space d)} (hA : IsPartition A)
    (v : Tuple d k) : ⟪v, moments A⟫ ≤ width v := by
  classical
  rw [pairing_integral hA]
  have hi : Integrable (fun x => ∑ i, (A i).indicator (fun x => ⟪v.ofLp i, x⟫) x)
      (gaussian d) := integrable_finsetSum _ (fun i _ =>
        ((integrable_id_gaussian d).const_inner (v.ofLp i)).indicator (hA.1 i))
  apply integral_mono_ae hi (integrable_scoreMax v)
  filter_upwards [hA.2] with x hx
  obtain ⟨i, hi, huniq⟩ := hx
  rw [Finset.sum_eq_single i]
  · simpa only [Set.indicator_of_mem hi] using le_scoreMax v.ofLp i x
  · intro j _ hji
    exact Set.indicator_of_notMem (fun hj => hji (huniq j hj)) _
  · simp

theorem pairing_scoreCell (v : Tuple d k) :
    ⟪v, moments (scoreCell v.ofLp)⟫ = width v := by
  classical
  rw [pairing_integral (scoreCell_partition v.ofLp)]
  apply integral_congr_ae
  filter_upwards [] with x
  obtain ⟨i, hi, huniq⟩ := exists_unique_scoreCell v.ofLp x
  rw [Finset.sum_eq_single i]
  · simpa only [Set.indicator_of_mem hi] using scoreCell_score v.ofLp hi
  · intro j _ hji
    exact Set.indicator_of_notMem (fun hj => hji (huniq j hj)) _
  · simp

theorem width_nonneg (v : Tuple d k) : 0 ≤ width v := by
  let i : Fin k := ⟨0, NeZero.pos k⟩
  have h := integral_mono_ae ((integrable_id_gaussian d).const_inner (v.ofLp i))
    (integrable_scoreMax v) (Filter.Eventually.of_forall (le_scoreMax v.ofLp i))
  have hzero : (∫ x : Space d, x ∂gaussian d) = 0 := integral_id_stdGaussian
  rw [integral_inner (integrable_id_gaussian d), hzero, inner_zero_right] at h
  exact h

theorem exists_max_width [NeZero d] :
    ∃ v : Tuple d k, ‖v‖ = 1 ∧ ∀ w : Tuple d k, ‖w‖ = 1 → width w ≤ width v := by
  obtain ⟨v, hv, hmax⟩ := (isCompact_sphere (0 : Tuple d k) 1).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1))
    continuous_width.continuousOn
  refine ⟨v, ?_, ?_⟩
  · simpa only [Metric.mem_sphere, dist_zero_right] using hv
  · intro w hw
    apply hmax
    simpa only [Metric.mem_sphere, dist_zero_right] using hw

theorem norm_moments_le {v : Tuple d k}
    (hmax : ∀ w : Tuple d k, ‖w‖ = 1 → width w ≤ width v)
    {A : Fin k → Set (Space d)} (hA : IsPartition A) : ‖moments A‖ ≤ width v := by
  by_cases hz : moments A = 0
  · simpa only [hz, norm_zero] using width_nonneg v
  have hn : ‖moments A‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  let w : Tuple d k := ‖moments A‖⁻¹ • moments A
  have hw : ‖w‖ = 1 := by
    rw [norm_smul_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hn]
  have h := (pairing_le_width hA w).trans (hmax w hw)
  have heq : ⟪w, moments A⟫ = ‖moments A‖ := by
    dsimp [w]
    rw [inner_smul_left, real_inner_self_eq_norm_sq]
    simp only [RCLike.conj_to_real]
    field_simp
  rwa [heq] at h

theorem exists_optimal_partition [NeZero d] :
    ∃ A : Fin k → Set (Space d), IsPartition A ∧
      ∀ B : Fin k → Set (Space d), IsPartition B → value B ≤ value A := by
  obtain ⟨v, hv, hmax⟩ := exists_max_width (d := d) (k := k)
  let A := scoreCell v.ofLp
  have hA := scoreCell_partition v.ofLp
  have hnorm : ‖moments A‖ = width v := by
    apply le_antisymm (norm_moments_le hmax hA)
    rw [← pairing_scoreCell]
    simpa only [hv, one_mul] using real_inner_le_norm v (moments A)
  refine ⟨A, hA, ?_⟩
  intro B hB
  have hnormB := norm_moments_le hmax hB
  rw [← hnorm] at hnormB
  rw [← norm_moments_sq, ← norm_moments_sq]
  exact sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hnormB

def Optimal (A : Fin k → Set (Space d)) : Prop :=
  IsPartition A ∧ ∀ B : Fin k → Set (Space d), IsPartition B → value B ≤ value A

noncomputable def activeLabels (A : Fin k → Set (Space d)) : Finset (Fin k) :=
  Finset.univ.filter (fun i => gaussian d (A i) ≠ 0)

noncomputable def activeCount (A : Fin k → Set (Space d)) : ℕ := (activeLabels A).card

def MinimalOptimal (A : Fin k → Set (Space d)) : Prop :=
  Optimal A ∧ ∀ B : Fin k → Set (Space d), Optimal B → activeCount A ≤ activeCount B

theorem exists_minimal_optimal [NeZero d] :
    ∃ A : Fin k → Set (Space d), MinimalOptimal A := by
  classical
  have hex : ∃ n, ∃ A : Fin k → Set (Space d), Optimal A ∧ activeCount A = n := by
    obtain ⟨A, hA⟩ := exists_optimal_partition (d := d) (k := k)
    exact ⟨activeCount A, A, hA, rfl⟩
  obtain ⟨A, hA, hn⟩ := Nat.find_spec hex
  refine ⟨A, hA, ?_⟩
  intro B hB
  rw [hn]
  exact Nat.find_min' hex ⟨B, hB, rfl⟩

def merge (A : Fin k → Set (Space d)) (i j : Fin k) (l : Fin k) : Set (Space d) :=
  if l = i then A i ∪ A j else if l = j then ∅ else A l

omit [NeZero k] in
theorem merge_partition {A : Fin k → Set (Space d)} (hA : IsPartition A)
    {i j : Fin k} (hij : i ≠ j) : IsPartition (merge A i j) := by
  classical
  constructor
  · intro l
    by_cases hli : l = i
    · simpa [merge, hli] using (hA.1 i).union (hA.1 j)
    · by_cases hlj : l = j
      · simp [merge, hlj, hij.symm]
      · simpa [merge, hli, hlj] using hA.1 l
  · filter_upwards [hA.2] with x hx
    obtain ⟨l, hl, huniq⟩ := hx
    by_cases hlj : l = j
    · subst l
      refine ⟨i, ?_, ?_⟩
      · simp [merge, hl]
      · intro q hq
        by_cases hqi : q = i
        · exact hqi
        · by_cases hqj : q = j
          · simp [merge, hqj, hij.symm] at hq
          · have hqA : x ∈ A q := by simpa [merge, hqi, hqj] using hq
            exact False.elim (hqj (huniq q hqA))
    · refine ⟨l, ?_, ?_⟩
      · by_cases hli : l = i
        · subst l
          simp [merge, hl]
        · simp [merge, hli, hlj, hl]
      · intro q hq
        by_cases hqi : q = i
        · subst q
          have h : x ∈ A i ∨ x ∈ A j := by simpa [merge] using hq
          rcases h with hi | hj
          · exact huniq i hi
          · exact False.elim (hlj (huniq j hj).symm)
        · by_cases hqj : q = j
          · simp [merge, hqj, hij.symm] at hq
          · apply huniq q
            simpa [merge, hqi, hqj] using hq

omit [NeZero k] in
theorem centroid_union {A : Fin k → Set (Space d)} (hA : IsPartition A)
    {i j : Fin k} (hij : i ≠ j) : centroid (A i ∪ A j) = centroid (A i) + centroid (A j) := by
  have hind : (A i ∪ A j).indicator (fun x => x) =ᵐ[gaussian d]
      (fun x => (A i).indicator (fun x => x) x + (A j).indicator (fun x => x) x) := by
    filter_upwards [hA.2] with x hx
    obtain ⟨l, _, huniq⟩ := hx
    by_cases hi : x ∈ A i <;> by_cases hj : x ∈ A j
    · exact False.elim (hij ((huniq i hi).trans (huniq j hj).symm))
    all_goals simp [Set.indicator, hi, hj]
  unfold centroid
  rw [← integral_indicator ((hA.1 i).union (hA.1 j)), integral_congr_ae hind,
    integral_add ((integrable_id_gaussian d).indicator (hA.1 i))
      ((integrable_id_gaussian d).indicator (hA.1 j)),
    integral_indicator (hA.1 i), integral_indicator (hA.1 j)]

omit [NeZero k] in
theorem value_merge {A : Fin k → Set (Space d)} (hA : IsPartition A)
    {i j : Fin k} (hij : i ≠ j) :
    value (merge A i j) = value A + 2 * ⟪centroid (A i), centroid (A j)⟫ := by
  classical
  have hcent : centroid (A i ∪ A j) = centroid (A i) + centroid (A j) := centroid_union hA hij
  have hfun (l : Fin k) : ‖centroid (merge A i j l)‖ ^ 2 =
      ‖centroid (A l)‖ ^ 2 +
      (if l = i then ‖centroid (A i) + centroid (A j)‖ ^ 2 - ‖centroid (A i)‖ ^ 2 else 0) +
      (if l = j then -‖centroid (A j)‖ ^ 2 else 0) := by
    by_cases hli : l = i
    · subst l
      simp [merge, hij, hcent]
    · by_cases hlj : l = j
      · subst l
        simp [merge, hij.symm]
      · simp [merge, hli, hlj]
  unfold value
  simp_rw [hfun, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [norm_add_sq_real]
  ring

omit [NeZero k] in
theorem activeCount_merge_lt {A : Fin k → Set (Space d)} {i j : Fin k}
    (hij : i ≠ j) (hi : gaussian d (A i) ≠ 0) (hj : gaussian d (A j) ≠ 0) :
    activeCount (merge A i j) < activeCount A := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro l hl
    simp only [activeLabels, Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    by_cases hli : l = i
    · simpa only [hli] using hi
    · by_cases hlj : l = j
      · simp [merge, hlj, hij.symm] at hl
      · simpa only [merge, ite_eq_right hli, ite_eq_right hlj] using hl
  · intro heq
    have hs : j ∈ activeLabels (merge A i j) := by
      rw [heq]
      simpa only [activeLabels, Finset.mem_filter, Finset.mem_univ, true_and] using hj
    have hnon : gaussian d (merge A i j j) ≠ 0 := (Finset.mem_filter.mp hs).2
    exact hnon (by simp [merge, hij.symm])

omit [NeZero k] in
theorem negative_inner_of_minimal {A : Fin k → Set (Space d)} (hA : MinimalOptimal A)
    {i j : Fin k} (hij : i ≠ j) (hi : gaussian d (A i) ≠ 0) (hj : gaussian d (A j) ≠ 0) :
    ⟪centroid (A i), centroid (A j)⟫ < 0 := by
  have hpart := merge_partition hA.1.1 hij
  have hvalue := value_merge hA.1.1 hij
  have hbound := hA.1.2 _ hpart
  have hle : ⟪centroid (A i), centroid (A j)⟫ ≤ 0 := by linarith
  apply lt_of_le_of_ne hle
  intro heq
  have heqval : value (merge A i j) = value A := by rw [heq, mul_zero, add_zero] at hvalue; exact hvalue
  have hopt : Optimal (merge A i j) := ⟨hpart, fun B hB => by rw [heqval]; exact hA.1.2 B hB⟩
  exact (not_lt_of_ge (hA.2 _ hopt)) (activeCount_merge_lt hij hi hj)

theorem width_moments_of_optimal {A : Fin k → Set (Space d)} (hA : Optimal A) :
    width (moments A) = value A := by
  have hnorm : ‖moments (scoreCell (moments A).ofLp)‖ ≤ ‖moments A‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_moments_sq, norm_moments_sq]
    exact hA.2 _ (scoreCell_partition _)
  apply le_antisymm
  · rw [← pairing_scoreCell, ← norm_moments_sq]
    calc
      ⟪moments A, moments (scoreCell (moments A).ofLp)⟫ ≤
          ‖moments A‖ * ‖moments (scoreCell (moments A).ofLp)‖ := real_inner_le_norm _ _
      _ ≤ ‖moments A‖ * ‖moments A‖ := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
      _ = ‖moments A‖ ^ 2 := (sq _).symm
  · simpa only [real_inner_self_eq_norm_sq, norm_moments_sq] using pairing_le_width hA.1 (moments A)

omit [NeZero k] in
theorem centroid_eq_zero_of_null {A : Set (Space d)} (hA : gaussian d A = 0) : centroid A = 0 := by
  unfold centroid
  rw [Measure.restrict_eq_zero.mpr hA, integral_zero_measure]

theorem assigned_le_scoreMax {A : Fin k → Set (Space d)} (hA : IsPartition A) (v : Tuple d k) :
    (fun x => ∑ i, (A i).indicator (fun x => ⟪v.ofLp i, x⟫) x) ≤ᵐ[gaussian d]
      scoreMax v.ofLp := by
  classical
  filter_upwards [hA.2] with x hx
  obtain ⟨i, hi, huniq⟩ := hx
  rw [Finset.sum_eq_single i]
  · simpa only [Set.indicator_of_mem hi] using le_scoreMax v.ofLp i x
  · intro j _ hji
    exact Set.indicator_of_notMem (fun hj => hji (huniq j hj)) _
  · simp

theorem optimal_winning_ae {A : Fin k → Set (Space d)} (hA : Optimal A) :
    ∀ᵐ x ∂gaussian d, ∀ i, x ∈ A i → ⟪centroid (A i), x⟫ =
      scoreMax (fun j => centroid (A j)) x := by
  classical
  let v := moments A
  let f (x : Space d) := ∑ i, (A i).indicator (fun x => ⟪v.ofLp i, x⟫) x
  have hf : Integrable f (gaussian d) :=
    integrable_finsetSum _ (fun i _ =>
      ((integrable_id_gaussian d).const_inner (v.ofLp i)).indicator (hA.1.1 i))
  have hgap : (fun x => scoreMax v.ofLp x - f x) =ᵐ[gaussian d] 0 := by
    apply (integral_eq_zero_iff_of_nonneg_ae
      (show 0 ≤ᵐ[gaussian d] (fun x => scoreMax v.ofLp x - f x) from
        (assigned_le_scoreMax hA.1 v).mono (fun x hx => sub_nonneg.mpr hx))
      ((integrable_scoreMax v).sub hf)).mp
    rw [integral_sub (integrable_scoreMax v) hf]
    have hi : (∫ x, f x ∂gaussian d) = value A := by
      rw [← pairing_integral hA.1, real_inner_self_eq_norm_sq, norm_moments_sq]
    rw [hi]
    exact sub_eq_zero.mpr (width_moments_of_optimal hA)
  filter_upwards [hgap, hA.1.2] with x hx hxA
  intro i hi
  obtain ⟨j, _, huniq⟩ := hxA
  have hiuniq : ∀ l, x ∈ A l → l = i := fun l hl => (huniq l hl).trans (huniq i hi).symm
  have hfx : f x = ⟪v.ofLp i, x⟫ := by
    dsimp only [f]
    rw [Finset.sum_eq_single i]
    · exact Set.indicator_of_mem hi _
    · intro l _ hli
      exact Set.indicator_of_notMem (fun hl => hli (hiuniq l hl)) _
    · simp
  change scoreMax v.ofLp x - f x = 0 at hx
  rw [hfx] at hx
  exact (sub_eq_zero.mp hx).symm

omit [NeZero k] in

theorem two_nonzero_centroids {A : Fin k → Set (Space d)} (hA : IsPartition A)
    (hpos : 0 < value A) : ∃ i j, i ≠ j ∧ centroid (A i) ≠ 0 ∧ centroid (A j) ≠ 0 := by
  classical
  have hi : ∃ i, centroid (A i) ≠ 0 := by
    by_contra! h
    have hz : value A = 0 := by simp [value, h]
    linarith
  obtain ⟨i, hi⟩ := hi
  have hj : ∃ j, j ≠ i ∧ centroid (A j) ≠ 0 := by
    by_contra! h
    have hz : ∑ j, centroid (A j) = centroid (A i) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact h j hji
      · simp
    exact hi (hz.symm.trans (sum_centroid_eq_zero hA))
  obtain ⟨j, hji, hj⟩ := hj
  exact ⟨i, j, hji.symm, hi, hj⟩

omit [NeZero k] in
theorem active_centroid_ne_zero {A : Fin k → Set (Space d)} (hA : MinimalOptimal A)
    (hpos : 0 < value A) {i : Fin k} (hi : gaussian d (A i) ≠ 0) : centroid (A i) ≠ 0 := by
  obtain ⟨j, l, hjl, hj, hl⟩ := two_nonzero_centroids hA.1.1 hpos
  have hjm : gaussian d (A j) ≠ 0 := fun hz => hj (centroid_eq_zero_of_null hz)
  have hlm : gaussian d (A l) ≠ 0 := fun hz => hl (centroid_eq_zero_of_null hz)
  by_cases hij : i = j
  · simpa only [hij] using hj
  · have hneg := negative_inner_of_minimal hA hij hi hjm
    intro hz
    simp only [hz, inner_zero_left] at hneg
    exact (lt_irrefl 0) hneg

omit [NeZero k] in
theorem active_centroid_ne_other {A : Fin k → Set (Space d)} (hA : MinimalOptimal A)
    (hpos : 0 < value A) {i j : Fin k} (hi : gaussian d (A i) ≠ 0) (hij : i ≠ j) :
    centroid (A i) ≠ centroid (A j) := by
  by_cases hj : gaussian d (A j) = 0
  · rw [centroid_eq_zero_of_null hj]
    exact active_centroid_ne_zero hA hpos hi
  · intro heq
    have hneg := negative_inner_of_minimal hA hij hi hj
    rw [heq, real_inner_self_eq_norm_sq] at hneg
    exact (not_lt_of_ge (sq_nonneg _)) hneg

omit [NeZero k] in

theorem gaussian_hyperplane_null (z : Space d) (hz : z ≠ 0) (c : ℝ) :
    gaussian d {x | ⟪z, x⟫ = c} = 0 := by
  let L : StrongDual ℝ (Space d) := innerSL ℝ z
  have hL : L ≠ 0 := by
    intro heq
    have hx : ⟪z, z⟫ = 0 := by
      have h := DFunLike.congr_fun heq z
      simpa [L] using h
    exact hz (inner_self_eq_zero.mp hx)
  have hv : (variance L (stdGaussian (Space d))).toNNReal ≠ 0 := by
    rw [variance_dual_stdGaussian]
    exact ne_of_gt (Real.toNNReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr hL)))
  have instN : NullSingletonClass
      (gaussianReal (∫ x, L x ∂stdGaussian (Space d))
        (variance L (stdGaussian (Space d))).toNNReal) := nullSingletonClass_gaussianReal hv
  have h := congrArg (fun μ : Measure ℝ => μ {c}) (IsGaussian.map_eq_gaussianReal
    (μ := stdGaussian (Space d)) L)
  rw [Measure.map_apply L.continuous.measurable (measurableSet_singleton c),
    measure_singleton] at h
  exact h

def closedCell (z : Fin k → Space d) (i : Fin k) : Set (Space d) :=
  {x | ∀ j, ⟪z j, x⟫ ≤ ⟪z i, x⟫}

omit [NeZero k] in
theorem measurableSet_closedCell (z : Fin k → Space d) (i : Fin k) :
    MeasurableSet (closedCell z i) := by
  unfold closedCell
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun j => measurableSet_le
    (by fun_prop) (by fun_prop))

theorem active_eq_closedCell_ae {A : Fin k → Set (Space d)}
    (hA : MinimalOptimal A) (hpos : 0 < value A) {i : Fin k}
    (hi : gaussian d (A i) ≠ 0) :
    A i =ᵐ[gaussian d] closedCell (fun j => centroid (A j)) i := by
  classical
  have hnotie : ∀ j, i ≠ j → ∀ᵐ x ∂gaussian d,
      ⟪centroid (A i), x⟫ ≠ ⟪centroid (A j), x⟫ := by
    intro j hij
    rw [ae_iff]
    change gaussian d {x | ¬⟪centroid (A i), x⟫ ≠ ⟪centroid (A j), x⟫} = 0
    simpa only [not_not, inner_sub_left, sub_eq_zero] using
      gaussian_hyperplane_null (centroid (A i) - centroid (A j))
        (sub_ne_zero.mpr (active_centroid_ne_other hA hpos hi hij)) 0
  have hnt : ∀ᵐ x ∂gaussian d, ∀ j, i ≠ j →
      ⟪centroid (A i), x⟫ ≠ ⟪centroid (A j), x⟫ := by
    exact ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun hij => hnotie j hij))
  filter_upwards [hA.1.1.2, optimal_winning_ae hA.1, hnt] with x hx hwin hnt
  apply propext
  constructor
  · intro hix j
    rw [hwin i hix]
    exact le_scoreMax (fun j => centroid (A j)) j x
  · intro hclosed
    obtain ⟨j, hj, _⟩ := hx
    by_cases hji : j = i
    · subst j
      exact hj
    · have hle := hclosed j
      rw [hwin j hj] at hle
      have heq := le_antisymm (le_scoreMax (fun l => centroid (A l)) i x) hle
      exact False.elim (hnt j (Ne.symm hji) (heq.trans (hwin j hj).symm))

end Reduction

end GaussianPropeller

end OAI

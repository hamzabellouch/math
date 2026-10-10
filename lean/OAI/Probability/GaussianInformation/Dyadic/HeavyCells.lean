import Mathlib
import OAI.Probability.GaussianInformation.Dyadic.BlockInformation

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization

noncomputable def heavyThreshold (n j : ℕ) : ℝ := (2:ℝ)^(-(n:ℝ)*j/2)

lemma heavyThreshold_pos (n j : ℕ) : 0 < heavyThreshold n j := Real.rpow_pos_of_pos (by norm_num) _
lemma heavyThreshold_zero (n : ℕ) : heavyThreshold n 0 = 1 := by simp [heavyThreshold]
lemma heavyThreshold_add (n j l : ℕ) : heavyThreshold n (j+l) = heavyThreshold n j*heavyThreshold n l := by
  unfold heavyThreshold
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  congr 1
  simp only [Nat.cast_add]
  ring

noncomputable def deepHeavyDepth {n : ℕ} (μ : Measure (Coordinate n))
    (Q : Cell n) (D : ℕ) (z : Coordinate n) : ℕ :=
  (Finset.range (D+1)).sup' Finset.nonempty_range_add_one (fun j =>
    if heavyThreshold n j ≤ μ.real (cellSet (cellAt (Q.1+j) z)) then j else 0)

lemma deepHeavyDepth_le {n : ℕ} (μ : Measure (Coordinate n)) (Q : Cell n) (D : ℕ) (z : Coordinate n) :
    deepHeavyDepth μ Q D z ≤ D := by
  unfold deepHeavyDepth
  apply Finset.sup'_le
  intro j hj
  have hj' := Finset.mem_range.mp hj
  split_ifs <;> omega

lemma le_deepHeavyDepth {n : ℕ} (μ : Measure (Coordinate n)) (Q : Cell n) (D : ℕ) (z : Coordinate n)
    {j : ℕ} (hj : j ≤ D) (heavy : heavyThreshold n j ≤ μ.real (cellSet (cellAt (Q.1+j) z))) :
    j ≤ deepHeavyDepth μ Q D z := by
  have h := Finset.le_sup' (s := Finset.range (D+1))
    (fun j => if heavyThreshold n j ≤ μ.real (cellSet (cellAt (Q.1+j) z)) then j else 0)
    (Finset.mem_range.mpr (show j < D+1 by omega))
  simpa only [ite_eq_left heavy,deepHeavyDepth] using h

lemma measurable_deepHeavyDepth {n : ℕ} (μ : Measure (Coordinate n)) (Q : Cell n) (D : ℕ) :
    Measurable (deepHeavyDepth μ Q D) := by
  classical
  apply Finset.measurable_range_sup''
  intro j _
  apply Measurable.ite _ measurable_const measurable_const
  exact measurableSet_le measurable_const ((measurable_of_countable (fun R : Cell n => μ.real (cellSet R))).comp (measurable_cellAt _))

lemma deepHeavyDepth_heavy {n : ℕ} (hn : 0 < n) (μ : Measure (Coordinate n))
    (Q : Cell n) (hQ : μ.real (cellSet Q) = 1) (D : ℕ) {z : Coordinate n} (hz : z ∈ cellSet Q) :
    heavyThreshold n (deepHeavyDepth μ Q D z) ≤ μ.real (cellSet (cellAt (Q.1+deepHeavyDepth μ Q D z) z)) := by
  obtain ⟨j,_,he⟩ := Finset.exists_mem_eq_sup' (Finset.nonempty_range_add_one (n := D))
    (fun j => if heavyThreshold n j ≤ μ.real (cellSet (cellAt (Q.1+j) z)) then j else 0)
  change deepHeavyDepth μ Q D z = _ at he
  split_ifs at he with hh
  · simpa only [he] using hh
  · rw [he,heavyThreshold_zero,Nat.add_zero,cellAt_eq_of_mem hn Q hz,hQ]

noncomputable def deepHeavyCell {n : ℕ} (μ : Measure (Coordinate n))
    (Q : Cell n) (D : ℕ) (z : Coordinate n) : Cell n := by
  classical
  exact if z ∈ cellSet Q then cellAt (Q.1+deepHeavyDepth μ Q D z) z else Q

lemma measurable_cellAt_variable {n : ℕ} (J : Coordinate n → ℕ) (hJ : Measurable J) :
    Measurable (fun z => cellAt (J z) z) := by
  have h : Measurable (fun x : ℕ × Coordinate n => cellAt x.1 x.2) := by
    apply measurable_from_prod_countable_right
    intro j
    exact measurable_cellAt j
  exact h.comp (hJ.prodMk measurable_id)

lemma measurable_deepHeavyCell {n : ℕ} (μ : Measure (Coordinate n)) (Q : Cell n) (D : ℕ) :
    Measurable (deepHeavyCell μ Q D) := by
  classical
  unfold deepHeavyCell
  apply Measurable.ite (measurableSet_cellSet Q) _ measurable_const
  apply measurable_cellAt_variable
  exact measurable_const.add (measurable_deepHeavyDepth μ Q D)

lemma deepHeavyCell_mem {n : ℕ} (hn : 0 < n) (μ : Measure (Coordinate n))
    (Q : Cell n) (D : ℕ) {z : Coordinate n} (hz : z ∈ cellSet Q) :
    z ∈ cellSet (deepHeavyCell μ Q D z) := by
  rw [deepHeavyCell,ite_eq_left hz]
  exact mem_cellAt hn _ (cellSet_subset_initialCube hn Q hz)

lemma deepHeavyCell_subset {n : ℕ} (hn : 0 < n) (μ : Measure (Coordinate n))
    (Q : Cell n) (D : ℕ) (z : Coordinate n) : cellSet (deepHeavyCell μ Q D z) ⊆ cellSet Q := by
  classical
  by_cases hz : z ∈ cellSet Q
  · rw [deepHeavyCell,ite_eq_left hz]
    have h := cellAt_nested hn (show Q.1 ≤ Q.1+deepHeavyDepth μ Q D z by omega) (cellSet_subset_initialCube hn Q hz)
    rwa [cellAt_eq_of_mem hn Q hz] at h
  · simp only [deepHeavyCell,ite_eq_right hz,Subset.rfl]

lemma deepHeavyCell_level {n : ℕ} (μ : Measure (Coordinate n))
    (Q : Cell n) (D : ℕ) {z : Coordinate n} (hz : z ∈ cellSet Q) :
    (deepHeavyCell μ Q D z).1 = Q.1+deepHeavyDepth μ Q D z := by
  simp only [deepHeavyCell,ite_eq_left hz,cellAt]

lemma finite_cells_bounded_level (n D : ℕ) : {Q : Cell n | Q.1 ≤ D}.Finite := by
  have h : {Q : Cell n | Q.1 ≤ D} ⊆ ⋃ j : Fin (D+1), Set.range (fun a : Fin n → Fin (2^j.val) => (⟨j.val,a⟩ : Cell n)) := by
    rintro ⟨j,a⟩ hj
    exact Set.mem_iUnion.mpr ⟨⟨j,by simpa using Nat.lt_succ_iff.mpr hj⟩,⟨a,rfl⟩⟩
  exact (Set.finite_iUnion (fun _ => Set.finite_range _)).subset h

lemma finite_range_deepHeavyCell {n : ℕ} (μ : Measure (Coordinate n)) (Q : Cell n) (D : ℕ) :
    (Set.range (deepHeavyCell μ Q D)).Finite := by
  apply (finite_cells_bounded_level n (Q.1+D)).subset
  rintro _ ⟨z,rfl⟩
  change (deepHeavyCell μ Q D z).1 ≤ Q.1+D
  unfold deepHeavyCell
  split_ifs
  · change Q.1+deepHeavyDepth μ Q D z ≤ Q.1+D
    exact Nat.add_le_add_left (deepHeavyDepth_le μ Q D z) Q.1
  · omega

lemma heavyThreshold_pow (n j : ℕ) : heavyThreshold n j = (heavyThreshold n 1)^j := by
  induction j with
  | zero => simp [heavyThreshold_zero]
  | succ j ih => rw [heavyThreshold_add,ih,pow_succ]

lemma heavyThreshold_sq (n j : ℕ) : (heavyThreshold n j)^2 = (1/2:ℝ)^(n*j) := by
  rw [heavyThreshold,← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  have he : (-(n:ℝ)*(j:ℝ)/2)*(2:ℝ) = -(↑(n*j):ℝ) := by push_cast; ring
  norm_num only [Nat.cast_ofNat]
  rw [he,Real.rpow_neg (by norm_num),Real.rpow_natCast]
  simp only [one_div,inv_pow]

lemma heavyThreshold_tendsto_zero {n : ℕ} (hn : 0 < n) :
    Filter.Tendsto (heavyThreshold n) Filter.atTop (nhds 0) := by
  have hb : heavyThreshold n 1 < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    have : (0:ℝ) < n := by exact_mod_cast hn
    simp only [Nat.cast_one,mul_one]
    linarith
  convert tendsto_pow_atTop_nhds_zero_of_lt_one (heavyThreshold_pos n 1).le hb using 1
  funext j
  exact heavyThreshold_pow n j

lemma exists_heavy_cutoff {n : ℕ} (hn : 0 < n) (μ : Measure (Coordinate n))
    {C : ℝ} (hC : 0 ≤ C)
    (hdom : ∀ R : Cell n,μ.real (cellSet R) ≤ C*(1/2:ℝ)^(n*R.1)) (Q : Cell n) :
    ∃ D : ℕ,∀ j : ℕ,D < j → ∀ R : Cell n,R.1 = Q.1+j →
      μ.real (cellSet R) < heavyThreshold n j := by
  have ht : Filter.Tendsto (fun j => C*heavyThreshold n j) Filter.atTop (nhds 0) := by
    simpa using Filter.Tendsto.const_mul C (heavyThreshold_tendsto_zero hn)
  obtain ⟨D,hD⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)))
  refine ⟨D,fun j hj R hR => ?_⟩
  have hpow : (1/2:ℝ)^(n*R.1) ≤ (1/2:ℝ)^(n*j) := by
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    apply Nat.mul_le_mul_left
    omega
  have hd := (hdom R).trans (mul_le_mul_of_nonneg_left hpow hC)
  rw [← heavyThreshold_sq] at hd
  have hsmall := hD j hj.le
  have hm := mul_lt_mul_of_pos_right hsmall (heavyThreshold_pos n j)
  nlinarith

lemma deepHeavyDepth_maximal {n : ℕ} (μ : Measure (Coordinate n)) (Q : Cell n) (D : ℕ)
    (hD : ∀ j : ℕ,D < j → ∀ R : Cell n,R.1 = Q.1+j → μ.real (cellSet R) < heavyThreshold n j)
    (z : Coordinate n) {j : ℕ} (h : heavyThreshold n j ≤ μ.real (cellSet (cellAt (Q.1+j) z))) :
    j ≤ deepHeavyDepth μ Q D z := by
  apply le_deepHeavyDepth
  · by_contra hj
    exact (not_le_of_gt (hD j (by omega) (cellAt (Q.1+j) z) rfl)) h
  · exact h

lemma selected_inter_heavy_descendant_empty {n : ℕ} (hn : 0 < n)
    (μ : Measure (Coordinate n)) (Q : Cell n) (D : ℕ)
    (hD : ∀ j : ℕ,D < j → ∀ R : Cell n,R.1 = Q.1+j → μ.real (cellSet R) < heavyThreshold n j)
    {R R' : Cell n} {j l : ℕ} (hR : R.1 = Q.1+j) (hR' : R'.1 = R.1+l)
    (hl : 0 < l) (heavy : heavyThreshold n (j+l) ≤ μ.real (cellSet R')) :
    {z | z ∈ cellSet Q ∧ deepHeavyCell μ Q D z = R} ∩ cellSet R' = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro z ⟨⟨hz,he⟩,hz'⟩
  have he' : Q.1+deepHeavyDepth μ Q D z = Q.1+j := by
    simpa only [deepHeavyCell_level μ Q D hz, hR] using congrArg Sigma.fst he
  have hcan : cellAt (Q.1+(j+l)) z = R' := by
    have hlev : Q.1+(j+l) = R'.1 := by omega
    rw [hlev,cellAt_eq_of_mem hn R' hz']
  have hmax := deepHeavyDepth_maximal μ Q D hD z (show heavyThreshold n (j+l) ≤ μ.real (cellSet (cellAt (Q.1+(j+l)) z)) by rwa [hcan])
  omega

lemma measurable_heavySelectionEvent {n : ℕ} (μ : Measure (Coordinate n))
    (Q : Cell n) (D : ℕ) (R : Cell n) :
    MeasurableSet {z | z ∈ cellSet Q ∧ deepHeavyCell μ Q D z = R} := by
  exact (measurableSet_cellSet Q).inter ((measurable_deepHeavyCell μ Q D) (measurableSet_singleton R))

lemma selected_posterior_spread {n : ℕ} (hn : 0 < n)
    (μ : Measure (Coordinate n)) [IsProbabilityMeasure μ] (Q : Cell n) (D : ℕ)
    (hD : ∀ j : ℕ,D < j → ∀ R : Cell n,R.1 = Q.1+j → μ.real (cellSet R) < heavyThreshold n j)
    {R : Cell n} {j : ℕ} (hR : R.1 = Q.1+j)
    (hP : 0 < μ.real {z | z ∈ cellSet Q ∧ deepHeavyCell μ Q D z = R}) :
    DyadicSpread (cond μ {z | z ∈ cellSet Q ∧ deepHeavyCell μ Q D z = R}) R
      (max 1 (heavyThreshold n j / μ.real {z | z ∈ cellSet Q ∧ deepHeavyCell μ Q D z = R})) := by
  let S := {z | z ∈ cellSet Q ∧ deepHeavyCell μ Q D z = R}
  have hS := measurable_heavySelectionEvent μ Q D R
  have hSn : μ S ≠ 0 := by
    intro h
    have hz : μ.real S = 0 := by simp [measureReal_def,h]
    exact (ne_of_gt hP) hz
  have : IsProbabilityMeasure (cond μ S) := cond_isProbabilityMeasure_of_finite hSn (measure_ne_top _ _)
  intro l R' hR' _
  have hB0 : 0 ≤ max 1 (heavyThreshold n j/μ.real S) := le_trans (by norm_num) (le_max_left _ _)
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (mul_nonneg hB0 (heavyThreshold_pos n l).le)).mpr
  change (cond μ S).real (cellSet R') ≤ max 1 (heavyThreshold n j/μ.real S)*heavyThreshold n l
  by_cases hl : l = 0
  · rw [hl,heavyThreshold_zero,mul_one]
    exact (measureReal_mono (Set.subset_univ _) ).trans (by simp)
  · have hbound : μ.real (S ∩ cellSet R') ≤ heavyThreshold n (j+l) := by
      by_cases hh : heavyThreshold n (j+l) ≤ μ.real (cellSet R')
      · have he := selected_inter_heavy_descendant_empty hn μ Q D hD hR hR' (by omega) hh
        rw [show S ∩ cellSet R' = ∅ from he]
        simp only [measureReal_empty]
        exact (heavyThreshold_pos n (j+l)).le
      · exact (measureReal_mono Set.inter_subset_right).trans (le_of_not_ge hh)
    rw [measureReal_def,cond_apply hS,ENNReal.toReal_mul,ENNReal.toReal_inv]
    change (μ.real S)⁻¹*μ.real (S ∩ cellSet R') ≤ _
    calc
      _ ≤ (μ.real S)⁻¹*heavyThreshold n (j+l) := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hP.le)
      _ = (heavyThreshold n j/μ.real S)*heavyThreshold n l := by rw [heavyThreshold_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (heavyThreshold_pos n l).le

lemma cellSet_disjoint_of_level_eq {n : ℕ} (hn : 0 < n) {R R' : Cell n}
    (h : R.1 = R'.1) (hne : R ≠ R') : Disjoint (cellSet R) (cellSet R') := by
  rcases R with ⟨J,a⟩
  rcases R' with ⟨K,b⟩
  dsimp at h
  subst K
  apply cellSet_disjoint hn
  intro hab
  exact hne (congrArg (Sigma.mk J) hab)

lemma heavy_cell_weight_budget {n : ℕ} (hn : 0 < n) (μ : Measure (Coordinate n))
    [IsProbabilityMeasure μ] (Q : Cell n) (D : ℕ) (s : Finset (Cell n))
    (hlo : ∀ R ∈ s,Q.1 ≤ R.1) (hhi : ∀ R ∈ s,R.1 ≤ Q.1+D)
    (hheavy : ∀ R ∈ s,heavyThreshold n (R.1-Q.1) ≤ μ.real (cellSet R))
    (g : ℕ → ℝ) (hg : ∀ j,0 ≤ g j) (hgs : ∑ j ∈ Finset.range (D+1),g j ≤ 1) :
    (∑ R ∈ s,heavyThreshold n (R.1-Q.1)*g (R.1-Q.1)) ≤ 1 := by
  classical
  have hm : ∀ R ∈ s,R.1-Q.1 ∈ Finset.range (D+1) := by
    intro R hR
    apply Finset.mem_range.mpr
    have := hhi R hR
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hm]
  apply le_trans (Finset.sum_le_sum (fun j _ => ?_)) hgs
  let sj := s.filter (fun R => R.1-Q.1 = j)
  have hin : ∀ R ∈ sj,R.1 = Q.1+j := by
    intro R hR
    have h := Finset.mem_filter.mp hR
    have hl := hlo R h.1
    omega
  have hd : (↑sj : Set (Cell n)).PairwiseDisjoint cellSet := by
    intro R hR R' hR' hne
    exact cellSet_disjoint_of_level_eq hn ((hin R hR).trans (hin R' hR').symm) hne
  have hsum : ∑ R ∈ sj,μ.real (cellSet R) ≤ 1 := by
    simpa using sum_measureReal_le_measureReal_univ
      (μ := μ) (fun R _ => measurableSet_cellSet R) hd
  calc
    _ ≤ ∑ R ∈ sj,μ.real (cellSet R)*g j := by
      apply Finset.sum_le_sum
      intro R hR
      have he := (Finset.mem_filter.mp hR).2
      rw [he]
      exact mul_le_mul_of_nonneg_right (by simpa only [he] using hheavy R (Finset.mem_filter.mp hR).1) (hg j)
    _ = (∑ R ∈ sj,μ.real (cellSet R))*g j := (Finset.sum_mul ..).symm
    _ ≤ 1*g j := mul_le_mul_of_nonneg_right hsum (hg j)
    _ = g j := one_mul _

lemma heavy_selection_range_properties {n : ℕ} (hn : 0 < n)
    (μ : Measure (Coordinate n)) (Q : Cell n) (hQ : μ.real (cellSet Q) = 1) (D : ℕ)
    {R : Cell n} (hR : R ∈ Set.range (deepHeavyCell μ Q D)) :
    Q.1 ≤ R.1 ∧ R.1 ≤ Q.1+D ∧ heavyThreshold n (R.1-Q.1) ≤ μ.real (cellSet R) := by
  rcases hR with ⟨z,rfl⟩
  by_cases hz : z ∈ cellSet Q
  · have hl := deepHeavyCell_level μ Q D hz
    have he : (deepHeavyCell μ Q D z).1-Q.1 = deepHeavyDepth μ Q D z := by omega
    refine ⟨by omega,by have := deepHeavyDepth_le μ Q D z; omega,?_⟩
    rw [he,deepHeavyCell,ite_eq_left hz]
    exact deepHeavyDepth_heavy hn μ Q hQ D hz
  · simp only [deepHeavyCell,ite_eq_right hz,Nat.sub_self,heavyThreshold_zero,hQ,le_refl,and_true]
    exact ⟨trivial, Nat.le_add_right _ _⟩

end RepeatedLocalization

end OAI

import OAI.Analysis.DiskMaximal.RunCancellation

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace ActualLabels
open FiniteLabels DyadicHats Finset

lemma row_change_le_rate (h : ℂ → ℂ) (r : ℝ) (x : ℂ) (n : Label) :
    expect (row h r x n) (fun j => if j = n then 0 else 1) ≤ rate h r x n := by
  rw [row,spatialRow_expect]
  simp only [ite_true,sub_zero,zero_add]
  apply interpolate_mono
  intro z
  split_ifs <;> simp [switchChance_nonneg]

lemma observation_startReward_le (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ)
    (J : ℕ → ℝ) (hJ : ∀ k, 0 ≤ J k) (k : ℕ) :
    expect (before h r old x k)
      (fun n => expect (observation h r k x n) (SignedRuns.startReward J k n)) ≤
      switchCost h r x k*J k := by
  cases k with
  | zero =>
    change (expect (delta old) fun _ => expect (initial h (r 0) x) (fun _ => J 0)) ≤ 1*J 0
    rw [FiniteLabels.expect_const,FiniteLabels.expect_const,one_mul]
  | succ k =>
    change expect (marginal h r k x) (fun n => expect (row h (r (k+1)) x n)
      (fun j => if j = n then 0 else J (k+1))) ≤ _
    have he (n : Label) : (fun j : Label => if j = n then (0:ℝ) else J (k+1)) =
        fun j => J (k+1)*(if j = n then 0 else 1) := by funext j; split_ifs <;> simp
    simp_rw [he,FiniteLabels.expect_mul]
    rw [switchCost,mul_comm _ (J (k+1))]
    apply mul_le_mul_of_nonneg_left _ (hJ _)
    exact expect_mono _ (fun n => row_change_le_rate h (r (k+1)) x n)

end ActualLabels

namespace ActualLabels
open FiniteLabels Finset

def boundaryCost (h : ℂ → ℂ) (r : ℕ → ℝ) (x : ℂ) (m k : ℕ) : ℝ :=
  switchCost h r x k+(if k=m then 1 else switchCost h r x (k+1))

lemma boundaryCost_nonneg (h : ℂ → ℂ) (r : ℕ → ℝ) (x : ℂ) (m k : ℕ) :
    0 ≤ boundaryCost h r x m k := by
  unfold boundaryCost
  apply add_nonneg (switchCost_nonneg h r x k)
  split_ifs
  · exact zero_le_one
  · exact switchCost_nonneg h r x (k+1)

lemma observation_boundaryReward_le (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ)
    (J : ℕ → ℝ) (hJ : ∀ k, 0 ≤ J k) (k : ℕ) :
    expect (before h r old x k)
      (fun n => expect (observation h r k x n) (SignedRuns.boundaryReward J k n)) ≤
      (match k with | 0 => J 0 | l+1 => switchCost h r x (l+1)*(J l+J (l+1))) := by
  cases k with
  | zero =>
    change (expect (delta old) fun _ => expect (initial h (r 0) x) (fun _ => J 0)) ≤ J 0
    rw [FiniteLabels.expect_const,FiniteLabels.expect_const]
  | succ k =>
    change expect (marginal h r k x) (fun n => expect (row h (r (k+1)) x n)
      (fun j => if j = n then 0 else J k+J (k+1))) ≤ _
    have he (n : Label) : (fun j : Label => if j = n then (0:ℝ) else J k+J (k+1)) =
        fun j => (J k+J (k+1))*(if j = n then 0 else 1) := by funext j; split_ifs <;> simp
    simp_rw [he,FiniteLabels.expect_mul]
    rw [switchCost,mul_comm _ (J k+J (k+1))]
    apply mul_le_mul_of_nonneg_left _ (add_nonneg (hJ _) (hJ _))
    exact expect_mono _ (fun n => row_change_le_rate h (r (k+1)) x n)

lemma boundary_reward_sum (h : ℂ → ℂ) (r : ℕ → ℝ) (x : ℂ) (J : ℕ → ℝ) (m : ℕ) :
    (∑ k ∈ range (m+1), (match k with | 0 => J 0 | l+1 => switchCost h r x (l+1)*(J l+J (l+1))))+J m =
      ∑ k ∈ range (m+1), boundaryCost h r x m k*J k := by
  induction m with
  | zero => simp [boundaryCost,switchCost]; ring
  | succ m ih =>
    conv_lhs => rw [sum_range_succ]
    conv_rhs => rw [sum_range_succ]
    have he : (∑ k ∈ range (m+1), boundaryCost h r x (m+1) k*J k) =
        (∑ k ∈ range (m+1), boundaryCost h r x m k*J k)+
          (switchCost h r x (m+1)-1)*J m := by
      conv_lhs => rw [sum_range_succ]
      conv_rhs => rw [sum_range_succ]
      have hh : (∑ k ∈ range m, boundaryCost h r x (m+1) k*J k) =
          ∑ k ∈ range m, boundaryCost h r x m k*J k := by
        apply sum_congr rfl
        intro k hk
        have hk' := mem_range.mp hk
        simp only [boundaryCost,ite_eq_right (by omega : k ≠ m+1),ite_eq_right (by omega : k ≠ m)]
      rw [hh]
      simp only [boundaryCost,ite_eq_right (by omega : m ≠ m+1),ite_true]
      ring
    rw [he,← ih]
    simp only [boundaryCost,ite_true]
    ring
end ActualLabels

namespace SignedRuns
open ActualLabels FiniteLabels Finset

lemma expected_start_sum_bound (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ)
    (J : ℕ → ℝ) (hJ : ∀ k, 0 ≤ J k) (m : ℕ) :
    leafSum (fun q => weight h r old x q*((runs q).map fun a => J a.first).sum) (m+1) [] ≤
      ∑ k ∈ range (m+1), switchCost h r x k*J k := by
  simp_rw [run_start_sum J old]
  rw [leafSum_pathReward]
  exact sum_le_sum (fun k _ => observation_startReward_le h r old x J hJ k)

lemma expected_boundary_sum_bound (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ)
    (J : ℕ → ℝ) (hJ : ∀ k, 0 ≤ J k) (m : ℕ) :
    leafSum (fun q => weight h r old x q*((runs q).map fun a => J a.first+J a.last).sum) (m+1) [] ≤
      ∑ k ∈ range (m+1), boundaryCost h r x m k*J k := by
  have he := leafSum_congr
    (fun q => weight h r old x q*((runs q).map fun a => J a.first+J a.last).sum)
    (fun q => weight h r old x q*pathReward old (boundaryReward J) q+weight h r old x q*J m)
    (m+1) [] (by
      intro q hq
      cases q with
      | nil => simp at hq
      | cons n p =>
        have hp : p.length = m := by simpa using hq
        rw [run_boundary_sum J old, hp,mul_add])
  rw [he,leafSum_add,leafSum_pathReward,leafSum_mul_const,leafSum_weight,weight,one_mul]
  rw [← boundary_reward_sum]
  exact add_le_add (sum_le_sum (fun k _ => observation_boundaryReward_le h r old x J hJ k)) le_rfl

lemma expected_span_sum (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ)
    (H : ℕ → Label → ℝ) (m : ℕ) :
    leafSum (fun q => weight h r old x q*((runs q).map fun a => ∑ k ∈ Icc a.first a.last, H k a.dir).sum) (m+1) [] =
      ∑ k ∈ range (m+1), expect (marginal h r k x) (H k) := by
  simp_rw [run_span_sum H old]
  rw [leafSum_pathReward]
  apply sum_congr rfl
  intro k _
  rw [← expect_move,← before_move]
  rfl

end SignedRuns

namespace PhysicalCells
open DyadicHats DirectionNeighbors CommonPrices Finset

def gridIndex (r : ℝ) (y : ℂ) : ℤ × ℤ := (⌊y.re/r⌋,⌊y.im/r⌋)

lemma toUnit_point_re (r : ℝ) (hr : r ≠ 0) (p : ℤ × ℤ) (y : ℂ) :
    (toUnit (point r p) r y).re = y.re/r-p.1 := by
  simp only [toUnit,Complex.smul_re,Complex.sub_re,point,smul_eq_mul]
  field_simp

lemma toUnit_point_im (r : ℝ) (hr : r ≠ 0) (p : ℤ × ℤ) (y : ℂ) :
    (toUnit (point r p) r y).im = y.im/r-p.2 := by
  simp only [toUnit,Complex.smul_im,Complex.sub_im,point,smul_eq_mul]
  field_simp

lemma mem_index_cell {r : ℝ} (hr : 0 < r) (y : ℂ) :
    y ∈ cell (point r (gridIndex r y)) r := by
  change (toUnit _ r y).re ∈ Set.Ico (0:ℝ) 1 ∧ (toUnit _ r y).im ∈ Set.Ico (0:ℝ) 1
  rw [toUnit_point_re r hr.ne',toUnit_point_im r hr.ne']
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · exact sub_nonneg.mpr (Int.floor_le _)
  · dsimp only [gridIndex]; linarith [Int.lt_floor_add_one (y.re/r)]
  · exact sub_nonneg.mpr (Int.floor_le _)
  · dsimp only [gridIndex]; linarith [Int.lt_floor_add_one (y.im/r)]

lemma cells_cover {r : ℝ} (hr : 0 < r) : (⋃ p : ℤ × ℤ, cell (point r p) r) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  exact Set.mem_iUnion.mpr ⟨gridIndex r y,mem_index_cell hr y⟩

lemma mem_cell_box {r : ℝ} (hr : 0 < r) {p : ℤ × ℤ} {y : ℂ}
    (hy : y ∈ cell (point r p) r) : boxNorm (y-point r p) ≤ r := by
  change (toUnit _ r y).re ∈ Set.Ico (0:ℝ) 1 ∧ (toUnit _ r y).im ∈ Set.Ico (0:ℝ) 1 at hy
  rw [toUnit_point_re r hr.ne',toUnit_point_im r hr.ne'] at hy
  have h (a : ℝ) (b : ℤ) (hab : a/r-b ∈ Set.Ico (0:ℝ) 1) : |a-r*b| ≤ r := by
    have hl : (b:ℝ) ≤ a/r := by linarith [hab.1]
    have hu : a/r < (b:ℝ)+1 := by linarith [hab.2]
    have hl' := (le_div_iff₀ hr).mp hl
    have hu' := (div_lt_iff₀ hr).mp hu
    apply abs_le.mpr
    constructor <;> nlinarith
  exact max_le (h y.re p.1 hy.1) (h y.im p.2 hy.2)

lemma cell_subset_root_neighborhood {N : ℕ} {r : ℝ} (hr : 0 < r)
    (p : ℤ × ℤ) (q : Grid N) (hq : q ∈ cellRoots N p) :
    cell (point r p) r ⊆ neighborhood r q := by
  intro y hy
  have hqp : boxNorm (point r p-point r q) ≤ 20*r := by
    rw [boxNorm_sub_comm]
    exact (mem_window_iff hr 20 p q).mp (mem_filter.mp hq).2
  have hb := boxNorm_add_le (y-point r p) (point r p-point r q)
  rw [sub_add_sub_cancel] at hb
  have hc := mem_cell_box hr hy
  change boxNorm (y-point r q) ≤ 25*r
  linarith

lemma lintegral_le_cells {r : ℝ} (hr : 0 < r) (F : ℂ → ℝ≥0∞) :
    (∫⁻ y, F y) ≤ ∑' p : ℤ × ℤ, ∫⁻ y in cell (point r p) r, F y := by
  have h := lintegral_iUnion_le (μ := (volume : Measure ℂ)) (fun p : ℤ × ℤ => cell (point r p) r) F
  simpa only [cells_cover hr,Measure.restrict_univ] using h

lemma tsum_ofReal_le {ι : Type*} (B : ι → ℝ) (hB : ∀ i, 0 ≤ B i) (A : ℝ)
    (hbudget : ∀ s : Finset ι, ∑ i ∈ s, B i ≤ A) :
    (∑' i, ENNReal.ofReal (B i)) ≤ ENNReal.ofReal A := by
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro s
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hB i)]
  exact ENNReal.ofReal_le_ofReal (hbudget s)

/-- Global integration over the actual full lattice. The budget is tested on
arbitrary finite sets, so neither support cutoffs nor omitted cells enter. -/
lemma integral_cell_budget {r : ℝ} (hr : 0 < r) (F : ℂ → ℝ≥0∞)
    (B : (ℤ × ℤ) → ℝ) (hB : ∀ p, 0 ≤ B p) (A : ℝ)
    (hcell : ∀ p, (∫⁻ y in cell (point r p) r, F y) ≤ ENNReal.ofReal (B p))
    (hbudget : ∀ s : Finset (ℤ × ℤ), ∑ p ∈ s, B p ≤ A) :
    (∫⁻ y, F y) ≤ ENNReal.ofReal A :=
  (lintegral_le_cells hr F).trans ((ENNReal.tsum_le_tsum hcell).trans (tsum_ofReal_le B hB A hbudget))

end PhysicalCells

namespace CommonPrices
open DyadicHats DirectionNeighbors Finset ConeCoordinates

lemma cellRoots_budget {N : ℕ} (B : Grid N → ℝ) (hB : ∀ q, 0 ≤ B q)
    (P : Finset (ℤ × ℤ)) :
    (∑ p ∈ P, ∑ q ∈ cellRoots N p, B q) ≤ 1681*∑ q, B q := by
  simp only [cellRoots,sum_filter]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply sum_le_sum
  intro q _
  have hs : P.filter (fun p => (q:ℤ×ℤ) ∈ window 20 p) ⊆ window 20 q := by
    intro p hp
    exact (mem_window_comm 20 _ _).mp (mem_filter.mp hp).2
  have hc : ((P.filter (fun p => (q:ℤ×ℤ) ∈ window 20 p)).card : ℝ) ≤ 1681 := by
    have hc := Finset.card_le_card hs
    rw [card_window] at hc
    exact_mod_cast hc
  rw [← sum_filter,sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right hc (hB q)

lemma badPrice_nonneg {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (S : Finset (Grid N)) (n : ℂ) :
    0 ≤ badPrice h r k S n := sum_nonneg (fun _ _ => norm_nonneg _)

lemma badPrice_le_rootMass {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (S : Finset (Grid N)) (n : ℂ) :
    badPrice h r k S n ≤ rootMass h r k S := by
  classical
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => norm_nonneg _)
end CommonPrices

namespace ActualLabels
open DyadicHats DirectionNeighbors FiniteLabels CommonPrices ConeCoordinates Finset

lemma marginal_localSup_nonneg (h : ℂ → ℂ) (r : ℕ → ℝ) (k : ℕ) (hr : 0 < r k)
    (p : ℤ × ℤ) (n : Label) : 0 ≤ localSup (fun x => marginal h r k x n) (r k) p :=
  localSup_nonneg hr.le p (fun x => (marginal h r k x).nonneg n) (fun _ _ => law_le_one _ _)

lemma marginal_localSup_le_one (h : ℂ → ℂ) (r : ℕ → ℝ) (k : ℕ) (hr : 0 < r k)
    (p : ℤ × ℤ) (n : Label) : localSup (fun x => marginal h r k x n) (r k) p ≤ 1 :=
  localSup_le hr.le p (fun _ _ => law_le_one _ _)

lemma marginal_localSup_bad_zero {N : ℕ} (h : ℂ → ℂ) (r : ℕ → ℝ) (k : ℕ) (hr : 0 < r k)
    (p : ℤ × ℤ) (q : Grid N) (hq : q ∈ cellRoots N p)
    (hE : energy h (r k) q ≤ (1/1000:ℝ)^2) (n : Label)
    (hn : ¬Good (n:ℂ) (theta h (r k) q)) : localSup (fun x => marginal h r k x n) (r k) p = 0 := by
  apply le_antisymm _ (marginal_localSup_nonneg h r k hr p n)
  apply localSup_le hr.le p
  intro y hy
  have hqp : boxNorm (point (r k) p-point (r k) q) ≤ 20*r k := by
    rw [boxNorm_sub_comm]
    exact (mem_window_iff hr 20 p q).mp (mem_filter.mp hq).2
  have hb := boxNorm_add_le (y-point (r k) p) (point (r k) p-point (r k) q)
  rw [sub_add_sub_cancel] at hb
  have hy' : boxNorm (y-point (r k) p) ≤ 25*r k := hy
  rw [marginal_bad_zero h r k hr q (by linarith) hE n hn]

/-- The actual bad-root charge is paid by geometric energy, not a separately
assumed probability budget. -/
lemma marginal_badPrice_bound {N : ℕ} (h : ℂ → ℂ) (r : ℕ → ℝ) (base : ℝ)
    (k j : ℕ) (hr : 0 < r k) (hrj : r k = scale base j) (p : ℤ × ℤ) (n : Label) :
    localSup (fun x => marginal h r k x n) (r k) p*badPrice h base j (cellRoots N p) n ≤
      1000000*∑ q ∈ cellRoots N p, scalarMass h (r k) q*energy h (r k) q := by
  classical
  have hp0 := marginal_localSup_nonneg h r k hr p n
  have hp1 := marginal_localSup_le_one h r k hr p n
  unfold badPrice
  rw [mul_sum]
  calc
    _ ≤ ∑ q ∈ badRoots h base j (cellRoots N p) n,
        1000000*(scalarMass h (r k) q*energy h (r k) q) := by
      apply sum_le_sum
      intro q hq
      have hqp := (mem_filter.mp hq).1
      have hbad : ¬Good (n:ℂ) (theta h (r k) q) := by
        simpa only [hrj] using (mem_filter.mp hq).2
      rw [← hrj]
      by_cases hE : energy h (r k) q ≤ (1/1000:ℝ)^2
      · rw [marginal_localSup_bad_zero h r k hr p q hqp hE n hbad,zero_mul]
        exact mul_nonneg (by norm_num) (mul_nonneg (norm_nonneg _) (energy_nonneg _ _ _))
      · have he : 1 ≤ 1000000*energy h (r k) q := by norm_num at hE; linarith
        have hb := mul_le_mul_of_nonneg_right hp1 (norm_nonneg (vectorMass h (r k) q))
        have hc := mul_le_mul_of_nonneg_right he (norm_nonneg (vectorMass h (r k) q))
        dsimp only [scalarMass] at ⊢
        nlinarith
    _ ≤ _ := by
      rw [mul_sum]
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun q _ _ =>
        mul_nonneg (by norm_num) (mul_nonneg (norm_nonneg _) (energy_nonneg _ _ _)))
end ActualLabels

namespace PhysicalCells
open DyadicHats Finset

/-- Measurable full-lattice patch; no choice of maximizing radius occurs. -/
def patch (r : ℝ) (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (x : ℂ) : ℝ≥0∞ :=
  ∑' p, (cell (point r p) r).indicator (F p) x

lemma patch_measurable (r : ℝ) (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (hF : ∀ p, Measurable (F p)) :
    Measurable (patch r F) :=
  Measurable.tsum (fun p => (hF p).indicator (cell_measurable _ _))

lemma le_patch (r : ℝ) (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (p : ℤ × ℤ) {x : ℂ}
    (hx : x ∈ cell (point r p) r) : F p x ≤ patch r F x := by
  have he := ENNReal.le_tsum (f := fun q => (cell (point r q) r).indicator (F q) x) p
  simpa only [patch,Set.indicator_of_mem hx] using he

lemma lintegral_patch (r : ℝ) (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (hF : ∀ p, Measurable (F p)) :
    (∫⁻ x, patch r F x) = ∑' p, ∫⁻ x in cell (point r p) r, F p x := by
  simp only [patch]
  rw [lintegral_tsum (f := fun p x => (cell (point r p) r).indicator (F p) x) (fun p => ((hF p).indicator (cell_measurable _ _)).aemeasurable)]
  simp_rw [lintegral_indicator (cell_measurable _ _)]

lemma lintegral_patch_budget (r : ℝ) (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (hF : ∀ p, Measurable (F p))
    (B : (ℤ × ℤ) → ℝ) (hB : ∀ p, 0 ≤ B p) (A : ℝ)
    (hcell : ∀ p, (∫⁻ x in cell (point r p) r, F p x) ≤ ENNReal.ofReal (B p))
    (hbudget : ∀ P : Finset (ℤ × ℤ), ∑ p ∈ P, B p ≤ A) :
    (∫⁻ x, patch r F x) ≤ ENNReal.ofReal A := by
  rw [lintegral_patch r F hF]
  exact (ENNReal.tsum_le_tsum hcell).trans (tsum_ofReal_le B hB A hbudget)

lemma patch_finite (r : ℝ) (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (hF : ∀ p, Measurable (F p))
    {A : ℝ} (hi : (∫⁻ x, patch r F x) ≤ ENNReal.ofReal A) :
    ∀ᵐ x, patch r F x ≠ ⊤ := by
  exact (ae_lt_top (patch_measurable r F hF) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hi)).mono
    (fun _ hx => hx.ne)

lemma patch_integrable (r : ℝ) (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (hF : ∀ p, Measurable (F p))
    {A : ℝ} (hi : (∫⁻ x, patch r F x) ≤ ENNReal.ofReal A) :
    Integrable (fun x => (patch r F x).toReal) :=
  integrable_toReal_of_lintegral_ne_top (patch_measurable r F hF).aemeasurable
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hi)

lemma real_le_patch {r : ℝ} (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (p : ℤ × ℤ) {x : ℂ}
    (hx : x ∈ cell (point r p) r) (hf : patch r F x ≠ ⊤) {a : ℝ}
    (hb : ENNReal.ofReal a ≤ F p x) : a ≤ (patch r F x).toReal := by
  exact (le_max_left a 0).trans (by
    rw [← ENNReal.toReal_ofReal']
    exact (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hf).mpr (hb.trans (le_patch r F p hx)))

/-- Take the cell supremum of a weight only after the local price has been
proved. This is the common production rule for all three spatial budgets. -/
lemma weighted_patch_bound (r : ℝ) (F : (ℤ × ℤ) → ℂ → ℝ≥0∞) (hF : ∀ p, Measurable (F p))
    (W : ℂ → ℝ≥0∞) (hW : Measurable W) (A B : (ℤ × ℤ) → ℝ)
    (hA : ∀ p, 0 ≤ A p) (_hB : ∀ p, 0 ≤ B p)
    (hcell : ∀ p, (∫⁻ x in cell (point r p) r, F p x) ≤ ENNReal.ofReal (B p))
    (hWB : ∀ p x, x ∈ cell (point r p) r → W x ≤ ENNReal.ofReal (A p)) :
    (∫⁻ x, W x*patch r F x) ≤ ∑' p, ENNReal.ofReal (A p*B p) := by
  simp only [patch,← ENNReal.tsum_mul_left]
  rw [lintegral_tsum (f := fun p x => W x*(cell (point r p) r).indicator (F p) x) (fun p => (hW.mul ((hF p).indicator (cell_measurable _ _))).aemeasurable)]
  apply ENNReal.tsum_le_tsum
  intro p
  have he : (fun x => W x*(cell (point r p) r).indicator (F p) x) =
      (cell (point r p) r).indicator (fun x => W x*F p x) := by
    funext x
    by_cases hx : x ∈ cell (point r p) r <;> simp [hx]
  rw [he,lintegral_indicator (cell_measurable _ _)]
  calc
    _ ≤ ∫⁻ x in cell (point r p) r, ENNReal.ofReal (A p)*F p x := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (cell_measurable (point r p) r)] with x hx
      exact mul_le_mul' (hWB p x hx) le_rfl
    _ = ENNReal.ofReal (A p)*(∫⁻ x in cell (point r p) r, F p x) :=
      lintegral_const_mul _ (hF p)
    _ ≤ ENNReal.ofReal (A p)*ENNReal.ofReal (B p) := mul_le_mul' le_rfl (hcell p)
    _ = _ := (ENNReal.ofReal_mul (hA p)).symm
end PhysicalCells

namespace ActualLabels
open DyadicHats FiniteLabels GeometricFilter Finset

/-- Global geometric extension of the finite descending radius grid. -/
def geometricRadii (base : ℝ) (m : ℕ) (k : ℕ) : ℝ := scale base m/(2:ℝ)^k
lemma geometricRadii_pos {base : ℝ} (hb : 0 < base) (m k : ℕ) :
    0 < geometricRadii base m k := div_pos (scale_pos hb m) (by positivity)
lemma geometricRadii_step (base : ℝ) (m k : ℕ) :
    2*geometricRadii base m (k+1) = geometricRadii base m k := by
  unfold geometricRadii
  rw [pow_succ]
  field_simp
lemma geometricRadii_eq (base : ℝ) {m k : ℕ} (hk : k ≤ m) :
    geometricRadii base m k = scale base (m-k) := by
  unfold geometricRadii scale
  rw [show m = (m-k)+k by omega,pow_add]
  field_simp
  rw [show m-k+k-k = m-k by omega]
  ring

lemma marginal_congr (h : ℂ → ℂ) (r s : ℕ → ℝ) (k : ℕ)
    (hrs : ∀ i, i ≤ k → r i = s i) (x : ℂ) : marginal h r k x = marginal h s k x := by
  induction k with
  | zero => simp only [marginal,hrs 0 le_rfl]
  | succ k ih =>
    simp only [marginal,hrs (k+1) le_rfl,ih (fun i hi => hrs i (by omega))]

lemma switchCost_congr (h : ℂ → ℂ) (r s : ℕ → ℝ) (k : ℕ)
    (hrs : ∀ i, i ≤ k → r i = s i) (x : ℂ) : switchCost h r x k = switchCost h s x k := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [switchCost,hrs (k+1) le_rfl,marginal_congr h r s k (fun i hi => hrs i (by omega)) x]

lemma derivativeCost_congr (h : ℂ → ℂ) (r s : ℕ → ℝ) (k : ℕ)
    (hrs : ∀ i, i ≤ k → r i = s i) (x : ℂ) : derivativeCost h r x k = derivativeCost h s x k := by
  cases k with
  | zero => simp only [derivativeCost,hrs 0 le_rfl]
  | succ k =>
    simp only [derivativeCost,hrs (k+1) le_rfl,marginal_congr h r s k (fun i hi => hrs i (by omega)) x]

lemma cellCost_congr (h : ℂ → ℂ) (r s : ℕ → ℝ) (m l : ℕ) (hl : l ≤ m)
    (hrs : ∀ i, i ≤ m → r i = s i) (q : ℤ × ℤ) : cellCost h r m l q = cellCost h s m l q := by
  have hsw (i : ℕ) (hi : i ≤ m) : (fun x => switchCost h r x i) = fun x => switchCost h s x i := by
    funext x
    exact switchCost_congr h r s i (fun j hj => hrs j (by omega)) x
  have hdc (i : ℕ) (hi : i ≤ m) : (fun x => derivativeCost h r x i) = fun x => derivativeCost h s x i := by
    funext x
    exact derivativeCost_congr h r s i (fun j hj => hrs j (by omega)) x
  unfold cellCost
  rw [hrs l hl,hsw l hl]
  congr 1
  · split_ifs with he
    · rfl
    · rw [hsw (l+1) (by omega)]
  · rw [filt_sum,filt_sum]
    apply sum_congr rfl
    intro i hi
    rw [hdc i (by have := mem_range.mp hi; omega)]
end ActualLabels

namespace SignedRuns
open ActualLabels FiniteLabels Finset DiskMoments PhysicalCells SignedAssembly

lemma run_cone_bound {g : ℂ → ℝ} {r : ℕ → ℝ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (hr : ∀ k, 0 < r k) (hstep : ∀ k, 2*r (k+1) = r k)
    (H : ℕ → Label → ℝ) (J : ℕ → ℝ) (hH : ∀ k n, 0 ≤ H k n) (hJ : ∀ k, 0 ≤ J k)
    (x : ℂ) (n : Label) (p : List Label)
    (hd : ∀ i j, i ≤ j → DifferentiableAt ℝ (runEnvelope g r i j) x)
    (hinterior : ∀ k n t, PhysicalNeighborhoodRadius g (r k) x t →
      unfavorable n (gradient (fun y => signedAverage g y t) x) ≤ H k n)
    (hend : ∀ k t, PhysicalEndpointRadius g (r k) x t →
      ‖gradient (fun y => signedAverage g y t) x‖ ≤ J k) :
    ((runs (n::p)).map fun a => coneContribution a.dir (gradient (runEnvelope g r a.first a.last) x)).sum ≤
      divergence (fun y => potential g r y (n::p)) x+
      ((runs (n::p)).map fun a => J a.first).sum+
      ((runs (n::p)).map fun a => ∑ k ∈ Icc a.first a.last, H k a.dir).sum+
      2*((runs (n::p)).map fun a => J a.first+J a.last).sum := by
  rw [potential_divergence hg hc hr (n::p) x hd]
  rw [← List.sum_map_mul_left,← List.sum_map_add,← List.sum_map_add,← List.sum_map_add]
  apply List.sum_le_sum
  intro a ha
  have hab := runs_bounds n p a ha
  have hu := run_unfavorable_bound hg hc hr hstep H J hH hJ x a.dir hab.1
    (hd _ _ hab.1) (hinterior · a.dir ·) hend
  have hb := hend a.first (r a.first) ⟨⟨le_rfl,by linarith [hr a.first]⟩,Or.inl rfl⟩
  have hi := real_inner_le_norm (a.dir:ℂ) (gradient (fun y => signedAverage g y (r a.first)) x)
  rw [label_unit,one_mul] at hi
  simp only [inner_sub_right]
  unfold coneContribution unfavorable at *
  linarith

/-- Complete pointwise signed assembly, still retaining the divergence term.
The remaining terms are exactly the direct directional and boundary costs. -/
theorem pointwise_signed_master {g : ℂ → ℝ} (h : ℂ → ℂ) {r : ℕ → ℝ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (hr : ∀ k, 0 < r k) (hstep : ∀ k, 2*r (k+1) = r k)
    (H : ℕ → Label → ℝ) (J : ℕ → ℝ) (hH : ∀ k n, 0 ≤ H k n) (hJ : ∀ k, 0 ≤ J k)
    (old : Label) (m : ℕ) (x : ℂ)
    (hd : ∀ i j, i ≤ j → DifferentiableAt ℝ (runEnvelope g r i j) x)
    (hinterior : ∀ k n t, PhysicalNeighborhoodRadius g (r k) x t →
      unfavorable n (gradient (fun y => signedAverage g y t) x) ≤ H k n)
    (hend : ∀ k t, PhysicalEndpointRadius g (r k) x t →
      ‖gradient (fun y => signedAverage g y t) x‖ ≤ J k) :
    ‖gradient (runEnvelope g r 0 m) x‖ ≤ 12*(
      leafSum (fun q => weight h r old x q*divergence (fun y => potential g r y q) x) (m+1) []+
      (∑ k ∈ range (m+1), expect (marginal h r k x) (H k))+
      3*(∑ k ∈ range (m+1), boundaryCost h r x m k*J k)) := by
  have hh := leafSum_mono
    (fun q => weight h r old x q*((runs q).map fun a => coneContribution a.dir
      (gradient (runEnvelope g r a.first a.last) x)).sum)
    (fun q => weight h r old x q*divergence (fun y => potential g r y q) x+
      weight h r old x q*((runs q).map fun a => J a.first).sum+
      weight h r old x q*((runs q).map fun a => ∑ k ∈ Icc a.first a.last, H k a.dir).sum+
      2*(weight h r old x q*((runs q).map fun a => J a.first+J a.last).sum)) (m+1) [] (by
        intro q hq
        cases q with
        | nil => simp at hq
        | cons n p =>
          have hh := mul_le_mul_of_nonneg_left
            (run_cone_bound hg hc hr hstep H J hH hJ x n p hd hinterior hend)
            (weight_nonneg h r old x (n::p))
          nlinarith only [hh])
  rw [leafSum_add,leafSum_add,leafSum_add,leafSum_const_mul,expected_span_sum] at hh
  have hb := expected_boundary_sum_bound h r old x J hJ m
  have hs := expected_start_sum_bound h r old x J hJ m
  have hsb : (∑ k ∈ range (m+1), switchCost h r x k*J k) ≤
      ∑ k ∈ range (m+1), boundaryCost h r x m k*J k := by
    apply sum_le_sum
    intro k _
    apply mul_le_mul_of_nonneg_right _ (hJ k)
    unfold boundaryCost
    have hn : 0 ≤ if k=m then (1:ℝ) else switchCost h r x (k+1) := by
      split_ifs
      · exact zero_le_one
      · exact switchCost_nonneg h r x (k+1)
    linarith
  have hm := expected_run_master g h r hg hc hr hstep old m x hd
  linarith
end SignedRuns

namespace PhysicalCells
open DyadicHats
lemma center_mem_cell (p : ℂ) (r : ℝ) : p ∈ cell p r := by
  simp [cell,toUnit,unitCell]
noncomputable def cellSup (f : ℂ → ℝ) (r : ℝ) (p : ℤ × ℤ) : ℝ :=
  sSup (f '' cell (point r p) r)
lemma cellSup_le {f : ℂ → ℝ} {r A : ℝ} (p : ℤ × ℤ)
    (h : ∀ x ∈ cell (point r p) r, f x ≤ A) : cellSup f r p ≤ A := by
  apply csSup_le (Set.Nonempty.image f ⟨point r p,center_mem_cell _ _⟩)
  rintro z ⟨x,hx,rfl⟩
  exact h x hx
lemma le_cellSup {f : ℂ → ℝ} {r A : ℝ} (p : ℤ × ℤ)
    (h : ∀ x ∈ cell (point r p) r, f x ≤ A) {x : ℂ} (hx : x ∈ cell (point r p) r) :
    f x ≤ cellSup f r p := le_csSup ⟨A,by rintro z ⟨y,hy,rfl⟩; exact h y hy⟩ ⟨x,hx,rfl⟩
lemma cellSup_nonneg {f : ℂ → ℝ} {r A : ℝ} (p : ℤ × ℤ)
    (h0 : ∀ x, 0 ≤ f x) (h : ∀ x ∈ cell (point r p) r, f x ≤ A) : 0 ≤ cellSup f r p :=
  (h0 (point r p)).trans (le_cellSup p h (center_mem_cell _ _))
end PhysicalCells

namespace ActualLabels
open DyadicHats GeometricFilter PhysicalCells CommonPrices DirectionNeighbors FiniteLabels Finset

def pointCost (h : ℂ → ℂ) (r : ℕ → ℝ) (x : ℂ) (m k : ℕ) : ℝ :=
  boundaryCost h r x m k+filt (fun i => derivativeCost h r x i) k

def costLimit : ℝ := 2+32*(Fintype.card Label:ℝ)
lemma costLimit_pos : 0 < costLimit := by dsimp [costLimit]; positivity
lemma pointCost_nonneg (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (x : ℂ) (m k : ℕ) :
    0 ≤ pointCost h r x m k := add_nonneg (boundaryCost_nonneg h r x m k)
      (filt_nonneg (fun i => derivativeCost_nonneg h r x i (hr i).le) k)
lemma pointCost_le (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (x : ℂ) (m k : ℕ) :
    pointCost h r x m k ≤ costLimit := by
  have hs0 := switchCost_le_one h r x k
  have hs1 := switchCost_le_one h r x (k+1)
  have ht := filt_le (by positivity : (0:ℝ) ≤ 16*(Fintype.card Label:ℝ))
    (fun i => derivativeCost_uniform h r x i (hr i)) k
  dsimp [pointCost,boundaryCost,costLimit]
  split_ifs <;> linarith

lemma pointCost_le_cellCost (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (m k : ℕ) (q : ℤ × ℤ) (x : ℂ) (hx : x ∈ neighborhood (r k) q) :
    pointCost h r x m k ≤ cellCost h r m k q := by
  have hs (i : ℕ) : switchCost h r x i ≤ localSup (fun y => switchCost h r y i) (r k) q :=
    le_localSup q (fun y _ => switchCost_le_one h r y i) hx
  have ht (i : ℕ) : derivativeCost h r x i ≤ localSup (fun y => derivativeCost h r y i) (r k) q :=
    le_localSup q (fun y _ => derivativeCost_uniform h r y i (hr i)) hx
  have hf := filt_mono ht k
  dsimp [pointCost,boundaryCost,cellCost]
  split_ifs <;> linarith [hs k,hs (k+1)]

lemma cellSup_pointCost_le {N : ℕ} (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (m k : ℕ) (p : ℤ × ℤ) (q : Grid N) (hq : q ∈ cellRoots N p) :
    cellSup (fun x => pointCost h r x m k) (r k) p ≤ cellCost h r m k q := by
  apply cellSup_le p
  intro x hx
  exact pointCost_le_cellCost h r hr m k q x (cell_subset_root_neighborhood (hr k) p q hq hx)

lemma cellSup_pointCost_nonneg (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (m k : ℕ) (p : ℤ × ℤ) : 0 ≤ cellSup (fun x => pointCost h r x m k) (r k) p :=
  cellSup_nonneg p (fun x => pointCost_nonneg h r hr x m k) (fun x _ => pointCost_le h r hr x m k)
lemma cellSup_pointCost_uniform (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (m k : ℕ) (p : ℤ × ℤ) : cellSup (fun x => pointCost h r x m k) (r k) p ≤ costLimit :=
  cellSup_le p (fun x _ => pointCost_le h r hr x m k)

lemma pointCost_cell_budget {N : ℕ} (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (base : ℝ) (m k j : ℕ) (hrj : r k = scale base j) (P : Finset (ℤ × ℤ)) :
    (∑ p ∈ P, cellSup (fun x => pointCost h r x m k) (r k) p*
      rootMass h base j (cellRoots N p)) ≤
        1681*∑ q : Grid N, scalarMass h (r k) q*cellCost h r m k q := by
  calc
    _ ≤ ∑ p ∈ P, ∑ q ∈ cellRoots N p, scalarMass h (r k) q*cellCost h r m k q := by
      apply sum_le_sum
      intro p _
      unfold rootMass
      rw [mul_sum]
      apply sum_le_sum
      intro q hq
      rw [← hrj,mul_comm]
      exact mul_le_mul_of_nonneg_left (cellSup_pointCost_le h r hr m k p q hq) (norm_nonneg _)
    _ ≤ _ := cellRoots_budget _ (fun q => mul_nonneg (norm_nonneg _) (cellCost_nonneg h r hr m k q)) P
end ActualLabels

namespace CommonPrices
open DyadicHats ConeCoordinates Finset

def priceConstant : ℝ := 1681*((fixedPalette.labels.card:ℝ)*2/(1-rho))
lemma priceConstant_nonneg : 0 ≤ priceConstant := by
  unfold priceConstant
  exact mul_nonneg (by norm_num) (div_nonneg (by positivity) (by linarith [rho_lt_one]))
lemma cellPrice_nonneg {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (S : Finset (Grid N)) :
    0 ≤ cellPrice N r h k S := sum_nonneg (fun q _ => rootPrice_nonneg hr hR hN hh hsupp k q)
lemma rootMass_cell_budget {N : ℕ} {h : ℂ → ℂ} (hh : Integrable h) (r : ℝ)
    (k : ℕ) (P : Finset (ℤ × ℤ)) :
    (∑ p ∈ P, rootMass h r k (cellRoots N p)) ≤ 1681*(∫ y, ‖h y‖) := by
  exact (cellRoots_budget _ (fun q => norm_nonneg (vectorMass h (scale r k) q)) P).trans
    (mul_le_mul_of_nonneg_left (sum_scalarMass_grid_le hh _) (by norm_num))
end CommonPrices

namespace ActualLabels
open DyadicHats GeometricFilter PhysicalCells CommonPrices DirectionNeighbors FiniteLabels Finset ActualMarkTrees

lemma geometricRadii_reverse (base : ℝ) {m j : ℕ} (hj : j ≤ m) :
    geometricRadii base m (m-j) = scale base j := by
  rw [geometricRadii_eq base (Nat.sub_le m j),Nat.sub_sub_self hj]

lemma pointCost_mass_budget {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R)
    (hN : R/base+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (m : ℕ) (P : ℕ → Finset (ℤ × ℤ)) :
    (∑ j ∈ range (m+1), ∑ p ∈ P j,
      cellSup (fun x => pointCost h (geometricRadii base m) x m (m-j)) (scale base j) p*
        rootMass h base j (cellRoots N p)) ≤ 1681*packingConstant*(∫ y, ‖h y‖) := by
  have he : (∑ j ∈ range (m+1), ∑ q : Grid N, scalarMass h (scale base j) q*
        cellCost h (geometricRadii base m) m (m-j) q) =
      ∑ j ∈ range (m+1), ∑ q : Grid N, scalarMass h (scale base j) q*
        cellCost h (fun i => scale base (m-i)) m (m-j) q := by
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro q _
    rw [cellCost_congr h _ _ m (m-j) (Nat.sub_le m j)
      (fun i hi => geometricRadii_eq base hi)]
  calc
    _ ≤ ∑ j ∈ range (m+1), 1681*∑ q : Grid N, scalarMass h (scale base j) q*
        cellCost h (geometricRadii base m) m (m-j) q := by
      apply sum_le_sum
      intro j hj
      have hjm : j ≤ m := by have := mem_range.mp hj; omega
      have ht := pointCost_cell_budget (N := N) h (geometricRadii base m) (geometricRadii_pos hb m)
        base m (m-j) j (geometricRadii_reverse base hjm) (P j)
      simpa only [geometricRadii_reverse base hjm] using ht
    _ = 1681*(∑ j ∈ range (m+1), ∑ q : Grid N, scalarMass h (scale base j) q*
        cellCost h (geometricRadii base m) m (m-j) q) := by rw [mul_sum]
    _ ≤ _ := by
      rw [he,mul_assoc]
      exact mul_le_mul_of_nonneg_left (spatial_packing hb hR hN hh hsupp m) (by norm_num)

lemma pointCost_price_budget {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R)
    (hN : R/base+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (m : ℕ) (P : ℕ → Finset (ℤ × ℤ)) :
    (∑ j ∈ range (m+1), ∑ p ∈ P j,
      cellSup (fun x => pointCost h (geometricRadii base m) x m (m-j)) (scale base j) p*
        cellPrice N base h j (cellRoots N p)) ≤ costLimit*priceConstant*(∫ y, ‖h y‖) := by
  calc
    _ ≤ ∑ j ∈ range (m+1), ∑ p ∈ P j, costLimit*cellPrice N base h j (cellRoots N p) := by
      apply sum_le_sum
      intro j hj
      have hjm : j ≤ m := by have := mem_range.mp hj; omega
      apply sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_right _ (cellPrice_nonneg hb hR hN hh hsupp j _)
      rw [← geometricRadii_reverse base hjm]
      exact cellSup_pointCost_uniform h _ (geometricRadii_pos hb m) m (m-j) p
    _ = costLimit*(∑ j ∈ range (m+1), ∑ p ∈ P j, cellPrice N base h j (cellRoots N p)) := by
      simp only [mul_sum]
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (cellPrice_budget hb hR hN hh hsupp m P) costLimit_pos.le

lemma marginal_bad_budget {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R)
    (hN : R/base+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (m : ℕ) (P : ℕ → Finset (ℤ × ℤ)) (n : Label) :
    (∑ j ∈ range (m+1), ∑ p ∈ P j,
      localSup (fun x => marginal h (geometricRadii base m) (m-j) x n) (scale base j) p*
        badPrice h base j (cellRoots N p) n) ≤
      (1000000*1681*(576*(4097:ℝ)^2))*(∫ y, ‖h y‖) := by
  calc
    _ ≤ ∑ j ∈ range (m+1), 1000000*1681*∑ q : Grid N,
        scalarMass h (scale base j) q*energy h (scale base j) q := by
      apply sum_le_sum
      intro j hj
      have hjm : j ≤ m := by have := mem_range.mp hj; omega
      calc
        _ ≤ ∑ p ∈ P j, 1000000*∑ q ∈ cellRoots N p,
            scalarMass h (scale base j) q*energy h (scale base j) q := by
          apply sum_le_sum
          intro p _
          have ht := marginal_badPrice_bound (N := N) h (geometricRadii base m) base (m-j) j
            (geometricRadii_pos hb m (m-j)) (geometricRadii_reverse base hjm) p n
          simpa only [geometricRadii_reverse base hjm] using ht
        _ ≤ _ := by
          rw [← mul_sum,mul_assoc]
          exact mul_le_mul_of_nonneg_left (cellRoots_budget _
            (fun q => mul_nonneg (norm_nonneg _) (energy_nonneg _ _ _)) (P j)) (by norm_num)
    _ ≤ _ := by
      rw [← mul_sum]
      have ht := mul_le_mul_of_nonneg_left (neighbor_energy_budget hb hR hN hh hsupp (m+1))
        (by norm_num : (0:ℝ) ≤ 1000000*1681)
      nlinarith only [ht]

lemma marginal_price_budget {N : ℕ} {base R : ℝ} (hb : 0 < base) (hR : 0 ≤ R)
    (hN : R/base+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (m : ℕ) (P : ℕ → Finset (ℤ × ℤ)) (n : Label) :
    (∑ j ∈ range (m+1), ∑ p ∈ P j,
      localSup (fun x => marginal h (geometricRadii base m) (m-j) x n) (scale base j) p*
        cellPrice N base h j (cellRoots N p)) ≤ priceConstant*(∫ y, ‖h y‖) := by
  apply le_trans _ (cellPrice_budget hb hR hN hh hsupp m P)
  apply sum_le_sum
  intro j hj
  have hjm : j ≤ m := by have := mem_range.mp hj; omega
  apply sum_le_sum
  intro p _
  have hbnd : localSup (fun x => marginal h (geometricRadii base m) (m-j) x n) (scale base j) p ≤ 1 := by
    rw [← geometricRadii_reverse base hjm]
    exact marginal_localSup_le_one h _ (m-j) (geometricRadii_pos hb m (m-j)) p n
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hbnd (cellPrice_nonneg hb hR hN hh hsupp j _)
end ActualLabels

end

end OAI

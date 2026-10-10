import OAI.Analysis.SignedDisk.DiskMoments1

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace SignedRuns
open ActualLabels FiniteLabels Finset

lemma leafSum_succ_last {E : Type*} [AddCommMonoid E] (f : List Label → E)
    (m : ℕ) (p : List Label) :
    leafSum f (m+1) p = leafSum (fun q => ∑ n, f (n::q)) m p := by
  induction m generalizing p with
  | zero => rfl
  | succ m ih =>
    change (∑ n, leafSum f (m+1) (n::p)) =
      ∑ n, leafSum (fun q => ∑ j, f (j::q)) m (n::p)
    simp_rw [ih]

lemma leafSum_sum {E : Type*} [AddCommMonoid E] {ι : Type*}
    (s : Finset ι) (f : ι → List Label → E) (m : ℕ) (p : List Label) :
    leafSum (fun q => ∑ i ∈ s, f i q) m p = ∑ i ∈ s, leafSum (f i) m p := by
  induction m generalizing p with
  | zero => rfl
  | succ m ih => simp only [leafSum,ih]; exact sum_comm

/-- The exact head law obtained from the genuine finite-history products. -/
lemma leafSum_headLaw (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ)
    (m : ℕ) (F : Label → ℝ) :
    leafSum (fun q => weight h r old x q*F (q.headD old)) m [] =
      expect (before h r old x m) F := by
  induction m generalizing F with
  | zero => simp only [leafSum,weight,List.headD_nil,one_mul,before,expect_delta]
  | succ m ih =>
    rw [leafSum_succ_last,before_move,expect_move]
    have he (q : List Label) :
        (∑ n, weight h r old x (n::q)*F ((n::q).headD old)) =
          weight h r old x q*expect (observation h r q.length x (q.headD old)) F := by
      simp only [weight,List.headD_cons,FiniteLabels.expect,mul_assoc,mul_sum]
    simp_rw [he]
    have hc := leafSum_congr
      (fun q => weight h r old x q*expect (observation h r q.length x (q.headD old)) F)
      (fun q => weight h r old x q*expect (observation h r m x (q.headD old)) F) m []
      (by
        intro q hq
        have hqm : q.length = m := by simpa using hq
        rw [hqm])
    rw [hc]
    exact ih (fun n => FiniteLabels.expect (observation h r m x n) F)

/-- Additive reward along a reversed history, with its true previous state. -/
def pathReward (old : Label) (A : ℕ → Label → Label → ℝ) : List Label → ℝ
  | [] => 0
  | n::p => pathReward old A p+A p.length (p.headD old) n

lemma leafSum_pathReward (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ)
    (A : ℕ → Label → Label → ℝ) (m : ℕ) :
    leafSum (fun q => weight h r old x q*pathReward old A q) m [] =
      ∑ k ∈ range m, expect (before h r old x k)
        (fun n => expect (observation h r k x n) (A k n)) := by
  induction m with
  | zero => simp [leafSum,pathReward]
  | succ m ih =>
    rw [leafSum_succ_last,sum_range_succ]
    have he (q : List Label) :
        (∑ n, weight h r old x (n::q)*pathReward old A (n::q)) =
          weight h r old x q*pathReward old A q+
            weight h r old x q*expect (observation h r q.length x (q.headD old)) (A q.length (q.headD old)) := by
      simp only [weight,pathReward,mul_add,sum_add_distrib,← sum_mul,← mul_sum,FiniteLabels.expect,mul_assoc]
      rw [(observation h r q.length x (q.headD old)).total,one_mul]
    simp_rw [he]
    rw [leafSum_add,ih]
    congr 1
    have hc := leafSum_congr
      (fun q => weight h r old x q*expect (observation h r q.length x (q.headD old)) (A q.length (q.headD old)))
      (fun q => weight h r old x q*expect (observation h r m x (q.headD old)) (A m (q.headD old))) m []
      (by
        intro q hq
        have hqm : q.length = m := by simpa using hq
        rw [hqm])
    rw [hc]
    exact leafSum_headLaw h r old x m (fun n => FiniteLabels.expect (observation h r m x n) (A m n))

lemma pathReward_add (old : Label) (A B : ℕ → Label → Label → ℝ) (q : List Label) :
    pathReward old (fun k n j => A k n j+B k n j) q =
      pathReward old A q+pathReward old B q := by
  induction q with
  | nil => simp [pathReward]
  | cons n p ih => simp only [pathReward,ih]; ring

lemma pathReward_nonneg (old : Label) (A : ℕ → Label → Label → ℝ)
    (hA : ∀ k n j, 0 ≤ A k n j) (q : List Label) : 0 ≤ pathReward old A q := by
  induction q with
  | nil => exact le_rfl
  | cons n p ih => exact add_nonneg ih (hA _ _ _)

open ActualLabels FiniteLabels Finset

lemma run_span_sum (H : ℕ → Label → ℝ) (old : Label) (p : List Label) :
    ((runs p).map fun a => ∑ k ∈ Icc a.first a.last, H k a.dir).sum =
      pathReward old (fun k _ n => H k n) p := by
  cases p with
  | nil => rfl
  | cons n p =>
    induction p generalizing n with
    | nil => simp [runs,closedRuns,activeStart,pathReward]
    | cons n' p ih =>
      by_cases hn : n = n'
      · subst n
        have hsum : (∑ k ∈ Icc (activeStart (n'::p)) (p.length+1), H k n') =
            (∑ k ∈ Icc (activeStart (n'::p)) p.length, H k n')+H (p.length+1) n' := by
          exact sum_Icc_succ_top ((activeStart_le n' p).trans (Nat.le_succ _)) _
        have hh := ih n'
        simp only [runs,List.map_cons,List.sum_cons] at hh
        simp only [runs,closedRuns,activeStart,ite_true,List.length_cons,List.map_cons,List.sum_cons,pathReward]
        rw [hsum]
        simp only [pathReward] at hh
        linarith
      · have hh := ih n'
        simp only [runs,List.map_cons,List.sum_cons] at hh
        simp only [runs,closedRuns,activeStart,hn,ite_false,List.length_cons,List.map_cons,List.sum_cons,pathReward,
          Finset.Icc_self,sum_singleton]
        simp only [pathReward] at hh
        linarith

def startReward (J : ℕ → ℝ) : ℕ → Label → Label → ℝ
  | 0,_,_ => J 0
  | k+1,n,j => if j = n then 0 else J (k+1)

def boundaryReward (J : ℕ → ℝ) : ℕ → Label → Label → ℝ
  | 0,_,_ => J 0
  | k+1,n,j => if j = n then 0 else J k+J (k+1)

lemma run_start_sum (J : ℕ → ℝ) (old : Label) (p : List Label) :
    ((runs p).map fun a => J a.first).sum = pathReward old (startReward J) p := by
  cases p with
  | nil => rfl
  | cons n p =>
    induction p generalizing n with
    | nil => simp [runs,activeStart,closedRuns,pathReward,startReward]
    | cons n' p ih =>
      have hh := ih n'
      simp only [runs,List.map_cons,List.sum_cons] at hh
      simp only [pathReward,startReward] at hh
      by_cases hn : n = n'
      · subst n
        simpa only [runs,closedRuns,activeStart,ite_true,List.length_cons,List.map_cons,List.sum_cons,
          pathReward,startReward,List.headD_cons,add_zero] using hh
      · simp only [runs,closedRuns,activeStart,hn,ite_false,List.length_cons,List.map_cons,List.sum_cons,
          pathReward,startReward,List.headD_cons]
        linarith

lemma run_boundary_sum (J : ℕ → ℝ) (old n : Label) (p : List Label) :
    ((runs (n::p)).map fun a => J a.first+J a.last).sum =
      pathReward old (boundaryReward J) (n::p)+J p.length := by
  induction p generalizing n with
  | nil => simp [runs,activeStart,closedRuns,pathReward,boundaryReward]
  | cons n' p ih =>
    have hh := ih n'
    simp only [runs,List.map_cons,List.sum_cons,pathReward,boundaryReward] at hh
    by_cases hn : n = n'
    · subst n
      simp only [runs,closedRuns,activeStart,ite_true,List.length_cons,List.map_cons,List.sum_cons,
        pathReward,boundaryReward,List.headD_cons]
      linarith
    · simp only [runs,closedRuns,activeStart,hn,ite_false,List.length_cons,List.map_cons,List.sum_cons,
        pathReward,boundaryReward,List.headD_cons]
      linarith

lemma startReward_nonneg (J : ℕ → ℝ) (hJ : ∀ k, 0 ≤ J k) (k : ℕ) (n j : Label) :
    0 ≤ startReward J k n j := by
  cases k with
  | zero => exact hJ 0
  | succ k => simp only [startReward]; split_ifs <;> first | exact le_rfl | exact hJ _

lemma boundaryReward_nonneg (J : ℕ → ℝ) (hJ : ∀ k, 0 ≤ J k) (k : ℕ) (n j : Label) :
    0 ≤ boundaryReward J k n j := by
  cases k with
  | zero => exact hJ 0
  | succ k => simp only [boundaryReward]; split_ifs <;> first | exact le_rfl | exact add_nonneg (hJ _) (hJ _)

end SignedRuns

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

end SignedDisk

end

end OAI

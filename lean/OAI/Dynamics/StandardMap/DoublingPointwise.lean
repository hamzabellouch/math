import OAI.Dynamics.StandardMap.CancellationTheorem

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
noncomputable def wingDefect (k : ℝ) (z : Torus) (n : ℕ) : ℝ :=
  (n:ℝ)-min (productDistance k z 0 (-(n:ℤ))) (productDistance k z 0 (n:ℤ))
noncomputable def cancellationLoss (k : ℝ) (z : Torus) (n : ℕ) : ℝ :=
  productDistance k z 0 (-(n:ℤ))+productDistance k z 0 (n:ℤ)-productDistance k z (-(n:ℤ)) (n:ℤ)
lemma wingDefect_nonneg (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ) : 0 ≤ wingDefect k z n := by
  have hh := productDistance_le k hk z 0 (n:ℤ)
  simp only [Int.cast_natCast,Int.cast_zero,sub_zero,Nat.abs_cast] at hh
  have hm := min_le_right (productDistance k z 0 (-(n:ℤ))) (productDistance k z 0 (n:ℤ))
  unfold wingDefect; linarith
lemma cancellationLoss_bounds (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ) :
    0 ≤ cancellationLoss k z n ∧ cancellationLoss k z n ≤ 2*(n:ℝ) := by
  have htri := productDistance_triangle k hk z (-(n:ℤ)) 0 (n:ℤ)
  rw [productDistance_symm k z (-(n:ℤ)) 0] at htri
  have hL := productDistance_le k hk z 0 (-(n:ℤ))
  have hR := productDistance_le k hk z 0 (n:ℤ)
  simp only [Int.cast_neg,Int.cast_natCast,Int.cast_zero,sub_zero,abs_neg,Nat.abs_cast] at hL hR
  have hn := productDistance_nonneg k hk z (-(n:ℤ)) (n:ℤ)
  unfold cancellationLoss
  constructor  <;> linarith
lemma torusCancellation_iff_distance (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ) :
    torusCancellation k n z ↔
      (1-1/100000000:ℝ)*(n:ℝ) ≤ productDistance k z 0 (-(n:ℤ)) ∧
      (1-1/100000000:ℝ)*(n:ℝ) ≤ productDistance k z 0 (n:ℤ) ∧
      productDistance k z (-(n:ℤ)) (n:ℤ) ≤ (1/100000000:ℝ)*(n:ℝ) := by
  have hM : 0 < growthBase k := lt_of_lt_of_le (by norm_num : (0:ℝ) < 4) (growthBase_ge_four k hk)
  have hp a m : 0 < ‖torusSegmentTransfer k z a m‖ := lt_of_lt_of_le zero_lt_one (torusSegmentTransfer_norm_bounds k hk z a m).1
  rw [productDistance_symm k z 0 (-(n:ℤ))]
  have h1 : productDistance k z (-(n:ℤ)) 0=Real.log ‖torusSegmentTransfer k z (-(n:ℤ)) n‖/Real.log (growthBase k) := by
    convert productDistance_forward k z (-(n:ℤ)) n using 1  ; simp
  have h2 : productDistance k z 0 (n:ℤ)=Real.log ‖torusSegmentTransfer k z 0 n‖/Real.log (growthBase k) := by
    simpa using productDistance_forward k z 0 n
  have h3 : productDistance k z (-(n:ℤ)) (n:ℤ)=Real.log ‖torusSegmentTransfer k z (-(n:ℤ)) (n+n)‖/Real.log (growthBase k) := by
    convert productDistance_forward k z (-(n:ℤ)) (n+n) using 1  ; push_cast  ; ring_nf
  rw [h1,h2,h3]
  simp only [torusCancellation,Real.rpow_le_iff_le_log hM (hp _ _),Real.le_rpow_iff_log_le (hp _ _) hM,
    le_div_iff₀ (log_growthBase_pos k hk),div_le_iff₀ (log_growthBase_pos k hk)]
lemma large_loss_implies_cancellation (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ)
    (hl : 10000000000*(1+wingDefect k z n) < cancellationLoss k z n) :
    let s := ⌊cancellationLoss k z n/2⌋₊
    1  ≤  s ∧ s  ≤  n ∧ cancellationLoss k z n < 2*(s:ℝ)+2 ∧ torusCancellation k s z := by
  let s := ⌊cancellationLoss k z n/2⌋₊
  change 1  ≤  s ∧ s  ≤  n ∧ cancellationLoss k z n < 2*(s:ℝ)+2 ∧ torusCancellation k s z
  have hD := wingDefect_nonneg k hk z n
  obtain ⟨hl0,hln⟩ := cancellationLoss_bounds k hk z n
  have hfloor : (s:ℝ) ≤ cancellationLoss k z n/2 := Nat.floor_le (by linarith)
  have hfloor' : cancellationLoss k z n/2 < (s:ℝ)+1 := Nat.lt_floor_add_one _
  have hs1 : 1  ≤  s := by
    have hs : (1:ℝ) ≤ s := by linarith
    exact_mod_cast hs
  have hsn : s  ≤  n := by
    have hs : (s:ℝ) ≤ n := by linarith
    exact_mod_cast hs
  have hsmall : 2*wingDefect k z n+6 ≤ (1/100000000:ℝ)*(s:ℝ) := by linarith
  refine ⟨hs1,hsn,by linarith,?_⟩
  rw [torusCancellation_iff_distance k hk z s]
  obtain ⟨hL,hR⟩ := productDistance_cut_wings k hk z 0 n s hsn
  simp only [zero_sub,zero_add] at hL hR
  change (s:ℝ)-wingDefect k z n ≤ productDistance k z 0 (-(s:ℤ)) at hL
  change (s:ℝ)-wingDefect k z n ≤ productDistance k z 0 (s:ℤ) at hR
  have hcut := productDistance_truncation k hk z 0 n s hsn
  simp only [zero_sub,zero_add] at hcut
  change min (cancellationLoss k z n) (2*(s:ℝ)-2*wingDefect k z n)-6 ≤ cancellationLoss k z s at hcut
  rw [min_eq_right (by linarith)] at hcut
  have hLs := productDistance_le k hk z 0 (-(s:ℤ))
  have hRs := productDistance_le k hk z 0 (s:ℤ)
  simp only [Int.cast_neg,Int.cast_natCast,Int.cast_zero,sub_zero,abs_neg,Nat.abs_cast] at hLs hRs
  unfold cancellationLoss at hcut
  exact ⟨by linarith,by linarith,by linarith⟩
lemma cancellationLoss_pointwise_bound (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ) :
    cancellationLoss k z n ≤ 10000000000*(1+wingDefect k z n)+
      ∑ s∈Finset.range (n+1), (if torusCancellation k s z then 2*(s:ℝ)+2 else 0) := by
  by_cases hl : cancellationLoss k z n ≤ 10000000000*(1+wingDefect k z n)
  · apply hl.trans
    have hh : 0 ≤ ∑ s∈Finset.range (n+1), (if torusCancellation k s z then 2*(s:ℝ)+2 else 0) :=
      Finset.sum_nonneg fun s hs => by split_ifs  <;> positivity
    linarith
  · obtain ⟨hs1,hsn,hls,hcan⟩ := large_loss_implies_cancellation k hk z n (lt_of_not_ge hl)
    let s := ⌊cancellationLoss k z n/2⌋₊
    have hsum := Finset.single_le_sum (f:=fun s : ℕ => if torusCancellation k s z then 2*(s:ℝ)+2 else 0)
      (fun i hi => by split_ifs  <;> positivity) (show s∈Finset.range (n+1) by simpa only [Finset.mem_range] using Nat.lt_succ_of_le hsn)
    rw [ite_eq_left hcan] at hsum
    have hD := wingDefect_nonneg k hk z n
    linarith
end StandardMapEntropy

end OAI

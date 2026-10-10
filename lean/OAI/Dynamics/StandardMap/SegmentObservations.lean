import OAI.Dynamics.StandardMap.CurveCellIntegral

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy
noncomputable def liftSegmentCoefficient (k : ℝ) (z : ℝ × ℝ) (a : ℤ) (i : ℕ) : ℝ :=
  potential k (liftIter k (a+(i:ℤ)-1) z).1
noncomputable def liftSegmentTransfer (k : ℝ) (z : ℝ × ℝ) (a : ℤ) (n : ℕ) : ℂ →L[ℝ] ℂ :=
  transferProduct (liftSegmentCoefficient k z a) n
noncomputable def liftShortfall (k : ℝ) (z : ℝ × ℝ) (a : ℤ) (n : ℕ) : ℝ :=
  1-Real.log ‖liftSegmentTransfer k z a n‖/((n:ℝ)*Real.log (growthBase k))
lemma liftSegmentCoefficient_bound (k : ℝ) (hk : 0 ≤ k) (z : ℝ × ℝ) (a : ℤ) (i : ℕ) :
    |liftSegmentCoefficient k z a i|+1 ≤ growthBase k := potential_bound k _ hk
lemma liftSegmentTransfer_eq (k : ℝ) (z : ℝ × ℝ) (a : ℤ) (n : ℕ) :
    liftSegmentTransfer k z a n=transferProduct
      (orbitCoefficient k (liftIter k a z).2 (liftIter k a z).1) n := by
  unfold liftSegmentTransfer
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [transferProduct,ih]
    congr 2
    unfold liftSegmentCoefficient orbitCoefficient
    rw [show a+((n+1:ℕ):ℤ)-1=(n:ℤ)+a by push_cast; ring,liftIter_add,liftIter_nat]
lemma liftSegmentCoefficient_near (k : ℝ) (hk : 0 ≤ k) (z w : ℝ × ℝ) (a b : ℤ)
    (i r : ℕ) (hwin : (a+(i:ℤ)-1-b).natAbs ≤ r) :
    |liftSegmentCoefficient k z a i-liftSegmentCoefficient k w a i| ≤
      (2*Real.pi*growthBase k)*(growthBase k^r*dist (liftIter k b z) (liftIter k b w)) := by
  have hM : 1 ≤ growthBase k := by have := growthBase_ge_four k hk; linarith
  have hshift (v : ℝ × ℝ) : liftIter k (a+(i:ℤ)-1) v=
      liftIter k (a+(i:ℤ)-1-b) (liftIter k b v) := by
    rw [← liftIter_add]; congr 1; ring
  have hdist := liftIter_lipschitz k hk (a+(i:ℤ)-1-b) (liftIter k b z) (liftIter k b w)
  have hfst : |(liftIter k (a+(i:ℤ)-1) z).1-(liftIter k (a+(i:ℤ)-1) w).1| ≤
      growthBase k^r*dist (liftIter k b z) (liftIter k b w) := by
    rw [← Real.dist_eq]
    calc
      _ ≤ dist (liftIter k (a+(i:ℤ)-1) z) (liftIter k (a+(i:ℤ)-1) w) := by
        rw [Prod.dist_eq]; exact le_max_left _ _
      _ ≤ growthBase k^(a+(i:ℤ)-1-b).natAbs*dist (liftIter k b z) (liftIter k b w) := by
        rw [hshift z,hshift w]; exact hdist
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM hwin) dist_nonneg
  exact (potential_lipschitz k _ _ hk).trans
    (mul_le_mul_of_nonneg_left hfst (by have := growthBase_ge_four k hk; positivity))
lemma liftShortfall_transport (k : ℝ) (hk : 0 ≤ k) (z w : ℝ × ℝ) (a b : ℤ)
    (n r : ℕ) (hn : 0 < n)
    (hwin : ∀ i, 1 ≤ i → i ≤ n → (a+(i:ℤ)-1-b).natAbs ≤ r) :
    |liftShortfall k z a n-liftShortfall k w a n| ≤
      ((2*Real.pi*growthBase k)/Real.log (growthBase k))*growthBase k^(r+n)*
        dist (liftIter k b z) (liftIter k b w) := by
  have hM : 1 < growthBase k := by have := growthBase_ge_four k hk; linarith
  have hp : 0 < Real.log (growthBase k) := Real.log_pos hM
  have hnp : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hδ : 0 ≤ (2*Real.pi*growthBase k)*(growthBase k^r*dist (liftIter k b z) (liftIter k b w)) := by positivity
  have hh := transfer_log_difference_bound (liftSegmentCoefficient k z a) (liftSegmentCoefficient k w a)
    (growthBase k) _ n hM.le hδ
    (fun i _ _ => liftSegmentCoefficient_bound k hk z a i)
    (fun i _ _ => liftSegmentCoefficient_bound k hk w a i)
    (fun i hi hin => liftSegmentCoefficient_near k hk z w a b i r (hwin i hi hin))
  unfold liftShortfall
  rw [sub_sub_sub_comm,sub_self,zero_sub,abs_neg,← sub_div,abs_div,
    abs_of_pos (mul_pos hnp hp)]
  calc
    _ ≤ ((n:ℝ)*((2*Real.pi*growthBase k)*(growthBase k^r*dist (liftIter k b z) (liftIter k b w)))*growthBase k^n)/
        ((n:ℝ)*Real.log (growthBase k)) := div_le_div_of_nonneg_right hh (mul_pos hnp hp).le
    _ = _ := by rw [pow_add]; field_simp
lemma liftSegmentTransfer_norm_bounds (k : ℝ) (hk : 0 ≤ k) (z : ℝ × ℝ) (a : ℤ) (n : ℕ) :
    1 ≤ ‖liftSegmentTransfer k z a n‖ ∧ ‖liftSegmentTransfer k z a n‖ ≤ growthBase k^n :=
  transferProduct_norm_bounds _ _ _ (by have := growthBase_ge_four k hk; linarith)
    (fun i _ _ => liftSegmentCoefficient_bound k hk z a i)
lemma liftShortfall_mem (k : ℝ) (hk : 0 ≤ k) (z : ℝ × ℝ) (a : ℤ) (n : ℕ) (hn : 0 < n) :
    liftShortfall k z a n ∈ Icc 0 1 := by
  have hM : 1 < growthBase k := by have := growthBase_ge_four k hk; linarith
  have hp : 0 < Real.log (growthBase k) := Real.log_pos hM
  have hnp : (0:ℝ) < n := Nat.cast_pos.mpr hn
  obtain ⟨hlo,hhi⟩ := liftSegmentTransfer_norm_bounds k hk z a n
  have hlog0 : 0 ≤ Real.log ‖liftSegmentTransfer k z a n‖ := Real.log_nonneg hlo
  have hlog1 : Real.log ‖liftSegmentTransfer k z a n‖ ≤ (n:ℝ)*Real.log (growthBase k) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by linarith) hhi
  unfold liftShortfall
  constructor
  · have := (div_le_one (mul_pos hnp hp)).mpr hlog1; linarith
  · have := div_nonneg hlog0 (mul_pos hnp hp).le; linarith
end StandardMapEntropy

end OAI

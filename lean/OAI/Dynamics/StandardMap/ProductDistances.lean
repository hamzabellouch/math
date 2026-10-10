import OAI.Dynamics.StandardMap.BiCocycle

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma torusTransfer_inverse (k : ℝ) (z : Torus) (i j : ℤ) (u : ℂ) :
    torusTransfer k z j i (torusTransfer k z i j u)=u := by
  rw [torusTransfer_comp]
  change (torusTransfer k z i i).toContinuousLinearMap u=u
  rw [torusTransfer_self]; rfl
lemma torusTransfer_norm_symm (k : ℝ) (z : Torus) (i j : ℤ) :
    ‖(torusTransfer k z i j).toContinuousLinearMap‖=‖(torusTransfer k z j i).toContinuousLinearMap‖ :=
  (torusTransfer_area k z i j).norm_inverse (torusTransfer_area k z j i) (torusTransfer_inverse k z j i) (torusTransfer_inverse k z i j)
lemma torusTransfer_one_le_norm (k : ℝ) (z : Torus) (i j : ℤ) :
    1≤‖(torusTransfer k z i j).toContinuousLinearMap‖ :=
  (torusTransfer_area k z i j).singular_pair.choose_spec.2.2.2.2
lemma torusTransfer_norm_pos (k : ℝ) (z : Torus) (i j : ℤ) :
    0<‖(torusTransfer k z i j).toContinuousLinearMap‖ := lt_of_lt_of_le zero_lt_one (torusTransfer_one_le_norm k z i j)
lemma torusTransfer_norm_le (k : ℝ) (hk : 0≤k) (z : Torus) (i j : ℤ) :
    ‖(torusTransfer k z i j).toContinuousLinearMap‖ ≤ growthBase k^(j-i).natAbs := by
  wlog hij : i≤j generalizing i j
  · rw [torusTransfer_norm_symm]
    convert this j i (le_of_not_ge hij) using 1
    rw [show i-j=-(j-i) by ring,Int.natAbs_neg]
  have hn : i+((j-i).natAbs:ℤ)=j := by rw [Int.natCast_natAbs,abs_of_nonneg (sub_nonneg.mpr hij)]; ring
  calc
    _ = ‖torusSegmentTransfer k z i (j-i).natAbs‖ := by rw [← torusTransfer_forward,hn]
    _ ≤ _ := (torusSegmentTransfer_norm_bounds k hk z i _).2
noncomputable def productDistance (k : ℝ) (z : Torus) (i j : ℤ) : ℝ :=
  Real.log ‖(torusTransfer k z i j).toContinuousLinearMap‖/Real.log (growthBase k)
lemma log_growthBase_pos (k : ℝ) (hk : 0≤k) : 0<Real.log (growthBase k) :=
  Real.log_pos (lt_of_lt_of_le (by norm_num : (1:ℝ)<4) (growthBase_ge_four k hk))
lemma productDistance_symm (k : ℝ) (z : Torus) (i j : ℤ) :
    productDistance k z i j=productDistance k z j i := by
  unfold productDistance; rw [torusTransfer_norm_symm]
@[simp] lemma productDistance_self (k : ℝ) (z : Torus) (i : ℤ) : productDistance k z i i=0 := by
  simp [productDistance,torusTransfer_self]
lemma productDistance_nonneg (k : ℝ) (hk : 0≤k) (z : Torus) (i j : ℤ) : 0≤productDistance k z i j :=
  div_nonneg (Real.log_nonneg (torusTransfer_one_le_norm k z i j)) (log_growthBase_pos k hk).le
lemma productDistance_le (k : ℝ) (hk : 0≤k) (z : Torus) (i j : ℤ) :
    productDistance k z i j≤|(j:ℝ)-(i:ℝ)| := by
  apply (div_le_iff₀ (log_growthBase_pos k hk)).mpr
  have hh := Real.log_le_log (torusTransfer_norm_pos k z i j) (torusTransfer_norm_le k hk z i j)
  rw [Real.log_pow] at hh
  have he : ((j-i).natAbs:ℝ)=|(j:ℝ)-(i:ℝ)| := by
    have hh := congrArg (fun a : ℤ => (a:ℝ)) (Int.natCast_natAbs (j-i))
    simpa only [Int.cast_natCast,Int.cast_abs,Int.cast_sub] using hh
  simpa only [he] using hh
lemma productDistance_triangle (k : ℝ) (hk : 0≤k) (z : Torus) (i j l : ℤ) :
    productDistance k z i l≤productDistance k z i j+productDistance k z j l := by
  have hc : (torusTransfer k z i l).toContinuousLinearMap=
      (torusTransfer k z j l).toContinuousLinearMap.comp (torusTransfer k z i j).toContinuousLinearMap := by
    ext u; exact (torusTransfer_comp k z i j l u).symm
  have hh := ContinuousLinearMap.opNorm_comp_le (torusTransfer k z j l).toContinuousLinearMap
    (torusTransfer k z i j).toContinuousLinearMap
  rw [← hc] at hh
  have hlog := Real.log_le_log (torusTransfer_norm_pos k z i l) hh
  rw [Real.log_mul (torusTransfer_norm_pos k z j l).ne' (torusTransfer_norm_pos k z i j).ne'] at hlog
  unfold productDistance
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by linarith) (log_growthBase_pos k hk).le
lemma productDistance_forward (k : ℝ) (z : Torus) (i : ℤ) (n : ℕ) :
    productDistance k z i (i+(n:ℤ))=Real.log ‖torusSegmentTransfer k z i n‖/Real.log (growthBase k) := by
  simp only [productDistance,torusTransfer_forward]
lemma productDistance_shift (k : ℝ) (z : Torus) (i j a : ℤ) :
    productDistance k (torusIter k a z) i j=productDistance k z (i+a) (j+a) := by
  wlog hij : i≤j generalizing i j
  · rw [productDistance_symm k _ i j,productDistance_symm k _ (i+a) (j+a)]
    exact this j i (le_of_not_ge hij)
  have hn : i+((j-i).toNat:ℤ)=j := by rw [Int.toNat_of_nonneg (sub_nonneg.mpr hij)]; ring
  have hn' : i+a+((j-i).toNat:ℤ)=j+a := by omega
  rw [← hn,productDistance_forward]
  conv_rhs => rw [show i+((j-i).toNat:ℤ)+a=i+a+((j-i).toNat:ℤ) by ring]
  rw [productDistance_forward,torusSegmentTransfer_shift]
lemma continuous_productDistance (k : ℝ) (hk : 0≤k) (i j : ℤ) :
    Continuous (fun z => productDistance k z i j) := by
  wlog hij : i≤j generalizing i j
  · have hh := this j i (le_of_not_ge hij)
    simpa only [productDistance_symm k _ j i] using hh
  have hn : i+((j-i).toNat:ℤ)=j := by rw [Int.toNat_of_nonneg (sub_nonneg.mpr hij)]; ring
  rw [← hn]
  simp only [productDistance_forward]
  apply Continuous.div_const
  exact (continuous_torusSegmentTransfer k i _).norm.log (fun z => by
    have := (torusSegmentTransfer_norm_bounds k hk z i (j-i).toNat).1; linarith)
lemma transfer_distance_fourpoint (k : ℝ) (hk : 0≤k) (z : Torus) (i j l p : ℤ) :
    productDistance k z j p-productDistance k z i j-productDistance k z i p ≤
      max (productDistance k z j l-productDistance k z i j-productDistance k z i l)
        (productDistance k z l p-productDistance k z i l-productDistance k z i p)+
        Real.log 6/Real.log (growthBase k) := by
  let A := fun j => (torusTransfer k z i j).toContinuousLinearMap
  let T := fun j p => (torusTransfer k z p j).toContinuousLinearMap
  let R := fun j p => ‖T j p‖/(‖A j‖*‖A p‖)
  have hR : ∀ j p, 0<R j p := fun j p => div_pos (torusTransfer_norm_pos k z p j)
    (mul_pos (torusTransfer_norm_pos k z i j) (torusTransfer_norm_pos k z i p))
  have hc := normalized_transfer_fourpoint A T (fun j => torusTransfer_area k z i j)
    (fun j p => torusTransfer_area k z p j) (fun j p u => torusTransfer_comp k z i p j u) j l p
  change R j p≤6*max (R j l) (R l p) at hc
  have he (j p : ℤ) : Real.log (R j p)/Real.log (growthBase k)=
      productDistance k z j p-productDistance k z i j-productDistance k z i p := by
    dsimp only [R,A,T]
    rw [Real.log_div (torusTransfer_norm_pos k z p j).ne'
      (mul_pos (torusTransfer_norm_pos k z i j) (torusTransfer_norm_pos k z i p)).ne',
      Real.log_mul (torusTransfer_norm_pos k z i j).ne' (torusTransfer_norm_pos k z i p).ne',
      torusTransfer_norm_symm k z p j]
    unfold productDistance; ring
  have hm : Real.log (max (R j l) (R l p))=max (Real.log (R j l)) (Real.log (R l p)) := by
    rcases le_total (R j l) (R l p) with h | h
    · rw [max_eq_right h,max_eq_right (Real.log_le_log (hR j l) h)]
    · rw [max_eq_left h,max_eq_left (Real.log_le_log (hR l p) h)]
  have hlog := Real.log_le_log (hR j p) hc
  rw [Real.log_mul (by norm_num : (6:ℝ)≠0) (lt_of_lt_of_le (hR j l) (le_max_left _ _)).ne',hm] at hlog
  have hd := div_le_div_of_nonneg_right hlog (log_growthBase_pos k hk).le
  rw [add_div,← max_div_div_right (log_growthBase_pos k hk).le,he,he,he] at hd
  linarith
lemma log_six_div_growth_le_three (k : ℝ) (hk : 0≤k) : Real.log 6/Real.log (growthBase k)≤3 := by
  apply (div_le_iff₀ (log_growthBase_pos k hk)).mpr
  have hh := Real.log_le_log (by norm_num : (0:ℝ)<6)
    (show (6:ℝ)≤growthBase k^3 by
      have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤4) (growthBase_ge_four k hk) 3
      norm_num at hp ⊢; linarith)
  simpa only [Real.log_pow,Nat.cast_ofNat] using hh

lemma productDistance_tree (k : ℝ) (hk : 0≤k) (z : Torus) (i j l p : ℤ) :
    min (productDistance k z i j+productDistance k z i l-productDistance k z j l)
        (productDistance k z i l+productDistance k z i p-productDistance k z l p)-3 ≤
      productDistance k z i j+productDistance k z i p-productDistance k z j p := by
  have hh := transfer_distance_fourpoint k hk z i j l p
  have he := log_six_div_growth_le_three k hk
  rcases le_total (productDistance k z i j+productDistance k z i l-productDistance k z j l)
      (productDistance k z i l+productDistance k z i p-productDistance k z l p) with h | h
  · rw [min_eq_left h]
    rw [max_eq_left (by linarith)] at hh
    linarith
  · rw [min_eq_right h]
    rw [max_eq_right (by linarith)] at hh
    linarith
end StandardMapEntropy

end OAI

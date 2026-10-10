import OAI.Dynamics.StandardMap.FineArrays

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped ENNReal Classical
namespace StandardMapEntropy
noncomputable def unitDefect (d:DistanceArray) : ℝ :=
  max (arrayShortfall 0 (dyadicInt 1) d) (arrayShortfall (dyadicInt 1) (dyadicInt 2) d)+arrayJ 0 (dyadicInt 2) d
lemma continuous_unitDefect : Continuous unitDefect :=
  ((continuous_arrayShortfall _ _).max (continuous_arrayShortfall _ _)).add (continuous_arrayJ _ _)
noncomputable def cutLeft (b:ℕ) : DyadicTime := dyadicInt 1-dyadicFine b (dyadicInt 1)
noncomputable def cutRight (b:ℕ) : DyadicTime := dyadicInt 1+dyadicFine b (dyadicInt 1)
lemma cutLeft_val (b:ℕ) : (cutLeft b:ℝ)=1-1/(2:ℝ)^b := by simp [cutLeft,dyadicFine_val]
lemma cutRight_val (b:ℕ) : (cutRight b:ℝ)=1+1/(2:ℝ)^b := by simp [cutRight,dyadicFine_val]
lemma cut_order (b:ℕ) : (cutLeft b:ℝ)<(cutRight b:ℝ) := by
  rw [cutLeft_val,cutRight_val]
  have : (0:ℝ)<1/2^b := by positivity
  linarith
lemma cut_mid (b:ℕ) : dyadicMid (cutLeft b) (cutRight b)=dyadicInt 1 := by
  apply Subtype.ext
  simp only [dyadicMid_val,cutLeft_val,cutRight_val,dyadicInt_val,Int.cast_one]; ring
lemma sample_eval_int (k:ℝ) (hk:0≤k) (z:Torus) (n:ℕ) (hn:0<n) (a b:ℤ) :
    (sampleArray k hk z n hn).val (dyadicInt a) (dyadicInt b)=productDistance k z ((n:ℤ)*a) ((n:ℤ)*b)/(n:ℝ) := by
  exact rescaledDistance_aligned k z n _ _ _ _ (by simp) (by simp)
lemma truncation_array_bound (k:ℝ) (hk:0≤k) (z:Torus) (p b:ℕ) (hb:b≤p)
    (hx:unitDefect (sampleArray k hk z (2^p) (by positivity))<1/(2:ℝ)^b) :
    arrayJ 0 (dyadicInt 2) (sampleArray k hk z (2^p) (by positivity))≤
      (1/(2:ℝ)^b)*arrayJ (cutLeft b) (cutRight b) (sampleArray k hk z (2^p) (by positivity))+3/(2:ℝ)^p := by
  let n:ℕ:=2^p
  let s:ℕ:=2^(p-b)
  let d:=sampleArray k hk z n (by dsimp [n]; positivity)
  have hn:(0:ℝ)<n := by dsimp [n]; positivity
  have hs:(0:ℝ)<s := by dsimp [s]; positivity
  have hsn:s≤n := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
  have he:(n:ℝ)/(2:ℝ)^b=s := by
    dsimp [n,s]; push_cast
    rw [div_eq_mul_inv,← pow_sub₀ (2:ℝ) (by norm_num) hb]
  have he':(n:ℝ)*(1/(2:ℝ)^b)=s := by simpa [div_eq_mul_inv] using he
  have hz : dyadicInt 0 = (0:DyadicTime) := by apply Subtype.ext; norm_num
  have he0:d.val 0 (dyadicInt 1)=productDistance k z 0 n/n := by simpa [hz] using sample_eval_int k hk z n (by dsimp [n]; positivity) 0 1
  have he1:d.val (dyadicInt 1) (dyadicInt 2)=productDistance k z n (2*n)/n := by simpa [mul_comm,hz] using sample_eval_int k hk z n (by dsimp [n]; positivity) 1 2
  have he2:d.val 0 (dyadicInt 2)=productDistance k z 0 (2*n)/n := by simpa [mul_comm,hz] using sample_eval_int k hk z n (by dsimp [n]; positivity) 0 2
  have hA:arrayShortfall 0 (dyadicInt 1) d=1-productDistance k z 0 n/n := by simp only [arrayShortfall,he0,dyadicInt_val,Int.cast_one,ZeroMemClass.coe_zero,sub_zero,div_one]
  have hB:arrayShortfall (dyadicInt 1) (dyadicInt 2) d=1-productDistance k z n (2*n)/n := by simp only [arrayShortfall,he1,dyadicInt_val]; norm_num
  have hJ:arrayJ 0 (dyadicInt 2) d=(productDistance k z 0 n+productDistance k z n (2*n)-productDistance k z 0 (2*n))/(2*n) := by
    rw [arrayJ_eq _ _ (by norm_num),dyadicMid_zero_two,he0,he1,he2]
    norm_num; ring
  have hL:d.val (cutLeft b) (dyadicInt 1)=productDistance k z ((n:ℤ)-s) n/n := by
    apply rescaledDistance_aligned
    · rw [cutLeft_val,Int.cast_sub,Int.cast_natCast,Int.cast_natCast,mul_sub,mul_one,he']
    · simp
  have hR:d.val (dyadicInt 1) (cutRight b)=productDistance k z n ((n:ℤ)+s)/n := by
    apply rescaledDistance_aligned
    · simp
    · rw [cutRight_val,Int.cast_add,Int.cast_natCast,Int.cast_natCast,mul_add,mul_one,he']
  have hLR:d.val (cutLeft b) (cutRight b)=productDistance k z ((n:ℤ)-s) ((n:ℤ)+s)/n := by
    apply rescaledDistance_aligned
    · rw [cutLeft_val,Int.cast_sub,Int.cast_natCast,Int.cast_natCast,mul_sub,mul_one,he']
    · rw [cutRight_val,Int.cast_add,Int.cast_natCast,Int.cast_natCast,mul_add,mul_one,he']
  have hCJ:arrayJ (cutLeft b) (cutRight b) d=(productDistance k z ((n:ℤ)-s) n+productDistance k z n ((n:ℤ)+s)-productDistance k z ((n:ℤ)-s) ((n:ℤ)+s))/(2*s) := by
    rw [arrayJ_eq _ _ (cut_order b),cut_mid,hL,hR,hLR,cutLeft_val,cutRight_val]
    have hnB:(n:ℝ)=s*(2:ℝ)^b := (div_eq_iff (by positivity)).mp he
    rw [hnB]; field_simp; ring
  have hu:unitDefect d=max (1-productDistance k z 0 n/n) (1-productDistance k z n (2*n)/n)+arrayJ 0 (dyadicInt 2) d := by rw [unitDefect,hA,hB]
  have hD:(n:ℝ)-min (productDistance k z n 0) (productDistance k z n (2*n))=
      n*max (1-productDistance k z 0 n/n) (1-productDistance k z n (2*n)/n) := by
    rw [productDistance_symm k z n 0]
    rcases le_total (productDistance k z 0 n) (productDistance k z n (2*n)) with h|h
    · rw [min_eq_left h,max_eq_left (by linarith [div_le_div_of_nonneg_right h hn.le])]; field_simp
    · rw [min_eq_right h,max_eq_right (by linarith [div_le_div_of_nonneg_right h hn.le])]; field_simp
  have ht:=productDistance_truncation k hk z (n:ℤ) n s hsn
  simp only [sub_self,show (n:ℤ)+(n:ℤ)=2*n by ring,productDistance_symm k z (n:ℤ) 0] at ht
  have hbound:productDistance k z 0 n+productDistance k z n (2*n)-productDistance k z 0 (2*n)≤
      2*(s:ℝ)-2*((n:ℝ)-min (productDistance k z n 0) (productDistance k z n (2*n))) := by
    rw [hD]
    have hx':max (1-productDistance k z 0 n/n) (1-productDistance k z n (2*n)/n)+arrayJ 0 (dyadicInt 2) d<1/(2:ℝ)^b := by rwa [←hu]
    have hmul:=mul_lt_mul_of_pos_left hx' hn
    have hjmul:(2*n)*arrayJ 0 (dyadicInt 2) d=productDistance k z 0 n+productDistance k z n (2*n)-productDistance k z 0 (2*n) := by rw [hJ]; field_simp
    rw [he'] at hmul; nlinarith
  rw [productDistance_symm k z n 0] at hbound
  rw [min_eq_left hbound] at ht
  rw [productDistance_symm k z n ((n:ℤ)-s)] at ht
  have hncast : (n:ℝ) = (2:ℝ)^p := by simp [n]
  rw [←hncast]
  change arrayJ 0 (dyadicInt 2) d≤(1/(2:ℝ)^b)*arrayJ (cutLeft b) (cutRight b) d+3/(n:ℝ)
  rw [hJ,hCJ]
  have hqi:1/(2:ℝ)^b=(s:ℝ)/n := (eq_div_iff hn.ne').mpr (by simpa [mul_comm] using he')
  rw [hqi]
  field_simp
  nlinarith
end StandardMapEntropy

end OAI

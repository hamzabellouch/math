import OAI.Combinatorics.HoneycombChords.CommonEigenline
import OAI.Combinatorics.HoneycombChords.LaurentPolynomials

namespace OAI

/-! Laurent and cosine polynomial forms of the strip transfer.

This development follows the finite strip transfer calculation for critical honeycomb
walks in the companion paper on uniform marked polygon estimates. -/

section
namespace CriticalHoneycomb.Transfer.SpectralFamily.Trig
open Reflection RowExchange BoundaryJet
open scoped BigOperators Matrix
noncomputable def qNum (a : ℝ) (k : ℤ) : LP := sn (Real.pi/4+a) k*sn (b+a) k
noncomputable def aNum (a : ℝ) (k : ℤ) : LP := LC S*sn (b-a) (-k)
noncomputable def hNum (a : ℝ) (k : ℤ) : LP := LC S*sn a k
noncomputable def vNum (a : ℝ) (k : ℤ) : LP := sn (b-a) (-k)*sn a k
noncomputable def cNum (a : ℝ) (k : ℤ) : LP := sn (b-a) (-k)*sn (Real.pi/4-a) (-k)
noncomputable def dNum (a : ℝ) (k : ℤ) : LP := sn a k*sn (a-L) k
abbrev LPLocal := Matrix Pair Pair LP
noncomputable def rNum (a : ℝ) (k : ℤ) : LPLocal := fun p q=>
  match p.1.val,p.2.val,q.1.val,q.2.val with
  | 0,0,0,0 => cNum a k
  | 2,2,2,2 => cNum a k
  | 0,1,0,1 => vNum a k
  | 1,0,1,0 => vNum a k
  | 2,1,2,1 => vNum a k
  | 1,2,1,2 => vNum a k
  | 0,1,1,0 => aNum a k
  | 1,0,0,1 => aNum a k
  | 2,1,1,2 => aNum a k
  | 1,2,2,1 => aNum a k
  | 0,2,0,2 => dNum a k
  | 0,2,1,1 => hNum a k*LC (Reflection.phase⁻¹)
  | 0,2,2,0 => cNum a k+dNum a k*LC ((Reflection.phase^2)⁻¹)
  | 1,1,0,2 => hNum a k*LC Reflection.phase
  | 1,1,1,1 => qNum a k
  | 1,1,2,0 => hNum a k*LC (Reflection.phase⁻¹)
  | 2,0,0,2 => cNum a k+dNum a k*LC (Reflection.phase^2)
  | 2,0,1,1 => hNum a k*LC Reflection.phase
  | 2,0,2,0 => dNum a k
  | _,_,_,_ => 0
lemma ev_qNum (u a : ℝ) (k : ℤ) : ev u (qNum a k)=Q (a+(k:ℝ)*u) := by
  simp only [qNum,map_mul,ev_sn,Q]
  congr 1 <;> congr 1 <;> ring
lemma ev_local_coefficients (u a : ℝ) (k : ℤ) :
    ev u (aNum a k)=coeffA (a+(k:ℝ)*u) ∧
    ev u (hNum a k)=coeffH (a+(k:ℝ)*u) ∧
    ev u (vNum a k)=coeffV (a+(k:ℝ)*u) ∧
    ev u (cNum a k)=coeffC (a+(k:ℝ)*u) ∧
    ev u (dNum a k)=coeffD (a+(k:ℝ)*u) := by
  have he (x : ℝ) : x-a+((-k:ℤ):ℝ)*u=x-(a+(k:ℝ)*u) := by push_cast;ring
  simp only [aNum,hNum,vNum,cNum,dNum,map_mul,ev_C,ev_sn,coeffA,coeffH,coeffV,coeffC,coeffD,he]
  refine ⟨True.intro,True.intro,True.intro,True.intro,?_⟩
  congr 1
  congr 1
  ring
lemma ev_rNum (u a : ℝ) (k : ℤ) (p q : Pair) :
    ev u (rNum a k p q)=bulkNumerator (a+(k:ℝ)*u) p q := by
  obtain ⟨ha,hh,hv,hc,hd⟩:=ev_local_coefficients u a k
  rcases p with ⟨p1,p2⟩;rcases q with ⟨q1,q2⟩
  fin_cases p1 <;> fin_cases p2 <;> fin_cases q1 <;> fin_cases q2 <;>
    simp only [rNum,bulkNumerator,map_mul,map_add,map_zero,ev_C,ha,hh,hv,hc,hd,ev_qNum,div_eq_mul_inv]
lemma local_bands (a : ℝ) (k : ℤ) :
    Band k.natAbs (aNum a k) ∧ Band k.natAbs (hNum a k) ∧
    Band (2*k.natAbs) (vNum a k) ∧ Band (2*k.natAbs) (cNum a k) ∧
    Band (2*k.natAbs) (dNum a k) ∧ Band (2*k.natAbs) (qNum a k) := by
  have hs (x : ℝ) : Band k.natAbs (sn x (-k)) := by simpa using sn_band x (-k)
  refine ⟨(hs _).C_mul _,(sn_band _ _).C_mul _,?_,?_,?_,?_⟩
  · simpa only [two_mul,vNum] using (hs (b-a)).mul (sn_band a k)
  · simpa only [two_mul,cNum] using (hs (b-a)).mul (hs (Real.pi/4-a))
  · simpa only [two_mul,dNum] using (sn_band a k).mul (sn_band (a-L) k)
  · simpa only [two_mul,qNum] using (sn_band (Real.pi/4+a) k).mul (sn_band (b+a) k)
attribute [local irreducible] Band aNum hNum vNum cNum dNum qNum sn
lemma rNum_band0 (a : ℝ) (k : ℤ) (p₂ q₁ q₂ : Spin) : Band (2*k.natAbs) (rNum a k (0,p₂) (q₁,q₂)) := by
  obtain ⟨ha,hh,hv,hc,hd,hq⟩:=local_bands a k
  have ha':=ha.mono (by omega : k.natAbs≤2*k.natAbs)
  have hh':=hh.mono (by omega : k.natAbs≤2*k.natAbs)
  fin_cases p₂ <;> fin_cases q₁ <;> fin_cases q₂ <;> simp only [rNum] <;>
    first
    | exact band_zero _
    | exact hc
    | exact hv
    | exact ha'
    | exact hd
    | exact hq
    | exact hh'.mul_C _
    | exact hc.add (hd.mul_C _)
lemma rNum_band1 (a : ℝ) (k : ℤ) (p₂ q₁ q₂ : Spin) : Band (2*k.natAbs) (rNum a k (1,p₂) (q₁,q₂)) := by
  obtain ⟨ha,hh,hv,hc,hd,hq⟩:=local_bands a k
  have ha':=ha.mono (by omega : k.natAbs≤2*k.natAbs)
  have hh':=hh.mono (by omega : k.natAbs≤2*k.natAbs)
  fin_cases p₂ <;> fin_cases q₁ <;> fin_cases q₂ <;> simp only [rNum] <;>
    first
    | exact band_zero _
    | exact hc
    | exact hv
    | exact ha'
    | exact hd
    | exact hq
    | exact hh'.mul_C _
lemma rNum_band2 (a : ℝ) (k : ℤ) (p₂ q₁ q₂ : Spin) : Band (2*k.natAbs) (rNum a k (2,p₂) (q₁,q₂)) := by
  obtain ⟨ha,hh,hv,hc,hd,hq⟩:=local_bands a k
  have ha':=ha.mono (by omega : k.natAbs≤2*k.natAbs)
  have hh':=hh.mono (by omega : k.natAbs≤2*k.natAbs)
  fin_cases p₂ <;> fin_cases q₁ <;> fin_cases q₂ <;> simp only [rNum] <;>
    first
    | exact band_zero _
    | exact hc
    | exact hv
    | exact ha'
    | exact hd
    | exact hq
    | exact hh'.mul_C _
    | exact hc.add (hd.mul_C _)
lemma rNum_band (a : ℝ) (k : ℤ) (p q : Pair) : Band (2*k.natAbs) (rNum a k p q) := by
  rcases p with ⟨p₁,p₂⟩
  fin_cases p₁
  · exact rNum_band0 a k p₂ q.1 q.2
  · exact rNum_band1 a k p₂ q.1 q.2
  · exact rNum_band2 a k p₂ q.1 q.2
noncomputable def kNum (a : ℝ) (k : ℤ) (i : Bool) (p : Pair) : LP :=
  LC (Reflection.phase^(spinValue p.2.rev)) *
    if i then
      if p.1=0 ∧ p.2.rev=1 then sn (2*a) (2*k) else
      if p.1=1 ∧ p.2.rev=2 then LC Reflection.phase*sn (2*a) (2*k) else 0
    else if p.1=p.2.rev then if p.1=1 then sn (gamma+a) k else sn (gamma-a) (-k) else 0
lemma kNum_band (a : ℝ) (k : ℤ) (i : Bool) (p : Pair) :
    Band ((if i then 2 else 1)*k.natAbs) (kNum a k i p) := by
  unfold kNum
  apply Band.C_mul
  cases i <;> simp only [Bool.false_eq_true,ite_false,ite_true,one_mul]
  · split_ifs
    · exact sn_band _ _
    · simpa using sn_band (gamma-a) (-k)
    · exact band_zero _
  · have hs : Band (2*k.natAbs) (sn (2*a) (2*k)) := by simpa only [Int.natAbs_mul,show Int.natAbs 2=2 from rfl] using sn_band (2*a) (2*k)
    split_ifs
    · exact hs
    · exact hs.C_mul _
    · exact band_zero _
lemma ev_kNum (u a : ℝ) (k : ℤ) (i : Bool) (p : Pair)
    (hn : sine (gamma+(a+(k:ℝ)*u))≠0) :
    ev u (kNum a k i p)=sine (gamma+(a+(k:ℝ)*u))*(if i then K1 (a+(k:ℝ)*u) p else K0 (a+(k:ℝ)*u) p) := by
  have he : gamma-a+((-k:ℤ):ℝ)*u=gamma-(a+(k:ℝ)*u) := by push_cast;ring
  have hd : 2*a+((2*k:ℤ):ℝ)*u=2*(a+(k:ℝ)*u) := by push_cast;ring
  have hp : gamma+a+(k:ℝ)*u=gamma+(a+(k:ℝ)*u) := by ring
  cases i <;> unfold kNum K0 K1 boundary0 boundary1
  all_goals simp only [Bool.false_eq_true,ite_false,ite_true]
  all_goals split_ifs <;> simp only [map_mul,map_zero,LC,ev_C,ev_sn,he,hd,hp] <;> field_simp [hn] ; ring
end CriticalHoneycomb.Transfer.SpectralFamily.Trig

end

section
namespace CriticalHoneycomb.Transfer.SpectralFamily.Trig
open Reflection RasterGrid RowExchange
open scoped BigOperators
noncomputable def qPlus : ℂ := -root^14/4
noncomputable def qMinus : ℂ := root^2/4
noncomputable def leadWeight (s : Spin) : ℂ := if s=0 then root^12 else if s=1 then 1 else -root^4
noncomputable def backWeight (s : Spin) : ℂ := if s=0 then -root^4 else if s=1 then 1 else root^12
lemma v_top_plus : (vNum L 1).coeff 2=-root^14/4 := by
  simp only [vNum,]
  rw [sn_minus_plus,show L-(b-L)=-(((2:ℕ):ℝ)*(Real.pi/16)) by dsimp only [L,b];push_cast;ring]
  rw [point_neg_angle 2 (by omega)]
lemma c_top_plus : (cNum L 1).coeff 2=root^10/4 := by
  simp only [cNum,]
  rw [sn_minus_minus,show -(b-L+(Real.pi/4-L))=-(((6:ℕ):ℝ)*(Real.pi/16)) by dsimp only [L,b];push_cast;ring]
  rw [point_neg_angle 6 (by omega)]
  all_goals norm_num
lemma d_top_plus : (dNum L 1).coeff 2=-root^2/4 := by
  simp only [dNum,]
  rw [sn_plus_plus,show L+(L-L)=((2:ℕ):ℝ)*(Real.pi/16) by dsimp only [L,b];push_cast;ring]
  rw [point_nat_angle 2]
lemma q_top_plus : (qNum L 1).coeff 2=-root^14/4 := by
  simp only [qNum,]
  rw [sn_plus_plus,show Real.pi/4+L+(b+L)=((14:ℕ):ℝ)*(Real.pi/16) by dsimp only [L,b];push_cast;ring]
  rw [point_nat_angle 14]
lemma v_top_minus : (vNum L (-1)).coeff 2=root^2/4 := by
  simp only [vNum,neg_neg]
  rw [sn_plus_minus,show b-L-L=((2:ℕ):ℝ)*(Real.pi/16) by dsimp only [L,b];push_cast;ring]
  rw [point_nat_angle 2]
lemma c_top_minus : (cNum L (-1)).coeff 2=-root^6/4 := by
  simp only [cNum,neg_neg]
  rw [sn_plus_plus,show b-L+(Real.pi/4-L)=((6:ℕ):ℝ)*(Real.pi/16) by dsimp only [L,b];push_cast;ring]
  rw [point_nat_angle 6]
lemma d_top_minus : (dNum L (-1)).coeff 2=root^14/4 := by
  simp only [dNum,]
  rw [sn_minus_minus,show -(L+(L-L))=-(((2:ℕ):ℝ)*(Real.pi/16)) by dsimp only [L,b];push_cast;ring]
  rw [point_neg_angle 2 (by omega)]
  all_goals norm_num
lemma q_top_minus : (qNum L (-1)).coeff 2=root^2/4 := by
  simp only [qNum,]
  rw [sn_minus_minus,show -(Real.pi/4+L+(b+L))=-(((14:ℕ):ℝ)*(Real.pi/16)) by dsimp only [L,b];push_cast;ring]
  rw [point_neg_angle 14 (by omega)]
  all_goals norm_num
lemma a_top_zero (k : ℤ) (hk : k.natAbs=1) : (aNum L k).coeff 2=0 := by
  exact ((local_bands L k).1).coeff_zero (by rw [hk];norm_num)
lemma h_top_zero (k : ℤ) (hk : k.natAbs=1) : (hNum L k).coeff 2=0 := by
  exact ((local_bands L k).2.1).coeff_zero (by rw [hk];norm_num)
lemma root_18 : root^18= -root^2 := by
  rw [show 18=16+2 from rfl,pow_add,root_sixteen];ring
lemma root_20 : root^20= -root^4 := by
  rw [show 20=16+4 from rfl,pow_add,root_sixteen];ring
lemma root_22 : root^22= -root^6 := by
  rw [show 22=16+6 from rfl,pow_add,root_sixteen];ring
lemma root_24 : root^24= -root^8 := by
  rw [show 24=16+8 from rfl,pow_add,root_sixteen];ring
lemma root_26 : root^26= -root^10 := by
  rw [show 26=16+10 from rfl,pow_add,root_sixteen];ring
lemma root_28 : root^28= -root^12 := by
  rw [show 28=16+12 from rfl,pow_add,root_sixteen];ring
lemma root_30 : root^30= -root^14 := by
  rw [show 30=16+14 from rfl,pow_add,root_sixteen];ring
lemma r_top_plus_small (i j s t : Spin) (hj : j.val<2) :
    (rNum L 1 (i,s) (j,t)).coeff 2=
      if i=j ∧ s=t then qPlus*(if j=0 then leadWeight s else 1) else 0 := by
  have ha:=a_top_zero 1 rfl
  have hh:=h_top_zero 1 rfl
  fin_cases j <;> norm_num at hj
  all_goals fin_cases i <;> fin_cases s <;> fin_cases t <;>
    simp only [rNum,coeff_add,coeff_mul_C,v_top_plus,c_top_plus,d_top_plus,q_top_plus,
      ha,hh,coeff_zero,qPlus,leadWeight] <;> (try simp only [Reflection.phase_eq]) <;> norm_num <;>
      (try ring_nf) <;> (try simp only [root_18,root_26,]) <;> ring
lemma r_top_minus_small (i j s t : Spin) (hi : i.val<2) :
    (rNum L (-1) (i,s) (j,t)).coeff 2=
      if i=j ∧ s=t then qMinus*(if i=0 then backWeight s else 1) else 0 := by
  have ha:=a_top_zero (-1) rfl
  have hh:=h_top_zero (-1) rfl
  fin_cases i <;> norm_num at hi
  all_goals fin_cases j <;> fin_cases s <;> fin_cases t <;>
    simp only [rNum,coeff_add,coeff_mul_C,v_top_minus,c_top_minus,d_top_minus,q_top_minus,
      ha,hh,coeff_zero,Reflection.phase_inv_sq,qMinus,backWeight] <;> (try simp only [Reflection.phase_eq]) <;> norm_num <;>
      (try ring_nf) <;> (try simp only [root_22,]) <;> ring
lemma qPlus_mul_qMinus : qPlus*qMinus=1/16 := by
  unfold qPlus qMinus
  rw [show -root^14/4*(root^2/4)= -root^(14+2)/16 by ring,root_sixteen]
  all_goals norm_num
lemma leadWeight_zpow (s : Spin) : leadWeight s=(-Reflection.phase)^(spinCharge s) := by
  fin_cases s <;> simp [leadWeight,spinCharge,inv_neg,Reflection.phase_eq]
  rw [←Reflection.phase_eq,Reflection.phase_inv,neg_neg]
lemma backWeight_zpow (s : Spin) : backWeight s=(-Reflection.phase)^(-spinCharge s) := by
  fin_cases s <;> simp [backWeight,spinCharge,inv_neg,Reflection.phase_eq]
  rw [←Reflection.phase_eq,Reflection.phase_inv,neg_neg]
end CriticalHoneycomb.Transfer.SpectralFamily.Trig

end

section
namespace CriticalHoneycomb.Transfer.SpectralFamily.Trig
open Reflection RowExchange BoundaryJet
open scoped BigOperators Matrix
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
noncomputable def rowNum : (n : ℕ)→ℝ→ℤ→Space n→Space n→Matrix Spin Spin LP
  | 0,_,_,_,_=>1
  | n+1,a,k,s,t=>fun i j=>∑ v : Spin,rNum a k (i,s 0) (v,t 0)*rowNum n a k (Fin.tail s) (Fin.tail t) v j
lemma rowNum_band (n : ℕ) (a : ℝ) (k : ℤ) (s t : Space n) (i j : Spin) :
    Band (2*n*k.natAbs) (rowNum n a k s t i j) := by
  induction n generalizing i j with
  | zero =>
    simp only [rowNum,Matrix.one_apply]
    split_ifs
    · simpa using (band_C (1:ℂ))
    · exact band_zero _
  | succ n ih =>
    simp only [rowNum]
    apply Band.sum
    intro v hv
    have h:=(rNum_band a k (i,s 0) (v,t 0)).mul (ih (Fin.tail s) (Fin.tail t) v j)
    convert h using 1  ; ring
lemma ev_rNum_scaled (u a : ℝ) (k : ℤ) (p q : Pair) (hq : Q (a+(k:ℝ)*u)≠0) :
    ev u (rNum a k p q)=Q (a+(k:ℝ)*u)*spectralR (a+(k:ℝ)*u) p q := by
  rw [ev_rNum]
  change bulkNumerator (a+(k:ℝ)*u) p q=Q (a+(k:ℝ)*u)*((Q (a+(k:ℝ)*u))⁻¹*bulkNumerator (a+(k:ℝ)*u) p q)
  rw [←mul_assoc,mul_inv_cancel₀ hq,one_mul]
lemma ev_rowNum (n : ℕ) (u a : ℝ) (k : ℤ) (s t : Space n) (i j : Spin)
    (hq : Q (a+(k:ℝ)*u)≠0) :
    ev u (rowNum n a k s t i j)=Q (a+(k:ℝ)*u)^n *
      row n (fun _=>spectralR (a+(k:ℝ)*u)) s t i j := by
  induction n generalizing i j with
  | zero =>
    simp only [rowNum,row,Matrix.one_apply,pow_zero,one_mul]
    split_ifs <;> simp
  | succ n ih =>
    simp only [rowNum,row,Matrix.mul_apply,map_sum,map_mul,ev_rNum_scaled _ _ _ _ _ hq]
    simp only [ih,block,Finset.mul_sum,pow_succ]
    apply Finset.sum_congr rfl
    intro v hv
    change Q (a+(k:ℝ)*u)*spectralR (a+(k:ℝ)*u) (i,s 0) (v,t 0) *
      (Q (a+(k:ℝ)*u)^n * row n (fun _=>spectralR (a+(k:ℝ)*u)) (Fin.tail s) (Fin.tail t) v j) =
      Q (a+(k:ℝ)*u)^n*Q (a+(k:ℝ)*u)*(spectralR (a+(k:ℝ)*u) (i,s 0) (v,t 0) *
       row n (fun _=>spectralR (a+(k:ℝ)*u)) (Fin.tail s) (Fin.tail t) v j)
    ring
noncomputable def bulkNum (n : ℕ) (s t : Space n) (p q : Pair) : LP :=
  ∑ v : Space n,rowNum n L 1 s v p.1 q.1 * rowNum n L (-1) v t p.2 q.2
lemma bulkNum_band (n : ℕ) (s t : Space n) (p q : Pair) : Band (4*n) (bulkNum n s t p q) := by
  apply Band.sum
  intro v hv
  have h:=(rowNum_band n L 1 s v p.1 q.1).mul (rowNum_band n L (-1) v t p.2 q.2)
  convert h using 1 ; simp ; omega
lemma ev_bulkNum (n : ℕ) (u : ℝ) (s t : Space n) (p q : Pair)
    (hp : Q (L+u)≠0) (hm : Q (L-u)≠0) :
    ev u (bulkNum n s t p q)=Q (L+u)^n*Q (L-u)^n*
      bulkRows n (homogeneous n) (gamma+u) s t p q := by
  have hs : exactSites n (homogeneous n) (gamma+u)=fun _=>spectralR (L+u) := by
    funext i
    dsimp only [exactSites]
    rw [show gamma+u+homogeneous n i=L+u by unfold homogeneous gamma L;ring]
  have ht : exactSites n (homogeneous n) (b-(gamma+u))=fun _=>spectralR (L-u) := by
    funext i
    dsimp only [exactSites]
    rw [show b-(gamma+u)+homogeneous n i=L-u by unfold homogeneous gamma L b;ring]
  have h1 : L+(1:ℤ)*u=L+u := by simp
  have h2 : L+(-1:ℤ)*u=L-u := by simp [sub_eq_add_neg]
  simp only [bulkNum,map_sum,map_mul,bulkRows,hs,ht,forward,Matrix.sum_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [ev_rowNum _ _ _ _ _ _ _ _ (by simpa only [Int.cast_one,one_mul] using hp),
    ev_rowNum _ _ _ _ _ _ _ _ (by simpa only [Int.cast_neg,Int.cast_one,neg_one_mul,←sub_eq_add_neg] using hm)]
  simp only [Int.cast_one,Int.cast_neg,one_mul,neg_one_mul,←sub_eq_add_neg]
  change _ = Q (L+u)^n*Q (L-u)^n*
    (row n (fun _=>spectralR (L+u)) s v p.1 q.1 * row n (fun _=>spectralR (L-u)) v t p.2 q.2)
  ring
end CriticalHoneycomb.Transfer.SpectralFamily.Trig

end

section
namespace CriticalHoneycomb.Transfer.SpectralFamily.Trig
open Reflection RasterGrid RowExchange
open scoped BigOperators
lemma rowNum_top_step (n : ℕ) (k : ℤ) (hk : k.natAbs=1) (s t : Space (n+1)) (i j : Spin) :
    (rowNum (n+1) L k s t i j).coeff (2*((n+1:ℕ):ℤ))=
      ∑ v : Spin,(rNum L k (i,s 0) (v,t 0)).coeff 2*
        (rowNum n L k (Fin.tail s) (Fin.tail t) v j).coeff (2*n) := by
  simp only [rowNum,coeff_sum]
  apply Finset.sum_congr rfl
  intro v hv
  have hr : Band 2 (rNum L k (i,s 0) (v,t 0)) := by simpa only [hk,mul_one] using rNum_band L k (i,s 0) (v,t 0)
  have ht : Band (2*n) (rowNum n L k (Fin.tail s) (Fin.tail t) v j) := by simpa only [hk,mul_one] using rowNum_band n L k (Fin.tail s) (Fin.tail t) v j
  convert top_mul hr ht using 1 <;> congr 1 ; push_cast ; ring
lemma space_eq_iff {n : ℕ} (s t : Space (n+1)) : s=t ↔ s 0=t 0 ∧ Fin.tail s=Fin.tail t := by
  constructor
  · rintro rfl;exact ⟨rfl,rfl⟩
  · rintro ⟨h₀,ht⟩
    funext i
    refine Fin.cases h₀ (fun j=>congrFun ht j) i
noncomputable def weightProd {n : ℕ} (w : Spin→ℂ) (s : Space n) : ℂ := ∏ i,w (s i)
lemma weightProd_succ {n : ℕ} (w : Spin→ℂ) (s : Space (n+1)) :
    weightProd w s=w (s 0)*weightProd w (Fin.tail s) := by
  unfold weightProd
  rw [Fin.prod_univ_succ]
  rfl
lemma row_top_plus_small (n : ℕ) (s t : Space n) (i j : Spin) (hj : j.val<2) :
    (rowNum n L 1 s t i j).coeff (2*n)=
      if i=j ∧ s=t then qPlus^n*(if j=0 then weightProd leadWeight s else 1) else 0 := by
  induction n generalizing i j with
  | zero =>
    have hst : s=t := Subsingleton.elim _ _
    by_cases hij : i=j <;> simp [rowNum,hst,hij,Matrix.one_apply,weightProd]
  | succ n ih =>
    rw [rowNum_top_step n 1 rfl]
    simp_rw [ih _ _ _ _ hj,ite_and,mul_ite,mul_zero]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    rw [r_top_plus_small _ _ _ _ hj]
    by_cases hij : i=j <;> by_cases hhead : s 0=t 0 <;> by_cases htail : Fin.tail s=Fin.tail t <;>
      simp [hij,hhead,htail,space_eq_iff,weightProd_succ,pow_succ] ; split_ifs <;> ring
lemma row_top_minus_small (n : ℕ) (s t : Space n) (i j : Spin) (hi : i.val<2) :
    (rowNum n L (-1) s t i j).coeff (2*n)=
      if i=j ∧ s=t then qMinus^n*(if i=0 then weightProd backWeight s else 1) else 0 := by
  induction n generalizing i j with
  | zero =>
    have hst : s=t := Subsingleton.elim _ _
    by_cases hij : i=j <;> simp [rowNum,hst,hij,Matrix.one_apply,weightProd]
  | succ n ih =>
    rw [rowNum_top_step n (-1) rfl]
    simp_rw [r_top_minus_small _ _ _ _ hi,ite_and,ite_mul,zero_mul]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    rw [ih _ _ _ _ hi]
    by_cases hij : i=j <;> by_cases hhead : s 0=t 0 <;> by_cases htail : Fin.tail s=Fin.tail t <;>
      simp [hij,hhead,htail,space_eq_iff,weightProd_succ,pow_succ] ; split_ifs <;> ring
lemma columnCharge_succ {n : ℕ} (s : Space (n+1)) :
    columnCharge s=spinCharge (s 0)+columnCharge (Fin.tail s) := by
  unfold columnCharge
  rw [Fin.sum_univ_succ]
  rfl
lemma weightProd_lead_zpow {n : ℕ} (s : Space n) :
    weightProd leadWeight s=(-Reflection.phase)^(columnCharge s) := by
  have hn : Reflection.phase≠0 := point_ne_zero _
  induction n with
  | zero => simp [weightProd,columnCharge]
  | succ n ih =>
    rw [weightProd_succ,leadWeight_zpow,ih,columnCharge_succ,
      zpow_add₀ (neg_ne_zero.mpr hn)]
lemma weightProd_back_zpow {n : ℕ} (s : Space n) :
    weightProd backWeight s=(-Reflection.phase)^(-columnCharge s) := by
  have hn : Reflection.phase≠0 := point_ne_zero _
  induction n with
  | zero => simp [weightProd,columnCharge]
  | succ n ih =>
    rw [weightProd_succ,backWeight_zpow,ih,columnCharge_succ,neg_add,
      zpow_add₀ (neg_ne_zero.mpr hn)]
end CriticalHoneycomb.Transfer.SpectralFamily.Trig

end

section
namespace CriticalHoneycomb.Transfer.SpectralFamily.Trig
open Reflection
noncomputable def den (n : ℕ) (u : ℝ) : ℂ :=
  Q (L+u)^n*Q (L-u)^n*sine (b+u)*sine (b-u)
lemma sine_pair (a u : ℝ) : sine (a+u)*sine (a-u)=
    ((Real.cos (2*u):ℂ)-(Real.cos (2*a):ℂ))/2 := by
  have h:=Real.cos_sub (a+u) (a-u)
  have hh:=Real.cos_add (a+u) (a-u)
  rw [show a+u-(a-u)=2*u by ring] at h
  rw [show a+u+(a-u)=2*a by ring] at hh
  have he : Real.sin (a+u)*Real.sin (a-u)=(Real.cos (2*u)-Real.cos (2*a))/2 := by linarith
  unfold sine
  exact_mod_cast he
lemma boundary_den_cos (u : ℝ) : sine (b+u)*sine (b-u)=
    ((Real.cos (2*u):ℂ)+(Real.cos (2*L):ℂ))/2 := by
  rw [sine_pair,show 2*b=Real.pi-2*L by unfold b L;ring,Real.cos_pi_sub]
  push_cast
  ring
lemma Q_pair_cos (u : ℝ) : Q (L+u)*Q (L-u)=
    (((Real.cos (2*u):ℂ)+1)*((Real.cos (2*u):ℂ)+(Real.cos (2*L):ℂ)))/4 := by
  have hb : Real.pi/4+L=b := by unfold b L;ring
  have hh : b+L=Real.pi/2 := by unfold b L;ring
  simp only [Q,←add_assoc,←add_sub_assoc,hb,hh]
  rw [show sine (b+u)*sine (Real.pi/2+u)*(sine (b-u)*sine (Real.pi/2-u))=
    (sine (b+u)*sine (b-u))*(sine (Real.pi/2+u)*sine (Real.pi/2-u)) by ring]
  rw [boundary_den_cos,sine_pair,show 2*(Real.pi/2)=Real.pi by ring,Real.cos_pi]
  push_cast
  ring
lemma den_cos (n : ℕ) (u : ℝ) : den n u=
    (2:ℂ)⁻¹^(2*n+1)*((Real.cos (2*u):ℂ)+1)^n*
      ((Real.cos (2*u):ℂ)+(Real.cos (2*L):ℂ))^(n+1) := by
  unfold den
  rw [←mul_pow,mul_assoc (_^n) (sine _) (sine _),boundary_den_cos,Q_pair_cos]
  simp only [div_eq_mul_inv,mul_pow,pow_add,pow_mul,pow_one]
  have hf : (4:ℂ)⁻¹=(2:ℂ)⁻¹^2 := by norm_num
  rw [hf]
  ring
lemma den_star (n : ℕ) (u : ℝ) : star (den n u)=den n u := by
  simp only [den,Q,sine,map_mul,map_pow,Complex.star_def,Complex.conj_ofReal]
lemma den_reflection (n : ℕ) (u : ℝ) : den n (-u)=den n u := by
  rw [den_cos,den_cos]
  simp only [mul_neg,Real.cos_neg]
lemma den_periodicity (n : ℕ) (u : ℝ) : den n (u+Real.pi)=den n u := by
  rw [den_cos,den_cos,mul_add,Real.cos_add_two_pi]
end CriticalHoneycomb.Transfer.SpectralFamily.Trig

end

section
namespace CriticalHoneycomb.Transfer.SpectralFamily.Trig
open Reflection RowExchange BoundaryJet RasterGrid
open scoped BigOperators Matrix
noncomputable def coefficientNum (n : ℕ) (i j : Bool) (s t : Space n) : LP :=
  ∑ p : Pair,∑ q : Pair,kNum gamma (-1) i p*bulkNum n s t p q*kNum gamma 1 j q
lemma coefficientNum_band (n : ℕ) (i j : Bool) (s t : Space n) :
    Band (4*n+2+(if i then 1 else 0)+(if j then 1 else 0)) (coefficientNum n i j s t) := by
  apply Band.sum;intro p hp
  apply Band.sum;intro q hq
  have h:=((kNum_band gamma (-1) i p).mul (bulkNum_band n s t p q)).mul (kNum_band gamma 1 j q)
  convert h using 1 ; cases i <;> cases j <;> simp <;> omega
lemma homogeneous_nonsingular_iff (n : ℕ) (hn : 0<n) (u : ℝ) :
    Nonsingular n (homogeneous n) (gamma+u) ↔
      sine (b+u)≠0 ∧ sine (b-u)≠0 ∧ Q (L+u)≠0 ∧ Q (L-u)≠0 := by
  have h1 : gamma+(gamma+u)=b+u := by unfold gamma b;ring
  have h2 : gamma+(b-(gamma+u))=b-u := by ring
  have h3 : gamma+u+(-L/2)=L+u := by unfold gamma L;ring
  have h4 : b-(gamma+u)+(-L/2)=L-u := by unfold gamma L b;ring
  simp only [Nonsingular,homogeneous,h1,h2,h3,h4]
  constructor
  · rintro ⟨h,h',hp⟩
    exact ⟨h,h',hp ⟨0,hn⟩⟩
  · rintro ⟨h,h',hp⟩
    exact ⟨h,h',fun _=>hp⟩
lemma ev_coefficientNum (n : ℕ) (u : ℝ) (s t : Space n) (i j : Bool)
    (hb : sine (b+u)≠0) (hm : sine (b-u)≠0) (hq : Q (L+u)≠0) (hq' : Q (L-u)≠0) :
    ev u (coefficientNum n i j s t)=den n u*coefficient n (homogeneous n) (gamma+u) i j s t := by
  have ha : gamma+((-1:ℤ):ℝ)*u=b-(gamma+u) := by unfold gamma b;push_cast;ring
  have ha' : gamma+(1:ℤ)*u=gamma+u := by simp
  have hp : gamma+(gamma+(1:ℤ)*u)=b+u := by unfold gamma b;push_cast;ring
  have hn : gamma+(gamma+((-1:ℤ):ℝ)*u)=b-u := by unfold gamma b;push_cast;ring
  have hkm (p : Pair) : ev u (kNum gamma (-1) i p)=sine (b-u)*(if i then K1 (b-(gamma+u)) p else K0 (b-(gamma+u)) p) := by
    rw [ev_kNum _ _ _ _ _ (by rw [hn];exact hm),hn,ha]
  have hkp (p : Pair) : ev u (kNum gamma 1 j p)=sine (b+u)*(if j then K1 (gamma+u) p else K0 (gamma+u) p) := by
    rw [ev_kNum _ _ _ _ _ (by rw [hp];exact hb),hp,ha']
  simp only [coefficientNum,map_sum,map_mul,hkm,hkp,ev_bulkNum _ _ _ _ _ _ hq hq']
  simp only [coefficient,den,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro p hp
  apply Finset.sum_congr rfl;intro q hq
  ring
lemma den_ne_zero (n : ℕ) (u : ℝ)
    (hb : sine (b+u)≠0) (hm : sine (b-u)≠0) (hq : Q (L+u)≠0) (hq' : Q (L-u)≠0) :
    den n u≠0 := by exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hq) (pow_ne_zero _ hq')) hb) hm
noncomputable def pairNum (n : ℕ) (a d : Jet) (s t : Space n) : LP :=
  LC (both (a*d))*conjugate (coefficientNum n false false s t)+
  LC (base a*right d+right a*base d)*conjugate (coefficientNum n false true s t)+
  LC (base a*left d+left a*base d)*conjugate (coefficientNum n true false s t)+
  LC (base a*base d)*conjugate (coefficientNum n true true s t)
lemma pairNum_band (n : ℕ) (a d : Jet) (s t : Space n) : Band (4*n+4) (pairNum n a d s t) := by
  have h (i j : Bool) : Band (4*n+4) (conjugate (coefficientNum n i j s t)) :=
    ((coefficientNum_band n i j s t).mono (by cases i <;> cases j <;> simp )).conjugate
  exact (((h false false).C_mul _).add ((h false true).C_mul _)).add
    ((h true false).C_mul _) |>.add ((h true true).C_mul _)

lemma both_pair_form (a d : Jet) (x y z w : ℂ) :
    both (a*form x y z w*d)=both (a*d)*x+(base a*right d+right a*base d)*y+
      (base a*left d+left a*base d)*z+base a*base d*w := by
  simp only [both_mul,base_mul,left_mul,right_mul,base_form,left_form,right_form,both_form]
  ring
lemma ev_pairNum (n : ℕ) (u : ℝ) (a d : Jet) (s t : Space n)
    (hb : sine (b+u)≠0) (hm : sine (b-u)≠0) (hq : Q (L+u)≠0) (hq' : Q (L-u)≠0) :
    ev u (pairNum n a d s t)=den n u*both (a*reflectJet (T n (homogeneous n) (gamma+u) s t)*d) := by
  simp only [pairNum,map_add,map_mul,LC,ev_C,ev_conjugate,ev_coefficientNum _ _ _ _ _ _ hb hm hq hq']
  rw [T_coefficients]
  have hr (x y z w : ℂ) : reflectJet (form x y z w)=form (star x) (star z) (star y) (star w) := by
    apply jet_ext <;> simp only [reflectJet_apply,reflected_base,reflected_left,reflected_right,reflected_both,base_form,left_form,right_form,both_form]
  rw [hr,both_pair_form]
  simp only [star_mul,den_star]
  ring
noncomputable def scalarNum (W : ℕ) : LP :=
  ∑ s : Space (W+1),∑ t : Space (W+1),pairNum (W+1) (normalizedDual W s) (markedEigenvector W t)
    (reflectedSites (W+1) s) (reflectedSites (W+1) t)
lemma scalarNum_band (W : ℕ) : Band (4*(W+1)+4) (scalarNum W) := by
  apply Band.sum;intro s hs
  apply Band.sum;intro t ht
  exact pairNum_band _ _ _ _ _
lemma ev_scalarNum (W : ℕ) (u : ℝ) (hu : Nonsingular (W+1) (homogeneous (W+1)) (gamma+u)) :
    ev u (scalarNum W)=den (W+1) u*physicalP W u := by
  obtain ⟨hb,hm,hq,hq'⟩:=(homogeneous_nonsingular_iff (W+1) (by omega) u).mp hu
  simp only [scalarNum,map_sum,ev_pairNum _ _ _ _ _ _ hb hm hq hq',physicalP,physicalScalar,
    commonScalar,Matrix.mulVec,dotProduct,Finset.mul_sum,both_sum]
  apply Finset.sum_congr rfl;intro s hs
  apply Finset.sum_congr rfl;intro t ht
  congr 2
  rw [mul_assoc]
  rfl
end CriticalHoneycomb.Transfer.SpectralFamily.Trig

end

section
namespace CriticalHoneycomb.Transfer.SpectralFamily.Trig
open Reflection RasterGrid RowExchange
open scoped BigOperators
lemma bulkNum_top (n : ℕ) (s t : Space n) (p q : Pair) :
    (bulkNum n s t p q).coeff (4*n)=
      ∑ v : Space n,(rowNum n L 1 s v p.1 q.1).coeff (2*n)*
        (rowNum n L (-1) v t p.2 q.2).coeff (2*n) := by
  simp only [bulkNum,coeff_sum]
  apply Finset.sum_congr rfl
  intro v hv
  have hp : Band (2*n) (rowNum n L 1 s v p.1 q.1) := by simpa using rowNum_band n L 1 s v p.1 q.1
  have hm : Band (2*n) (rowNum n L (-1) v t p.2 q.2) := by simpa using rowNum_band n L (-1) v t p.2 q.2
  convert top_mul hp hm using 1 <;> congr 1 ; push_cast ; ring
lemma bulkNum_top_small (n : ℕ) (s t : Space n) (i j k l : Spin) (hk : k.val<2) (hj : j.val<2) :
    (bulkNum n s t (i,j) (k,l)).coeff (4*n)=
      if i=k ∧ j=l ∧ s=t then (1/16:ℂ)^n*(if k=0 then weightProd leadWeight s else 1)*
        (if j=0 then weightProd backWeight s else 1) else 0 := by
  rw [bulkNum_top]
  simp_rw [row_top_plus_small _ _ _ _ _ hk,row_top_minus_small _ _ _ _ _ hj]
  by_cases hi : i=k <;> by_cases hl : j=l
  all_goals simp only [hi,hl,ite_false,zero_mul,mul_zero,Finset.sum_const_zero,false_and,true_and]
  by_cases hst : s=t
  · subst t
    rw [Finset.sum_eq_single s]
    · simp only [ite_true]
      rw [show qPlus^n*(if k=0 then weightProd leadWeight s else 1)*
          (qMinus^n*(if l=0 then weightProd backWeight s else 1))=
          (qPlus*qMinus)^n*(if k=0 then weightProd leadWeight s else 1)*
          (if l=0 then weightProd backWeight s else 1) by rw [mul_pow];ring,
        qPlus_mul_qMinus]
    · intro v hv hn
      simp [hn,Ne.symm hn]
    · simp
  · simp only [hst,ite_false]
    apply Finset.sum_eq_zero
    intro v hv
    by_cases hsv : s=v
    · subst v;simp [hst]
    · simp [hsv]
lemma kNum_true (a : ℝ) (k : ℤ) (p : Pair) :
    kNum a k true p=if p=(0,1) ∨ p=(1,0) then sn (2*a) (2*k) else 0 := by
  rcases p with ⟨p,q⟩
  have hp : Reflection.phase≠0 := point_ne_zero _
  fin_cases p <;> fin_cases q <;> simp [kNum,Fin.rev,spinValue,LC,←map_mul,hp,←mul_assoc]
lemma coefficientNum_TT (n : ℕ) (s t : Space n) :
    coefficientNum n true true s t=
      sn (2*gamma) (-2)*(bulkNum n s t (0,1) (0,1)+bulkNum n s t (0,1) (1,0)+
        bulkNum n s t (1,0) (0,1)+bulkNum n s t (1,0) (1,0))*sn (2*gamma) 2 := by
  simp only [coefficientNum,kNum_true]
  simp [Fintype.sum_prod_type,Fin.sum_univ_succ,mul_ite,ite_mul,]
  ring
lemma wall_top_product : (sn (2*gamma) (-2)).coeff 2*(sn (2*gamma) 2).coeff 2=1/4 := by
  calc
    _= -((2*Complex.I)⁻¹)^2*(point (-(2*gamma))*point (2*gamma)) := by
      simp only [sn_coeff]
      norm_num
      ring
    _=1/4 := by rw [inv_two_I_sq,←point_add,neg_add_cancel];norm_num [point]
end CriticalHoneycomb.Transfer.SpectralFamily.Trig

end

section
namespace CriticalHoneycomb.Transfer.SpectralFamily.Trig
open Reflection RasterGrid RowExchange
open scoped BigOperators
lemma wall_bulk_wall_top (n : ℕ) (p : LP) (hp : Band (4*n) p) :
    (sn (2*gamma) (-2)*p*sn (2*gamma) 2).coeff (4*n+4)=
      (sn (2*gamma) (-2)).coeff 2*p.coeff (4*n)*(sn (2*gamma) 2).coeff 2 := by
  have hm : Band 2 (sn (2*gamma) (-2)) := sn_band (2*gamma) (-2)
  have ht : Band 2 (sn (2*gamma) 2) := sn_band (2*gamma) 2
  have h : (sn (2*gamma) (-2)*p).coeff (2+4*n)=
      (sn (2*gamma) (-2)).coeff 2*p.coeff (4*n) := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using top_mul hm hp
  have hh:=top_mul (hm.mul hp) ht
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hh
  rw [show (2+4*(n:ℤ))+2=4*n+4 by ring,h] at hh
  exact hh
lemma coefficientNum_TT_top (n : ℕ) (s t : Space n) :
    (coefficientNum n true true s t).coeff (4*n+4)=
      if s=t then (1/4:ℂ)*(1/16:ℂ)^n*(weightProd leadWeight s+weightProd backWeight s) else 0 := by
  rw [coefficientNum_TT,wall_bulk_wall_top _ _
    ((((bulkNum_band n s t (0,1) (0,1)).add (bulkNum_band n s t (0,1) (1,0))).add
      (bulkNum_band n s t (1,0) (0,1))).add (bulkNum_band n s t (1,0) (1,0)))]
  simp only [coeff_add]
  rw [bulkNum_top_small _ _ _ _ _ _ _ (by decide) (by decide),
    bulkNum_top_small _ _ _ _ _ _ _ (by decide) (by decide),
    bulkNum_top_small _ _ _ _ _ _ _ (by decide) (by decide),
    bulkNum_top_small _ _ _ _ _ _ _ (by decide) (by decide)]
  by_cases h : s=t
  · simp only [h,ite_true,ite_false,show (0:Spin)≠1 from by decide,
      show (1:Spin)≠0 from by decide,false_and,and_self,mul_one,add_zero]
    rw [show (sn (2*gamma) (-2)).coeff 2*((1/16:ℂ)^n*weightProd leadWeight t+
      (1/16:ℂ)^n*weightProd backWeight t)*(sn (2*gamma) 2).coeff 2=
      ((sn (2*gamma) (-2)).coeff 2*(sn (2*gamma) 2).coeff 2)*
      (1/16:ℂ)^n*(weightProd leadWeight t+weightProd backWeight t) by ring,wall_top_product]
  · simp [h]
lemma coefficientNum_TT_top_zeroCharge (n : ℕ) (s t : Space n) (hs : columnCharge s=0) :
    (coefficientNum n true true s t).coeff (4*n+4)=
      if s=t then (1/2:ℂ)*(1/16:ℂ)^n else 0 := by
  rw [coefficientNum_TT_top,weightProd_lead_zpow,weightProd_back_zpow,hs]
  split_ifs <;> norm_num ; ring
end CriticalHoneycomb.Transfer.SpectralFamily.Trig

end

section
namespace CriticalHoneycomb.Transfer.SpectralFamily.Trig
open Reflection BoundaryJet
open scoped BigOperators
lemma physicalP_reflection (W : ℕ) (u : ℝ)
    (hu : Nonsingular (W+1) (homogeneous (W+1)) (gamma+u)) : physicalP W (-u)=physicalP W u := by
  unfold physicalP
  rw [show gamma+-u=b-(gamma+u) by unfold gamma b;ring,physicalScalar_reflection W (gamma+u) hu]
lemma physicalP_periodicity (W : ℕ) (u : ℝ) : physicalP W (u+Real.pi)=physicalP W u := by
  unfold physicalP
  rw [←add_assoc,physicalScalar_periodicity]
lemma homogeneous_nonsingular_den (n : ℕ) (hn : 0<n) (u : ℝ) :
    Nonsingular n (homogeneous n) (gamma+u) ↔ den n u≠0 := by
  rw [homogeneous_nonsingular_iff n hn]
  constructor
  · rintro ⟨hb,hm,hp,hq⟩;exact den_ne_zero n u hb hm hp hq
  · intro hd
    have hb : sine (b+u)≠0 := by intro h;apply hd;simp [den,h]
    have hm : sine (b-u)≠0 := by intro h;apply hd;simp [den,h]
    have hp : Q (L+u)≠0 := by intro h;apply hd;simp [den,h,ne_of_gt hn]
    have hq : Q (L-u)≠0 := by intro h;apply hd;simp [den,h,ne_of_gt hn]
    exact ⟨hb,hm,hp,hq⟩
lemma dense_homogeneous_nonsingular (n : ℕ) (hn : 0<n) :
    Dense {u : ℝ | Nonsingular n (homogeneous n) (gamma+u)} := by
  have h₁:=sine_zero_countable.preimage (f:=fun u : ℝ=>b+u) (fun x y h=>add_left_cancel h)
  have h₂:=sine_zero_countable.preimage (f:=fun u : ℝ=>b-u) (fun x y h=>sub_right_injective h)
  have h₃:=Q_zero_countable.preimage (f:=fun u : ℝ=>L+u) (fun x y h=>add_left_cancel h)
  have h₄:=Q_zero_countable.preimage (f:=fun u : ℝ=>L-u) (fun x y h=>sub_right_injective h)
  have hd:=(((h₁.union h₂).union h₃).union h₄).dense_compl ℝ
  convert hd using 1
  ext u
  simp only [Set.mem_ofPred_eq,homogeneous_nonsingular_iff n hn,Set.mem_compl_iff,
    Set.mem_union,Set.mem_preimage,Set.mem_ofPred_eq]
  tauto
lemma flip_coeff (p : LP) (k : ℤ) : (flip p).coeff k=p.coeff (-k) := by
  simp [flip,AddMonoidAlgebra.coeff_mapDomainRingEquiv,Finsupp.equivMapDomain_apply]
lemma flip_C (c : ℂ) : flip (LaurentPolynomial.C c)=LaurentPolynomial.C c := by
  ext k
  simp only [flip_coeff,LaurentPolynomial.C_apply,neg_eq_zero]
lemma flip_T (k : ℤ) : flip (LaurentPolynomial.T k)=LaurentPolynomial.T (-k) := by
  ext j
  simp only [flip_coeff,LaurentPolynomial.T_apply,neg_eq_iff_eq_neg]
lemma ev_flip (u : ℝ) (p : LP) : ev u (flip p)=ev (-u) p := by
  have hp : p=∑ k∈p.coeff.support,LaurentPolynomial.C (p.coeff k)*LaurentPolynomial.T k := by
    simpa only [Finsupp.sum,LaurentPolynomial.single_eq_C_mul_T] using (AddMonoidAlgebra.sum_coeff_single p).symm
  conv_lhs => rw [hp]
  conv_rhs => rw [hp]
  simp only [map_sum,map_mul,flip_C,flip_T,ev_C,ev_T]
  apply Finset.sum_congr rfl
  intro k hk
  congr 2
  push_cast
  ring
lemma scalarNum_flip (W : ℕ) : flip (scalarNum W)=scalarNum W := by
  apply ev_ext_dense (dense_homogeneous_nonsingular (W+1) (by omega))
  intro u hu
  have hn : Nonsingular (W+1) (homogeneous (W+1)) (gamma+-u) := by
    rw [homogeneous_nonsingular_den _ (by omega),den_reflection]
    exact (homogeneous_nonsingular_den _ (by omega) u).mp hu
  rw [ev_flip,ev_scalarNum _ _ hn,ev_scalarNum _ _ hu,den_reflection,physicalP_reflection _ _ hu]
lemma scalarNum_coeff_reflection (W : ℕ) (k : ℤ) : (scalarNum W).coeff (-k)=(scalarNum W).coeff k := by
  rw [←flip_coeff,scalarNum_flip]
lemma cosinePoly_physical (W : ℕ) (u : ℝ)
    (hu : Nonsingular (W+1) (homogeneous (W+1)) (gamma+u)) :
    (cosinePoly (2*(W+1)+2) (scalarNum W)).eval (Real.cos (2*u):ℂ)=den (W+1) u*physicalP W u := by
  have hh : Band (2*(2*(W+1)+2)) (scalarNum W) := by convert scalarNum_band W using 1  ; omega
  rw [cosinePoly_eval hh]
  have hd:= (homogeneous_nonsingular_den _ (by omega) u).mp hu
  have hnu : Nonsingular (W+1) (homogeneous (W+1)) (gamma+-u) := by
    rw [homogeneous_nonsingular_den _ (by omega),den_reflection];exact hd
  have hpu : Nonsingular (W+1) (homogeneous (W+1)) (gamma+(u+Real.pi)) := by
    rw [homogeneous_nonsingular_den _ (by omega),den_periodicity];exact hd
  have hnpu : Nonsingular (W+1) (homogeneous (W+1)) (gamma+(-u+Real.pi)) := by
    rw [homogeneous_nonsingular_den _ (by omega),den_periodicity,den_reflection];exact hd
  rw [ev_scalarNum _ _ hu,ev_scalarNum _ _ hnu,ev_scalarNum _ _ hpu,ev_scalarNum _ _ hnpu,
    den_periodicity,den_periodicity,den_reflection,physicalP_periodicity,physicalP_periodicity,
    physicalP_reflection _ _ hu]
  ring
end CriticalHoneycomb.Transfer.SpectralFamily.Trig

end

section
namespace CriticalHoneycomb.Transfer.SpectralFamily.Trig
open Reflection RasterGrid RowExchange BoundaryJet
open scoped BigOperators
lemma pairNum_bottom (n : ℕ) (a d : Jet) (s t : Space n) :
    (pairNum n a d s t).coeff (-(4*n+4))=
      base a*base d*star ((coefficientNum n true true s t).coeff (4*n+4)) := by
  have h (i j : Bool) (hij : i=false ∨ j=false) :
      (coefficientNum n i j s t).coeff (4*n+4)=0 := by
    apply (coefficientNum_band n i j s t).coeff_zero
    cases i <;> cases j <;> simp_all <;> omega
  simp only [pairNum,coeff_add,coeff_C_mul,conjugate_coeff,neg_neg,
    h false false (Or.inl rfl),h false true (Or.inl rfl),h true false (Or.inr rfl),
    star_zero,mul_zero,zero_add]
lemma spinCharge_rev (s : Spin) : spinCharge s.rev= -spinCharge s := by
  fin_cases s <;> norm_num [spinCharge,Fin.rev]
lemma reflectedSites_charge (n : ℕ) (s : Space n) :
    columnCharge (reflectedSites n s)= -columnCharge s := by
  change (∑ i : Fin n,spinCharge ((s i.rev).rev))= -(∑ i : Fin n,spinCharge (s i))
  simp_rw [spinCharge_rev]
  rw [Finset.sum_neg_distrib,neg_inj]
  exact Equiv.sum_comp Fin.revPerm (fun i=>spinCharge (s i))
lemma base_normalizedDual (W : ℕ) (s : Space (W+1)) :
    base (normalizedDual W s)=archRow W s := by
  simp [normalizedDual,inverseAtOne,dualEigenvector]
lemma base_markedEigenvector (W : ℕ) (s : Space (W+1)) :
    base (markedEigenvector W s)=archColumn W s := by simp [markedEigenvector]
lemma physical_pair_bottom (W : ℕ) (s t : Space (W+1)) :
    (pairNum (W+1) (normalizedDual W s) (markedEigenvector W t)
      (reflectedSites (W+1) s) (reflectedSites (W+1) t)).coeff (-(4*((W+1:ℕ):ℤ)+4))=
      if s=t then archRow W s*archColumn W s*((1/2:ℂ)*(1/16:ℂ)^(W+1)) else 0 := by
  rw [pairNum_bottom,base_normalizedDual,base_markedEigenvector]
  by_cases hst : s=t
  · subst t
    by_cases hs : columnCharge s=0
    · rw [coefficientNum_TT_top_zeroCharge _ _ _ (by rw [reflectedSites_charge,hs,neg_zero])]
      simp
    · rw [archRow_charge s hs]
      simp
  · rw [coefficientNum_TT_top]
    have hr : reflectedSites (W+1) s≠reflectedSites (W+1) t :=
      fun h=>hst ((reflectedSites (W+1)).injective h)
    simp [hst,hr]
lemma scalarNum_bottom (W : ℕ) : (scalarNum W).coeff (-(4*((W+1:ℕ):ℤ)+4))=(1/2:ℂ)*(1/16:ℂ)^(W+1) := by
  simp only [scalarNum,coeff_sum,physical_pair_bottom]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [←Finset.sum_mul,arch_pairing,one_mul]
lemma scalarNum_top (W : ℕ) : (scalarNum W).coeff (4*((W+1:ℕ):ℤ)+4)=(1/2:ℂ)*(1/16:ℂ)^(W+1) := by
  rw [←scalarNum_coeff_reflection,scalarNum_bottom]
noncomputable def physicalNumerator (W : ℕ) : Polynomial ℂ :=
  Polynomial.C ((2:ℂ)^(2*(W+1)+1))*cosinePoly (2*(W+1)+2) (scalarNum W)
lemma physicalNumerator_degree (W : ℕ) : (physicalNumerator W).natDegree≤2*(W+1)+2 := by
  calc
    _≤(cosinePoly (2*(W+1)+2) (scalarNum W)).natDegree := Polynomial.natDegree_C_mul_le _ _
    _≤_ := cosinePoly_degree _ _
lemma physicalNumerator_top (W : ℕ) : (physicalNumerator W).coeff (2*(W+1)+2)=4 := by
  rw [physicalNumerator,Polynomial.coeff_C_mul,cosinePoly_top _ (by omega)]
  have he : (2*((2*(W+1)+2:ℕ):ℤ))=4*((W+1:ℕ):ℤ)+4 := by push_cast;ring
  rw [he,scalarNum_top,scalarNum_bottom]
  have hd : 2*(W+1)+2-1=2*(W+1)+1 := by omega
  rw [hd]
  rw [show (1/16:ℂ)^(W+1)=((2:ℂ)^(4*(W+1)))⁻¹ by rw [pow_mul,←inv_pow];norm_num]
  have hp : (2:ℂ)^((2*(W+1)+1)+(2*(W+1)+1))=(2:ℂ)^(4*(W+1)+2) := by congr 1;omega
  rw [show (2:ℂ)^(2*(W+1)+1)*((2:ℂ)^(2*(W+1)+1)*
      ((1/2)*((2:ℂ)^(4*(W+1)))⁻¹+(1/2)*((2:ℂ)^(4*(W+1)))⁻¹))=
      (2:ℂ)^((2*(W+1)+1)+(2*(W+1)+1))*((2:ℂ)^(4*(W+1)))⁻¹ by rw [pow_add];ring,
    hp,pow_add,mul_assoc,mul_comm ((2:ℂ)^2),←mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ (by norm_num))]
  norm_num
end CriticalHoneycomb.Transfer.SpectralFamily.Trig

end

section
namespace CriticalHoneycomb.Transfer.SpectralFamily.Trig
open Polynomial
lemma drop_top_degree {p : Polynomial ℂ} {d : ℕ}
    (hp : p.natDegree ≤ d+1) (hc : p.coeff (d+1)=0) : p.natDegree≤d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  by_cases hnd : n=d+1
  · simpa only [hnd] using hc
  · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp (by omega))
noncomputable def polePoly (N : ℕ) : Polynomial ℂ :=
  (X+C 1)^N*(X+C (Real.cos (2*Reflection.L):ℂ))^(N+1)
lemma polePoly_monic (N : ℕ) : (polePoly N).Monic := by
  exact ((monic_X_add_C _).pow N).mul ((monic_X_add_C _).pow (N+1))
lemma polePoly_degree (N : ℕ) : (polePoly N).natDegree=2*N+1 := by
  unfold polePoly
  rw [natDegree_mul ((monic_X_add_C _).pow N).ne_zero ((monic_X_add_C _).pow (N+1)).ne_zero,
    natDegree_pow,natDegree_pow,natDegree_X_add_C,natDegree_X_add_C]
  omega
lemma polePoly_top (N : ℕ) : (polePoly N).coeff (2*N+1)=1 := by
  rw [←polePoly_degree]
  exact (polePoly_monic N).coeff_natDegree
lemma polynomial_linear_decomposition {A D : Polynomial ℂ} {d : ℕ}
    (hD : D.Monic) (hdeg : D.natDegree=d)
    (hA : A.natDegree ≤ d+1) (hc : A.coeff (d+1)=4) (hd : 0<d) :
    ∃ (ρ : ℂ) (P : Polynomial ℂ), P.natDegree<d ∧
      A=(C 4*X+C ρ)*D+P := by
  let B := A-C 4*(X*D)
  have hBD : (C 4*(X*D)).natDegree≤d+1 := by
    calc
      _≤(X*D).natDegree := natDegree_C_mul_le _ _
      _=d+1 := by rw [natDegree_X_mul hD.ne_zero,hdeg]
  have hB : B.natDegree≤d := by
    apply drop_top_degree
    · exact (natDegree_sub_le _ _).trans (max_le hA hBD)
    · simp only [B,Polynomial.coeff_sub,Polynomial.coeff_C_mul,Polynomial.coeff_X_mul,hc]
      rw [←hdeg,hD.coeff_natDegree]
      norm_num
  let ρ := B.coeff d
  let P := B-C ρ*D
  have hC : (C ρ*D).natDegree≤d := (natDegree_C_mul_le _ _).trans_eq hdeg
  have hP : P.natDegree<d := by
    have hp : P.natDegree≤d := (natDegree_sub_le _ _).trans (max_le hB hC)
    have pc : P.coeff d=0 := by
      simp only [P,Polynomial.coeff_sub,Polynomial.coeff_C_mul,←hdeg,hD.coeff_natDegree,mul_one,ρ]
      rw [hdeg,sub_self]
    have hle : P.natDegree≤d-1 := by
      apply drop_top_degree
      · simpa only [Nat.sub_add_cancel hd] using hp
      · simpa only [Nat.sub_add_cancel hd] using pc
    omega
  refine ⟨ρ,P,hP,?_⟩
  dsimp [P,B]
  ring
lemma physicalNumerator_decomposition (W : ℕ) :
    ∃ (ρ : ℂ) (P : Polynomial ℂ), P.natDegree<2*(W+1)+1 ∧
      physicalNumerator W=(C 4*X+C ρ)*polePoly (W+1)+P := by
  apply polynomial_linear_decomposition (polePoly_monic _) (polePoly_degree _)
  · simpa only [Nat.add_assoc] using physicalNumerator_degree W
  · simpa only [Nat.add_assoc] using physicalNumerator_top W
  · omega
end CriticalHoneycomb.Transfer.SpectralFamily.Trig

end

end OAI

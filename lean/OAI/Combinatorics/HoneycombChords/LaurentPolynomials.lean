import OAI.Combinatorics.HoneycombChords.Reflection

namespace OAI

/-! Laurent polynomial support, evaluation, and cosine polynomial averages.

The formulas express reflection-symmetric trigonometric polynomials in the Chebyshev basis. -/

section

namespace CriticalHoneycomb.Transfer.SpectralFamily.Trig
open Reflection
open scoped BigOperators Pointwise
abbrev LP := LaurentPolynomial ℂ
noncomputable abbrev LC := LaurentPolynomial.C (R:=ℂ)
noncomputable def ev (u : ℝ) : LP →+* ℂ :=
  LaurentPolynomial.eval₂ (RingHom.id ℂ) (Units.mk0 (point u) (point_ne_zero u))
def Band (d : ℕ) (p : LP) : Prop := ∀ k ∈ p.coeff.support,-(d:ℤ)≤k ∧ k≤d
lemma band_zero (d : ℕ) : Band d 0 := by simp [Band]
lemma band_C (c : ℂ) : Band 0 (LaurentPolynomial.C c) := by
  intro k hk
  have : k=0 := by
    have h : k=0 ∧ c≠0 := by simpa [LaurentPolynomial.C_apply] using (Finsupp.mem_support_iff.mp hk)
    exact h.1
  simp [this]
lemma band_T (k : ℤ) : Band k.natAbs (LaurentPolynomial.T k : LP) := by
  intro j hj
  have : j=k := by simpa [LaurentPolynomial.T_apply,eq_comm] using (Finsupp.mem_support_iff.mp hj)
  subst j
  have h1 : k≤(k.natAbs:ℤ) := Int.le_natAbs
  have h2 : -k≤(k.natAbs:ℤ) := by simpa using (Int.le_natAbs (a:=-k))
  omega
lemma Band.mono {d e : ℕ} {p : LP} (h : Band d p) (he : d≤e) : Band e p := by
  intro k hk
  have:=h k hk
  omega
lemma Band.add {d : ℕ} {p q : LP} (hp : Band d p) (hq : Band d q) : Band d (p+q) := by
  intro k hk
  have : k∈p.coeff.support ∪ q.coeff.support := Finsupp.support_add hk
  rcases Finset.mem_union.mp this with h|h
  · exact hp k h
  · exact hq k h
lemma Band.neg {d : ℕ} {p : LP} (hp : Band d p) : Band d (-p) := by
  simpa only [Band,AddMonoidAlgebra.coeff_neg,Finsupp.support_neg] using hp
lemma Band.sub {d : ℕ} {p q : LP} (hp : Band d p) (hq : Band d q) : Band d (p-q) := by
  simpa only [sub_eq_add_neg] using hp.add hq.neg
lemma Band.mul {d e : ℕ} {p q : LP} (hp : Band d p) (hq : Band e q) : Band (d+e) (p*q) := by
  intro k hk
  obtain ⟨i,hi,j,hj,rfl⟩:=Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset p q hk)
  have:=hp i hi
  have:=hq j hj
  constructor <;> push_cast <;> omega
lemma Band.sum {ι : Type*} (s : Finset ι) {d : ℕ} (p : ι→LP)
    (h : ∀ i∈s,Band d (p i)) : Band d (∑ i∈s,p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using band_zero d
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    apply (h a (Finset.mem_insert_self _ _)).add
    exact ih (fun i hi=>h i (Finset.mem_insert_of_mem hi))
lemma Band.C_mul {d : ℕ} {p : LP} (hp : Band d p) (c : ℂ) : Band d (LaurentPolynomial.C c*p) := by
  simpa only [zero_add] using (band_C c).mul hp
lemma Band.mul_C {d : ℕ} {p : LP} (hp : Band d p) (c : ℂ) : Band d (p*LaurentPolynomial.C c) := by
  simpa only [add_zero] using hp.mul (band_C c)
lemma Band.pow {d : ℕ} {p : LP} (hp : Band d p) (m : ℕ) : Band (m*d) (p^m) := by
  induction m with
  | zero => simpa using band_C 1
  | succ m ih => simpa only [pow_succ,Nat.succ_mul] using ih.mul hp
@[simp] lemma ev_C (u : ℝ) (c : ℂ) : ev u (LaurentPolynomial.C c)=c := by simp [ev]
lemma ev_T (u : ℝ) (k : ℤ) : ev u (LaurentPolynomial.T k)=point ((k:ℝ)*u) := by
  rw [ev,LaurentPolynomial.eval₂_T]
  rw [Units.val_zpow_eq_zpow_val]
  change (point u)^k=point ((k:ℝ)*u)
  unfold point
  rw [←Complex.exp_int_mul]
  congr 1
  push_cast
  ring
lemma ev_sum (u : ℝ) (p : LP) : ev u p=∑ k∈p.coeff.support,p.coeff k*point ((k:ℝ)*u) := by
  have hp : p=∑ k∈p.coeff.support,LaurentPolynomial.C (p.coeff k)*LaurentPolynomial.T k := by
    simpa only [Finsupp.sum,LaurentPolynomial.single_eq_C_mul_T] using (AddMonoidAlgebra.sum_coeff_single p).symm
  conv_lhs => rw [hp]
  simp only [map_sum,map_mul,ev_C,ev_T]
noncomputable def sn (a : ℝ) (k : ℤ) : LP :=
  LaurentPolynomial.C ((2*Complex.I)⁻¹) *
    (LaurentPolynomial.C (point a)*LaurentPolynomial.T k-
      LaurentPolynomial.C (point (-a))*LaurentPolynomial.T (-k))
lemma sn_band (a : ℝ) (k : ℤ) : Band k.natAbs (sn a k) := by
  apply Band.C_mul
  apply Band.sub
  · exact (band_T k).C_mul _
  · simpa only [Int.natAbs_neg] using (band_T (-k)).C_mul (point (-a))
lemma ev_sn (u a : ℝ) (k : ℤ) : ev u (sn a k)=sine (a+(k:ℝ)*u) := by
  simp only [sn,map_mul,map_sub,ev_C,ev_T]
  rw [←point_add,←point_add]
  have he : -a+((-k:ℤ):ℝ)*u= -(a+(k:ℝ)*u) := by push_cast;ring
  rw [he,←sine_exp]
  change _=sine (a+(k:ℝ)*u)
  have hi : (2*Complex.I:ℂ)≠0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  rw [←mul_assoc,inv_mul_cancel₀ hi,one_mul]
  rfl
lemma top_mul {d e : ℕ} {p q : LP} (hp : Band d p) (hq : Band e q) :
    (p*q).coeff (d+e)=p.coeff d*q.coeff e := by
  classical
  rw [AddMonoidAlgebra.coeff_mul_apply_left]
  change (∑ k∈p.coeff.support,p.coeff k*q.coeff (-k+(d+e)))=_
  by_cases hd : (d:ℤ)∈p.coeff.support
  · rw [Finset.sum_eq_single (d:ℤ)]
    · congr 1
      congr 1
      omega
    · intro k hk hkd
      have hlt : (e:ℤ)< -k+(d+e) := by have:=hp k hk;omega
      have hz : q.coeff (-k+(d+e))=0 := by
        by_contra hz
        have:=hq _ (Finsupp.mem_support_iff.mpr hz)
        omega
      simp [hz]
    · exact fun h=>False.elim (h hd)
  · have hz : p.coeff (d:ℤ)=0 := Finsupp.notMem_support_iff.mp hd
    rw [hz,zero_mul]
    apply Finset.sum_eq_zero
    intro k hk
    have hlt : (e:ℤ)< -k+(d+e) := by
      have:=hp k hk
      have : k≠(d:ℤ) := by intro h;subst k;exact hd hk
      omega
    have hzq : q.coeff (-k+(d+e))=0 := by
      by_contra hzq
      have:=hq _ (Finsupp.mem_support_iff.mpr hzq)
      omega
    simp [hzq]
end CriticalHoneycomb.Transfer.SpectralFamily.Trig

end

section
namespace CriticalHoneycomb.Transfer.SpectralFamily.Trig
open Reflection
open scoped BigOperators
lemma coeff_C_mul (c : ℂ) (p : LP) (k : ℤ) :
    (LC c*p).coeff k=c*p.coeff k :=
  AddMonoidAlgebra.coeff_single_zero_mul p c k
lemma coeff_mul_C (p : LP) (c : ℂ) (k : ℤ) :
    (p*LC c).coeff k=p.coeff k*c :=
  AddMonoidAlgebra.coeff_mul_single_zero p c k
lemma coeff_add (p q : LP) (k : ℤ) : (p+q).coeff k=p.coeff k+q.coeff k := rfl
lemma coeff_sub (p q : LP) (k : ℤ) : (p-q).coeff k=p.coeff k-q.coeff k := rfl
lemma coeff_zero (k : ℤ) : (0:LP).coeff k=0 := rfl
lemma coeff_sum {ι : Type*} (s : Finset ι) (p : ι→LP) (k : ℤ) :
    (∑ i∈s,p i).coeff k=∑ i∈s,(p i).coeff k := by simp
lemma Band.coeff_zero {d : ℕ} {p : LP} (hp : Band d p) {k : ℤ} (hk : (d:ℤ)<k) : p.coeff k=0 := by
  apply Finsupp.notMem_support_iff.mp
  intro hc
  exact (hp k hc).2.not_gt hk
lemma sn_coeff (a : ℝ) (k j : ℤ) : (sn a k).coeff j=
    (2*Complex.I)⁻¹*((if k=j then point a else 0)-(if -k=j then point (-a) else 0)) := by
  simp only [sn,coeff_C_mul,coeff_sub,LaurentPolynomial.T_apply]
  split_ifs <;> simp
lemma sn_top_plus (a : ℝ) : (sn a 1).coeff 1=(2*Complex.I)⁻¹*point a := by
  simp only [sn_coeff];norm_num
lemma sn_top_minus (a : ℝ) : (sn a (-1)).coeff 1= -(2*Complex.I)⁻¹*point (-a) := by
  simp only [sn_coeff];norm_num
lemma sn_pair_top (a b : ℝ) (s t : ℤ) (hs : s.natAbs=1) (ht : t.natAbs=1) :
    (sn a s*sn b t).coeff 2=(sn a s).coeff 1*(sn b t).coeff 1 := by
  simpa only [hs,ht,Nat.cast_one,one_add_one_eq_two] using top_mul (sn_band a s) (sn_band b t)
lemma inv_two_I_sq : ((2*Complex.I)⁻¹:ℂ)^2= -1/4 := by
  rw [inv_pow,mul_pow,Complex.I_sq];norm_num
lemma sn_plus_plus (a b : ℝ) : (sn a 1*sn b 1).coeff 2= -point (a+b)/4 := by
  rw [sn_pair_top _ _ _ _ rfl rfl,sn_top_plus,sn_top_plus]
  rw [show (2*Complex.I)⁻¹*point a*((2*Complex.I)⁻¹*point b)=((2*Complex.I)⁻¹)^2*(point a*point b) by ring]
  rw [inv_two_I_sq,←point_add];ring
lemma sn_minus_minus (a b : ℝ) : (sn a (-1)*sn b (-1)).coeff 2= -point (-(a+b))/4 := by
  rw [sn_pair_top _ _ _ _ rfl rfl,sn_top_minus,sn_top_minus]
  rw [show -(2*Complex.I)⁻¹*point (-a)*(-(2*Complex.I)⁻¹*point (-b))=((2*Complex.I)⁻¹)^2*(point (-a)*point (-b)) by ring]
  rw [inv_two_I_sq,←point_add,←neg_add];ring
lemma sn_minus_plus (a b : ℝ) : (sn a (-1)*sn b 1).coeff 2=point (b-a)/4 := by
  rw [sn_pair_top _ _ _ _ rfl rfl,sn_top_minus,sn_top_plus]
  rw [show -(2*Complex.I)⁻¹*point (-a)*((2*Complex.I)⁻¹*point b)= -((2*Complex.I)⁻¹)^2*(point (-a)*point b) by ring]
  rw [inv_two_I_sq,←point_add,show -a+b=b-a by ring];ring
lemma sn_plus_minus (a b : ℝ) : (sn a 1*sn b (-1)).coeff 2=point (a-b)/4 := by
  rw [mul_comm,sn_minus_plus]
end CriticalHoneycomb.Transfer.SpectralFamily.Trig

end

section
namespace CriticalHoneycomb.Transfer.SpectralFamily.Trig
open Reflection
open scoped BigOperators
lemma point_pair (x : ℝ) : point x+point (-x)=2*(Real.cos x:ℂ) := by
  simpa only [point,Complex.ofReal_neg,←Complex.ofReal_cos] using (Complex.two_cos (x:ℂ)).symm
lemma point_even_pi {k : ℤ} (h : Even k) : point ((k:ℝ)*Real.pi)=1 := by
  obtain ⟨j,rfl⟩:=h
  unfold point
  convert Complex.exp_int_mul_two_pi_mul_I j using 1; congr 1; push_cast; ring
lemma point_odd_pi {k : ℤ} (h : Odd k) : point ((k:ℝ)*Real.pi)= -1 := by
  obtain ⟨j,rfl⟩:=h
  rw [show (((2*j+1:ℤ):ℝ)*Real.pi)=(j:ℝ)*(2*Real.pi)+Real.pi by push_cast;ring,point_add]
  have hp : point ((j:ℝ)*(2*Real.pi))=1 := by
    unfold point
    convert Complex.exp_int_mul_two_pi_mul_I j using 1; congr 1; push_cast; ring
  rw [hp,one_mul]
  exact Complex.exp_pi_mul_I
lemma cheb_cos (u : ℝ) (j : ℤ) :
    (Polynomial.Chebyshev.T ℂ j).eval (Real.cos (2*u):ℂ)=(Real.cos ((j:ℝ)*(2*u)):ℂ) := by
  simpa only [Complex.ofReal_cos,Complex.ofReal_mul,Complex.ofReal_intCast] using
    Polynomial.Chebyshev.T_complex_cos ((2*u:ℝ):ℂ) j
lemma monomial_average (u : ℝ) (k : ℤ) :
    (point ((k:ℝ)*u)+point ((k:ℝ)*(-u))+point ((k:ℝ)*(u+Real.pi))+
      point ((k:ℝ)*(-u+Real.pi)))/4=
    if Even k then (Polynomial.Chebyshev.T ℂ (k/2)).eval (Real.cos (2*u):ℂ) else 0 := by
  have hp (v : ℝ) : point ((k:ℝ)*(v+Real.pi))=point ((k:ℝ)*v)*point ((k:ℝ)*Real.pi) := by
    rw [mul_add,point_add]
  rw [hp,hp,show (k:ℝ)*(-u)= -((k:ℝ)*u) by ring]
  by_cases hk : Even k
  · rw [ite_eq_left hk,point_even_pi hk,mul_one,mul_one,cheb_cos]
    have hdiv : k/2*2=k := Int.ediv_mul_cancel (even_iff_two_dvd.mp hk)
    have he : ((k/2:ℤ):ℝ)*(2*u)=(k:ℝ)*u := by
      have h : ((k/2:ℤ):ℝ)*2=(k:ℝ) := by exact_mod_cast hdiv
      linear_combination u*h
    rw [he]
    have hh:=point_pair ((k:ℝ)*u)
    linear_combination hh/2
  · rw [ite_eq_right hk,point_odd_pi ((Int.even_or_odd k).resolve_left hk)]
    ring
noncomputable def cosinePoly (D : ℕ) (p : LP) : Polynomial ℂ :=
  ∑ k∈Finset.Icc (-(2*D:ℕ):ℤ) (2*D),
    if Even k then Polynomial.C (p.coeff k)*Polynomial.Chebyshev.T ℂ (k/2) else 0
lemma cos_index_bound (D : ℕ) {k : ℤ} (hk : k∈Finset.Icc (-(2*D:ℕ):ℤ) (2*D)) :
    (k/2).natAbs≤D := by
  have h:=Finset.mem_Icc.mp hk
  have h1 : -(D:ℤ)≤k/2 := by omega
  have h2 : k/2≤(D:ℤ) := by omega
  have ha : |k/2|≤(D:ℤ) := abs_le.mpr ⟨h1,h2⟩
  have hb : ((k/2).natAbs:ℤ)≤(D:ℤ) := by simpa only [Int.natCast_natAbs] using ha
  exact_mod_cast hb
lemma cosinePoly_degree (D : ℕ) (p : LP) : (cosinePoly D p).natDegree≤D := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  split_ifs
  · exact (Polynomial.natDegree_C_mul_le _ _).trans
      ((Polynomial.Chebyshev.natDegree_T ℂ (k/2)).le.trans (cos_index_bound D hk))
  · simp
lemma ev_interval {D : ℕ} {p : LP} (h : Band D p) (u : ℝ) :
    ev u p=∑ k∈Finset.Icc (-(D:ℤ)) D,p.coeff k*point ((k:ℝ)*u) := by
  rw [ev_sum]
  apply Finset.sum_subset
  · intro k hk
    exact Finset.mem_Icc.mpr (h k hk)
  · intro k hk hn
    simp [Finsupp.notMem_support_iff.mp hn]
lemma cosinePoly_eval {D : ℕ} {p : LP} (h : Band (2*D) p) (u : ℝ) :
    (cosinePoly D p).eval (Real.cos (2*u):ℂ)=
      (ev u p+ev (-u) p+ev (u+Real.pi) p+ev (-u+Real.pi) p)/4 := by
  simp only [cosinePoly,Polynomial.eval_finsetSum,apply_ite,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_zero,ev_interval h,←Finset.sum_add_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hh:=monomial_average u k
  by_cases he : Even k
  · simp only [ite_eq_left he] at hh ⊢
    rw [←hh]
    ring
  · simp only [ite_eq_right he] at hh ⊢
    linear_combination -(p.coeff k)*hh
end CriticalHoneycomb.Transfer.SpectralFamily.Trig

end

section
namespace CriticalHoneycomb.Transfer.SpectralFamily.Trig
open Reflection
open scoped BigOperators
noncomputable def flip : LP ≃+* LP := AddMonoidAlgebra.mapDomainRingEquiv ℂ (AddEquiv.neg ℤ)
noncomputable def conjugate : LP →+* LP :=
  (AddMonoidAlgebra.mapRingHom ℤ (starRingEnd ℂ)).comp flip.toRingHom
lemma conjugate_coeff (p : LP) (k : ℤ) : (conjugate p).coeff k=star (p.coeff (-k)) := by
  simp [conjugate,flip,AddMonoidAlgebra.coeff_mapRingHom,AddMonoidAlgebra.coeff_mapDomainRingEquiv,
    Finsupp.equivMapDomain_apply]
lemma Band.conjugate {d : ℕ} {p : LP} (h : Band d p) : Band d (conjugate p) := by
  intro k hk
  have hn : p.coeff (-k)≠0 := by simpa only [conjugate_coeff,star_ne_zero] using Finsupp.mem_support_iff.mp hk
  have:=h (-k) (Finsupp.mem_support_iff.mpr hn)
  omega
lemma conjugate_single (c : ℂ) (k : ℤ) :
    conjugate (AddMonoidAlgebra.single k c)=AddMonoidAlgebra.single (-k) (star c) := by
  ext j
  simp only [conjugate_coeff,AddMonoidAlgebra.coeff_single,Finsupp.single_apply]
  by_cases h : k= -j
  · simp [h]
  · have h' : -k≠j := by omega
    simp [h,h']
lemma point_star (u : ℝ) : star (point u)=point (-u) := by
  simp [point,←Complex.exp_conj,mul_comm]
lemma conjugate_C (c : ℂ) : conjugate (LaurentPolynomial.C c)=LaurentPolynomial.C (star c) := by
  change conjugate (AddMonoidAlgebra.single 0 c)=AddMonoidAlgebra.single 0 (star c)
  simpa only [neg_zero] using conjugate_single c 0
lemma conjugate_T (k : ℤ) : conjugate (LaurentPolynomial.T k)=LaurentPolynomial.T (-k) := by
  change conjugate (AddMonoidAlgebra.single k 1)=AddMonoidAlgebra.single (-k) 1
  simpa only [star_one] using conjugate_single 1 k
lemma ev_conjugate (u : ℝ) (p : LP) : ev u (conjugate p)=star (ev u p) := by
  have hp : p=∑ k∈p.coeff.support,AddMonoidAlgebra.single k (p.coeff k) :=
    (AddMonoidAlgebra.sum_coeff_single p).symm
  conv_lhs => rw [hp]
  conv_rhs => rw [hp]
  simp only [map_sum,star_sum,LaurentPolynomial.single_eq_C_mul_T,
    map_mul,conjugate_C,conjugate_T,ev_C,ev_T,star_mul,point_star]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show ((-k:ℤ):ℝ)*u= -((k:ℝ)*u) by push_cast; ring]
  exact mul_comm _ _
end CriticalHoneycomb.Transfer.SpectralFamily.Trig

end

section
namespace CriticalHoneycomb.Transfer.SpectralFamily.Trig
open Reflection
open scoped BigOperators
lemma continuous_ev (p : LP) : Continuous (fun u : ℝ=> ev u p) := by
  simp_rw [ev_sum]
  apply continuous_finsetSum
  intro k hk
  unfold point
  fun_prop
lemma point_range_infinite : (Set.range point).Infinite := by
  intro hf
  have he : Complex.re '' Set.range point=Set.range Real.cos := by
    rw [←Set.range_comp]
    congr 1
    funext u
    exact Complex.exp_ofReal_mul_I_re u
  exact Real.range_cos_infinite (he ▸ hf.image Complex.re)
lemma ev_toLaurent (u : ℝ) (p : Polynomial ℂ) : ev u p.toLaurent=p.eval (point u) := by
  change LaurentPolynomial.eval₂ (RingHom.id ℂ) (Units.mk0 (point u) (point_ne_zero u)) p.toLaurent=_
  rw [LaurentPolynomial.eval₂_toLaurent]
  rfl

lemma ev_eq_zero {p : LP} (he : ∀ u : ℝ,ev u p=0) : p=0 := by
  obtain ⟨n,f,hf⟩:=LaurentPolynomial.exists_T_pow p
  have hz : f=0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply point_range_infinite.mono
    rintro z ⟨u,rfl⟩
    change f.eval (point u)=0
    rw [←ev_toLaurent,hf,map_mul,he,zero_mul]
  rw [hz,map_zero] at hf
  have ht : (LaurentPolynomial.T (n:ℤ):LP)≠0 := by
    apply_fun ev 0
    simp only [map_zero,ev_T]
    exact point_ne_zero _
  exact (mul_eq_zero.mp hf.symm).resolve_right ht
lemma ev_ext {p q : LP} (he : ∀ u : ℝ,ev u p=ev u q) : p=q := by
  apply sub_eq_zero.mp
  apply ev_eq_zero
  intro u
  rw [map_sub,he,sub_self]
lemma ev_ext_dense {S : Set ℝ} (hS : Dense S) {p q : LP}
    (he : ∀ u∈S,ev u p=ev u q) : p=q := by
  apply ev_ext
  intro u
  exact Set.EqOn.closure he (continuous_ev p) (continuous_ev q) (by rw [hS.closure_eq];exact Set.mem_univ u)
end CriticalHoneycomb.Transfer.SpectralFamily.Trig

end

section
namespace CriticalHoneycomb.Transfer.SpectralFamily.Trig
open Reflection
open scoped BigOperators
lemma cheb_coeff_top (D : ℕ) (k : ℤ) (hk : k.natAbs=D) :
    (Polynomial.Chebyshev.T ℂ k).coeff D=2^(D-1) := by
  rw [←hk,←Polynomial.Chebyshev.natDegree_T ℂ k,Polynomial.coeff_natDegree,
    Polynomial.Chebyshev.leadingCoeff_T,Polynomial.Chebyshev.natDegree_T]
lemma cosinePoly_top (D : ℕ) (hD : 0<D) (p : LP) :
    (cosinePoly D p).coeff D=2^(D-1)*(p.coeff (2*D)+p.coeff (-(2*D:ℤ))) := by
  classical
  have hs : ({(-(2*D:ℤ)),(2*D:ℤ)} : Finset ℤ) ⊆Finset.Icc (-(2*D:ℕ):ℤ) (2*D) := by
    intro k hk
    simp only [Finset.mem_insert,Finset.mem_singleton] at hk
    rcases hk with rfl|rfl <;> simp
  have hz (k : ℤ) (hk : k∈Finset.Icc (-(2*D:ℕ):ℤ) (2*D))
      (hn : k∉({(-(2*D:ℤ)),(2*D:ℤ)} : Finset ℤ)) :
      (if Even k then Polynomial.C (p.coeff k)*Polynomial.Chebyshev.T ℂ (k/2) else 0).coeff D=0 := by
    by_cases he : Even k
    · rw [ite_eq_left he,Polynomial.coeff_C_mul]
      have hd : (Polynomial.Chebyshev.T ℂ (k/2)).natDegree<D := by
        rw [Polynomial.Chebyshev.natDegree_T]
        have h0:=Finset.mem_Icc.mp hk
        have h1 : k≠ -(2*D:ℤ) ∧ k≠(2*D:ℤ) := by simpa using hn
        have h2 : k%2=0 := Int.emod_eq_zero_of_dvd (even_iff_two_dvd.mp he)
        have h3 : |k/2|<(D:ℤ) := abs_lt.mpr ⟨by omega,by omega⟩
        exact_mod_cast (show ((k/2).natAbs:ℤ)<(D:ℤ) by simpa only [Int.natCast_natAbs] using h3)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hd,mul_zero]
    · simp [he]
  simp only [cosinePoly,Polynomial.finsetSum_coeff]
  rw [←Finset.sum_subset hs hz]
  have hne : -(2*D:ℤ)≠(2*D:ℤ) := by omega
  have hp : Even (2*D:ℤ) := even_two_mul _
  have hn : Even (-(2*D:ℤ)) := hp.neg
  have hdivp : (2*D:ℤ)/2=(D:ℤ) := by omega
  have hdivn : (-(2*D:ℤ))/2= -(D:ℤ) := by omega
  simp only [Finset.sum_insert,Finset.mem_singleton,hne,not_false_eq_true,Finset.sum_singleton,
    ite_eq_left hp,ite_eq_left hn,Polynomial.coeff_C_mul,hdivp,hdivn]
  rw [cheb_coeff_top D (-D) (by simp),cheb_coeff_top D D (by simp)]
  ring
end CriticalHoneycomb.Transfer.SpectralFamily.Trig

end

end OAI

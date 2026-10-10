import OAI.Algebra.Determinantal.SingularValues

namespace OAI

namespace PermanentBorder.FrobeniusPlane
open MvPolynomial
variable {K : Type*} [Field K] [CharP K 2]

omit [CharP K 2] in
lemma partial_degree {f : Plane K} {n : ℕ} (hf : f.totalDegree ≤ n+1) (i : Fin 2) :
    (pderiv i f).totalDegree ≤ n := by
  classical
  apply Finset.sup_le
  intro m hm
  have hc := mem_support_iff.mp hm
  rw [coeff_pderiv] at hc
  have hp : f.coeff (m+Finsupp.single i 1) ≠ 0 := (mul_ne_zero_iff.mp hc).1
  have hd := le_totalDegree (mem_support_iff.mpr hp)
  change (m+Finsupp.single i 1).degree ≤ f.totalDegree at hd
  simp only [map_add,Finsupp.degree_single] at hd
  change m.degree ≤ n
  omega

omit [CharP K 2] in
lemma square_degree (p : Plane K) : (p^2).totalDegree = 2*p.totalDegree := by
  by_cases hp : p=0
  · simp [hp]
  · rw [pow_two,totalDegree_mul_of_isDomain hp hp]
    omega

lemma squareForm_degree_bounds {a b c d : Plane K} {n : ℕ}
    (h : (squareForm a b c d).totalDegree ≤ n+2) :
    2*a.totalDegree ≤ n+2 ∧ 2*b.totalDegree ≤ n+1 ∧
      2*c.totalDegree ≤ n+1 ∧ 2*d.totalDegree ≤ n := by
  have hx := partial_degree h 0
  have hy := partial_degree h 1
  rw [squareForm_partial_zero] at hx
  rw [squareForm_partial_one] at hy
  have hd := partial_degree (partial_degree h 0) 1
  rw [squareForm_mixed,square_degree] at hd
  have hxd : (X (0 : Fin 2)*d^2).totalDegree ≤ n+1 := by
    exact (totalDegree_mul _ _).trans (by rw [totalDegree_X,square_degree]; omega)
  have hyd : (X (1 : Fin 2)*d^2).totalDegree ≤ n+1 := by
    exact (totalDegree_mul _ _).trans (by rw [totalDegree_X,square_degree]; omega)
  have hb : 2*b.totalDegree ≤ n+1 := by
    rw [← square_degree]
    have he : b^2=(b^2+X 1*d^2)-X 1*d^2 := by ring
    rw [he]
    exact (totalDegree_sub _ _).trans (max_le hx hyd)
  have hc : 2*c.totalDegree ≤ n+1 := by
    rw [← square_degree]
    have he : c^2=(c^2+X 0*d^2)-X 0*d^2 := by ring
    rw [he]
    exact (totalDegree_sub _ _).trans (max_le hy hxd)
  have ha : 2*a.totalDegree ≤ n+2 := by
    rw [← square_degree]
    have he : a^2=squareForm a b c d-X 0*b^2-X 1*c^2-X 0*X 1*d^2 := by
      unfold squareForm; ring
    rw [he]
    apply (totalDegree_sub _ _).trans
    apply max_le
    · apply (totalDegree_sub _ _).trans
      apply max_le
      · apply (totalDegree_sub _ _).trans
        exact max_le h ((totalDegree_mul _ _).trans (by rw [totalDegree_X,square_degree]; omega))
      · exact (totalDegree_mul _ _).trans (by rw [totalDegree_X,square_degree]; omega)
    · have he' : X (0 : Fin 2)*X 1*d^2=X 0*(X 1*d^2) := mul_assoc ..
      rw [he']
      exact (totalDegree_mul _ _).trans (by rw [totalDegree_X]; omega)
  exact ⟨ha,hb,hc,hd⟩

omit [CharP K 2] in
lemma squareForm_degree_le {a b c d : Plane K} {n : ℕ}
    (ha : 2*a.totalDegree ≤ n) (hb : 1+2*b.totalDegree ≤ n)
    (hc : 1+2*c.totalDegree ≤ n) (hd : 2+2*d.totalDegree ≤ n) :
    (squareForm a b c d).totalDegree ≤ n := by
  unfold squareForm
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    apply max_le
    · apply (totalDegree_add _ _).trans
      exact max_le (by simpa only [square_degree] using ha)
        ((totalDegree_mul _ _).trans (by simpa only [totalDegree_X,square_degree] using hb))
    · exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_X,square_degree] using hc)
  · have h := (totalDegree_mul (X (0 : Fin 2) : Plane K) (X 1))
    exact (totalDegree_mul _ _).trans (by simp only [totalDegree_X,square_degree] at *; omega)

omit [CharP K 2] in
lemma subtract_top_degree {p : Plane K} {n : ℕ} (hp : p.totalDegree ≤ n+1) :
    (p-homogeneousComponent (n+1) p).totalDegree ≤ n := by
  classical
  apply Finset.sup_le
  intro m hm
  have hc := mem_support_iff.mp hm
  rw [coeff_sub,coeff_homogeneousComponent] at hc
  change m.degree ≤ n
  by_contra! hn
  by_cases he : m.degree=n+1
  · exact hc (by simp [he])
  · have hz : p.coeff m=0 := coeff_eq_zero_of_totalDegree_lt (by change p.totalDegree < m.degree; omega)
    exact hc (by simp [he,hz])

lemma squareForm_top_even {a b c d : Plane K} {r : ℕ} (hr : 2 ≤ r)
    (hf : (squareForm a b c d).totalDegree ≤ 2*r) :
    homogeneousComponent (2*r) (squareForm a b c d) =
      squareForm (homogeneousComponent r a) 0 0 (homogeneousComponent (r-1) d) := by
  let A := homogeneousComponent r a
  let D := homogeneousComponent (r-1) d
  have hdeg := squareForm_degree_bounds (n := 2*r-2) (by omega :
    (squareForm a b c d).totalDegree ≤ (2*r-2)+2)
  have ha : 2*(a-A).totalDegree ≤ 2*r-1 := by
    have hh : (a-homogeneousComponent ((r-1)+1) a).totalDegree ≤ r-1 :=
      subtract_top_degree (by omega)
    have he : r-1+1=r := by omega
    rw [he] at hh
    change (a-A).totalDegree ≤ r-1 at hh
    omega
  have hd : 2+2*(d-D).totalDegree ≤ 2*r-1 := by
    have hh : (d-homogeneousComponent ((r-2)+1) d).totalDegree ≤ r-2 :=
      subtract_top_degree (by omega)
    have he : r-2+1=r-1 := by omega
    rw [he] at hh
    change (d-D).totalDegree ≤ r-2 at hh
    omega
  have hlow := squareForm_degree_le ha (by omega : 1+2*b.totalDegree ≤ 2*r-1)
    (by omega : 1+2*c.totalDegree ≤ 2*r-1) hd
  have hz : homogeneousComponent (2*r) (squareForm (a-A) b c (d-D))=0 :=
    homogeneousComponent_eq_zero _ _ (by omega)
  have htop : (squareForm A 0 0 D).IsHomogeneous (2*r) := by
    simp only [squareForm,zero_pow (by omega : 2 ≠ 0),mul_zero,add_zero]
    apply IsHomogeneous.add
    · convert (homogeneousComponent_isHomogeneous r a).pow 2 using 1; omega
    · convert ((isHomogeneous_X K (0 : Fin 2)).mul (isHomogeneous_X K 1)).mul
        ((homogeneousComponent_isHomogeneous (r-1) d).pow 2) using 1; omega
  have he : squareForm a b c d = squareForm A 0 0 D + squareForm (a-A) b c (d-D) := by
    rw [← squareForm_add]
    simp only [add_sub_cancel,zero_add]
  rw [he,map_add,homogeneousComponent_eq_self htop,hz,add_zero]

lemma squareForm_top_odd {a b c d : Plane K} {r : ℕ} (hr : 1 ≤ r)
    (hf : (squareForm a b c d).totalDegree ≤ 2*r+1) :
    homogeneousComponent (2*r+1) (squareForm a b c d) =
      squareForm 0 (homogeneousComponent r b) (homogeneousComponent r c) 0 := by
  let B := homogeneousComponent r b
  let C' := homogeneousComponent r c
  have hdeg := squareForm_degree_bounds (n := 2*r-1) (by omega :
    (squareForm a b c d).totalDegree ≤ (2*r-1)+2)
  have hb : 1+2*(b-B).totalDegree ≤ 2*r := by
    have hh : (b-homogeneousComponent ((r-1)+1) b).totalDegree ≤ r-1 :=
      subtract_top_degree (by omega)
    have he : r-1+1=r := by omega
    rw [he] at hh
    change (b-B).totalDegree ≤ r-1 at hh
    omega
  have hc : 1+2*(c-C').totalDegree ≤ 2*r := by
    have hh : (c-homogeneousComponent ((r-1)+1) c).totalDegree ≤ r-1 :=
      subtract_top_degree (by omega)
    have he : r-1+1=r := by omega
    rw [he] at hh
    change (c-C').totalDegree ≤ r-1 at hh
    omega
  have hlow := squareForm_degree_le (by omega : 2*a.totalDegree ≤ 2*r) hb hc
    (by omega : 2+2*d.totalDegree ≤ 2*r)
  have hz : homogeneousComponent (2*r+1) (squareForm a (b-B) (c-C') d)=0 :=
    homogeneousComponent_eq_zero _ _ (by omega)
  have htop : (squareForm 0 B C' 0).IsHomogeneous (2*r+1) := by
    simp only [squareForm,zero_pow (by omega : 2 ≠ 0),mul_zero,add_zero,zero_add]
    apply IsHomogeneous.add
    · convert (isHomogeneous_X K (0 : Fin 2)).mul
        ((homogeneousComponent_isHomogeneous r b).pow 2) using 1; omega
    · convert (isHomogeneous_X K (1 : Fin 2)).mul
        ((homogeneousComponent_isHomogeneous r c).pow 2) using 1; omega
  have he : squareForm a b c d = squareForm 0 B C' 0 + squareForm a (b-B) (c-C') d := by
    rw [← squareForm_add]
    simp only [add_sub_cancel,zero_add]
  rw [he,map_add,homogeneousComponent_eq_self htop,hz,add_zero]

end PermanentBorder.FrobeniusPlane
namespace PermanentBorder.FrobeniusPlane
open MvPolynomial
variable {K : Type*} [Field K] [CharP K 2]

omit [CharP K 2] in
lemma homogeneous_not_unit {p : Plane K} {n : ℕ} (hp : p.IsHomogeneous n)
    (hn : 0 < n) : ¬ IsUnit p := by
  intro hu
  have hz := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
  have he := hp.totalDegree hu.ne_zero
  omega

omit [CharP K 2] in
lemma squarefree_even_pair {a d : Plane K}
    (h : Squarefree (squareForm a 0 0 d)) : IsRelPrime a d := by
  intro g hga hgd
  apply h g
  simp only [squareForm,zero_pow (by omega : 2 ≠ 0),mul_zero,add_zero]
  apply dvd_add
  · simpa only [pow_two] using mul_dvd_mul hga hga
  · exact dvd_mul_of_dvd_right (by simpa only [pow_two] using mul_dvd_mul hgd hgd) _

omit [CharP K 2] in
lemma squarefree_odd_pair {b c : Plane K}
    (h : Squarefree (squareForm 0 b c 0)) : IsRelPrime b c := by
  intro g hgb hgc
  apply h g
  simp only [squareForm,zero_pow (by omega : 2 ≠ 0),mul_zero,add_zero,zero_add]
  exact dvd_add (dvd_mul_of_dvd_right (by simpa only [pow_two] using mul_dvd_mul hgb hgb) _)
    (dvd_mul_of_dvd_right (by simpa only [pow_two] using mul_dvd_mul hgc hgc) _)

lemma squarefree_even_leading {a b c d : Plane K} {r : ℕ} (hr : 2 ≤ r)
    (hf : (squareForm a b c d).totalDegree ≤ 2*r)
    (hs : Squarefree (homogeneousComponent (2*r) (squareForm a b c d))) :
    homogeneousComponent r a ≠ 0 ∧ homogeneousComponent (r-1) d ≠ 0 ∧
      IsRelPrime (homogeneousComponent r a) (homogeneousComponent (r-1) d) := by
  rw [squareForm_top_even hr hf] at hs
  have hp := squarefree_even_pair hs
  have ha := homogeneous_not_unit (homogeneousComponent_isHomogeneous r a) (by omega : 0 < r)
  have hd := homogeneous_not_unit (homogeneousComponent_isHomogeneous (r-1) d) (by omega : 0 < r-1)
  refine ⟨?_,?_,hp⟩
  · intro hz
    apply hd
    exact hp (by rw [hz]; exact dvd_zero _) dvd_rfl
  · intro hz
    apply ha
    exact hp dvd_rfl (by rw [hz]; exact dvd_zero _)

lemma squarefree_odd_leading {a b c d : Plane K} {r : ℕ} (hr : 1 ≤ r)
    (hf : (squareForm a b c d).totalDegree ≤ 2*r+1)
    (hs : Squarefree (homogeneousComponent (2*r+1) (squareForm a b c d))) :
    homogeneousComponent r b ≠ 0 ∧ homogeneousComponent r c ≠ 0 ∧
      IsRelPrime (homogeneousComponent r b) (homogeneousComponent r c) := by
  rw [squareForm_top_odd hr hf] at hs
  have hp := squarefree_odd_pair hs
  have hb := homogeneous_not_unit (homogeneousComponent_isHomogeneous r b) (by omega : 0 < r)
  have hc := homogeneous_not_unit (homogeneousComponent_isHomogeneous r c) (by omega : 0 < r)
  refine ⟨?_,?_,hp⟩
  · intro hz
    exact hc (hp (by rw [hz]; exact dvd_zero _) dvd_rfl)
  · intro hz
    exact hb (hp dvd_rfl (by rw [hz]; exact dvd_zero _))

end PermanentBorder.FrobeniusPlane

namespace PermanentBorder.BinaryLeading
open MvPolynomial
variable {K : Type*} [Field K]

noncomputable def linear (t : K) : MvPolynomial (Fin 2) K := X 1+C t*X 0

lemma linear_irreducible (t : K) : Irreducible (linear t) := by
  have h := irreducible_mul_X_add (1 : MvPolynomial (Fin 2) K) (C t*X 0) 1
    one_ne_zero (by simp) (by
      intro hh
      have := vars_mul (C t : MvPolynomial (Fin 2) K) (X 0) hh
      simp at this) (isRelPrime_one_left)
  simpa only [one_mul,linear] using h

lemma linear_eval (a t : K) : eval ![1,-a] (linear t) = t-a := by
  simp [linear,sub_eq_add_neg,add_comm]

lemma linear_pair {a b : K} (hab : a ≠ b) : IsRelPrime (linear a) (linear b) := by
  apply (linear_irreducible a).isRelPrime_iff_not_dvd.mpr
  intro h
  have hh := map_dvd (eval ![1,-a]) h
  rw [linear_eval,linear_eval,sub_self,zero_dvd_iff,sub_eq_zero] at hh
  exact hab hh.symm

variable {ι : Type*} [Fintype ι]

lemma squarefree_product (t : ι → K) (ht : Function.Injective t) :
    Squarefree (∏ i, linear (t i)) := by
  classical
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i _ j _ hij
    exact linear_pair (fun h => hij (ht h))
  · intro i _
    exact (linear_irreducible (t i)).squarefree

lemma product_partial_coprime (t : ι → K) (ht : Function.Injective t) :
    IsRelPrime (∏ i, linear (t i)) (pderiv 1 (∏ i, linear (t i))) := by
  classical
  apply IsRelPrime.prod_left
  intro i hi
  apply (linear_irreducible (t i)).isRelPrime_iff_not_dvd.mpr
  intro hd
  let E := eval ![1,-t i]
  have hprod : (∏ j, linear (t j)) = linear (t i)*∏ j ∈ Finset.univ.erase i,linear (t j) :=
    (Finset.mul_prod_erase Finset.univ (fun j => linear (t j)) hi).symm
  have he : E (pderiv 1 (∏ j, linear (t j))) = ∏ j ∈ Finset.univ.erase i, (t j-t i) := by
    rw [hprod,pderiv_mul]
    have hdlin : pderiv 1 (linear (t i)) = 1 := by simp [linear]
    rw [hdlin,one_mul,map_add,map_mul]
    simp only [E,linear_eval,sub_self,zero_mul,add_zero,map_prod]
  have hh := map_dvd E hd
  rw [show E (linear (t i))=0 by simp [E,linear_eval],zero_dvd_iff,he] at hh
  obtain ⟨j,hj,hj0⟩ := Finset.prod_eq_zero_iff.mp hh
  have hji := (Finset.mem_erase.mp hj).1
  exact hji (ht (sub_eq_zero.mp hj0))

lemma product_nonzero (t : ι → K) : (∏ i, linear (t i)) ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact (linear_irreducible _).ne_zero

lemma product_partial_nonzero [Nonempty ι] (t : ι → K) (ht : Function.Injective t) :
    pderiv 1 (∏ i, linear (t i)) ≠ 0 := by
  intro hz
  have hunit := product_partial_coprime t ht dvd_rfl (by rw [hz]; exact dvd_zero _)
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hi : linear (t i) ∣ ∏ j, linear (t j) := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  exact (linear_irreducible (t i)).not_isUnit (isUnit_of_dvd_unit hi hunit)

end PermanentBorder.BinaryLeading
namespace PermanentBorder.PlaneHilbert
open MvPolynomial
variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

lemma leading_vanishing_mem (q : Plane (K := K) →ₐ[K] R) {p : Plane (K := K)} {e : ℕ}
    (hp : p.totalDegree ≤ e) (hq : q p=0) : q (homogeneousComponent e p) ∈ filtered q e := by
  have hh := sub_topComponent_mem_filtered q hp
  change q p-q (homogeneousComponent e p) ∈ filtered q e at hh
  rw [hq,zero_sub] at hh
  exact (Submodule.neg_mem_iff _).mp hh

theorem finite_of_leading_pair (q : Plane (K := K) →ₐ[K] R) (hq : Function.Surjective q)
    {p t : Plane (K := K)} {e f B : ℕ} (hp : p.totalDegree ≤ e) (ht : t.totalDegree ≤ f)
    (hqp : q p=0) (hqt : q t=0) (hp0 : homogeneousComponent e p ≠ 0)
    (ht0 : homogeneousComponent f t ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e p) (homogeneousComponent f t))
    (he : e ≤ B+1) (hf : f ≤ B+1) (hef : e+f ≤ 2*B+1) :
    Module.Finite K R ∧ Module.finrank K R ≤ 2*Module.finrank K (filtered q B) := by
  have hh := finite_interpolation_half q hq
    (SliceParameters.homogeneous_intWeight (homogeneousComponent_isHomogeneous e p))
    (SliceParameters.homogeneous_intWeight (homogeneousComponent_isHomogeneous f t))
    hp0 ht0 hcop (leading_vanishing_mem q hp hqp) (leading_vanishing_mem q ht hqt) he hf hef
  refine ⟨?_,hh.2⟩
  apply Module.Finite.of_surjective (filtered q (2*B)).subtype
  intro z
  exact ⟨⟨z,by rw [hh.1]; trivial⟩,rfl⟩

end PermanentBorder.PlaneHilbert

namespace PermanentBorder.CurveFamily
open MvPolynomial Module LowPlane PlaneHilbert FrobeniusPlane
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [CharP L 2]

noncomputable def halfIdeal (a b c d : Plane L) : Ideal (Plane L) := Ideal.span {a,b,c,d}

omit [CharP L 2] in
lemma halfIdeal_mem (a b c d : Plane L) :
    a ∈ halfIdeal a b c d ∧ b ∈ halfIdeal a b c d ∧ c ∈ halfIdeal a b c d ∧ d ∈ halfIdeal a b c d := by
  exact ⟨Ideal.subset_span (by simp),Ideal.subset_span (by simp),
    Ideal.subset_span (by simp),Ideal.subset_span (by simp)⟩

lemma halfIdeal_even_finite {a b c d : Plane L} {r : ℕ} (hr : 2 ≤ r)
    (hf : (squareForm a b c d).totalDegree ≤ 2*r)
    (hs : Squarefree (homogeneousComponent (2*r) (squareForm a b c d))) :
    let q := Ideal.Quotient.mkₐ L (halfIdeal a b c d)
    Module.Finite L (Plane L ⧸ halfIdeal a b c d) ∧
      finrank L (Plane L ⧸ halfIdeal a b c d) ≤ 2*finrank L (filtered q r) := by
  let q := Ideal.Quotient.mkₐ L (halfIdeal a b c d)
  have hm := halfIdeal_mem a b c d
  have hdeg := squareForm_degree_bounds (n := 2*r-2) (by simpa [show 2*r-2+2=2*r by omega] using hf)
  obtain ⟨ha0,hd0,hcop⟩ := squarefree_even_leading hr hf hs
  exact finite_of_leading_pair q Ideal.Quotient.mk_surjective
    (show a.totalDegree ≤ r by omega) (show d.totalDegree ≤ r-1 by omega)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hm.1) (Ideal.Quotient.eq_zero_iff_mem.mpr hm.2.2.2)
    ha0 hd0 hcop (by omega) (by omega) (by omega)

lemma halfIdeal_odd_finite {a b c d : Plane L} {r : ℕ} (hr : 1 ≤ r)
    (hf : (squareForm a b c d).totalDegree ≤ 2*r+1)
    (hs : Squarefree (homogeneousComponent (2*r+1) (squareForm a b c d))) :
    let q := Ideal.Quotient.mkₐ L (halfIdeal a b c d)
    Module.Finite L (Plane L ⧸ halfIdeal a b c d) ∧
      finrank L (Plane L ⧸ halfIdeal a b c d) ≤ 2*finrank L (filtered q r) := by
  let q := Ideal.Quotient.mkₐ L (halfIdeal a b c d)
  have hm := halfIdeal_mem a b c d
  have hdeg := squareForm_degree_bounds (n := 2*r-1) (by simpa [show 2*r-1+2=2*r+1 by omega] using hf)
  obtain ⟨hb0,hc0,hcop⟩ := squarefree_odd_leading hr hf hs
  exact finite_of_leading_pair q Ideal.Quotient.mk_surjective
    (show b.totalDegree ≤ r by omega) (show c.totalDegree ≤ r by omega)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hm.2.1) (Ideal.Quotient.eq_zero_iff_mem.mpr hm.2.2.1)
    hb0 hc0 hcop (by omega) (by omega) (by omega)

end PermanentBorder.CurveFamily

end OAI

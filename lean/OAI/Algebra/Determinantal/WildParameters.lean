import OAI.Algebra.Determinantal.DegreeBounds

namespace OAI

namespace PermanentBorder.CurveFamily
open MvPolynomial Module LowPlane PlaneHilbert FrobeniusPlane
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [CharP L 2]

lemma twice_choose_two (n : ℕ) : 2*((n+1).choose 2)=n*(n+1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.choose_succ_succ]
    simp only [Nat.choose_one_right]
    nlinarith

lemma even_count (r : ℕ) :
    2*(Fintype.card (Index (r-1)) + ∑ _ : Fin 3, Fintype.card (Index r)) = (2*r)*(2*r+1) := by
  simp only [LowPlane.card_index,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  cases r with
  | zero => norm_num
  | succ s =>
    simp only [Nat.add_sub_cancel]
    have h1 := twice_choose_two s
    have h2 := twice_choose_two (s+1)
    nlinarith

lemma odd_count (r : ℕ) :
    2*(Fintype.card (Index r) + ∑ i : Fin 3, Fintype.card (Index (![r+1,r,r] i))) =
      (2*r+1)*(2*r+2) := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.isValue,
    Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero,LowPlane.card_index]
  have h1 := twice_choose_two r
  have h2 := twice_choose_two (r+1)
  nlinarith

theorem wild_parameter_bound_even [Infinite K] [IsAlgClosed L]
    {a b c d : Plane L} {r : ℕ} (hr : 2 ≤ r)
    (hf : (squareForm a b c d).totalDegree ≤ 2*r)
    (hs : Squarefree (homogeneousComponent (2*r) (squareForm a b c d)))
    (t : Fin 4 → Plane K)
    (h : ∀ i s, (![r,r,r,r-1] i) ≤ s.degree →
      (![a,b,c,d] i).coeff s=algebraMap K L ((t i).coeff s)) :
    ∃ (E : IntermediateField K L) (n : ℕ), InField E a ∧ InField E b ∧ InField E c ∧
      InField E d ∧ Algebra.trdeg K E ≤ (n : Cardinal) ∧
      2*n+finrank L (Plane L ⧸ halfIdeal a b c d) ≤ (2*r)*(2*r+1) := by
  classical
  let q := Ideal.Quotient.mkₐ L (halfIdeal a b c d)
  obtain ⟨hfinite,hrank⟩ := halfIdeal_even_finite hr hf hs
  let := hfinite
  have hm := halfIdeal_mem a b c d
  have hd0 : d ≠ 0 := by
    intro hz
    have hh := (squarefree_even_leading hr hf hs).2.1
    exact hh (by rw [hz,map_zero])
  obtain ⟨E,n,hdE,hpE,hE,hn⟩ := four_polynomial_bound q Ideal.Quotient.mk_surjective
    (r-1) (fun _ => r) d ![a,b,c] (t 3) ![t 0,t 1,t 2] hd0
    (h 3) (by
      intro i
      fin_cases i
      · exact h 0
      · exact h 1
      · exact h 2)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hm.2.2.2)
    (by intro i; fin_cases i
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hm.1
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hm.2.1
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hm.2.2.1)
    (fun _ => hrank)
  exact ⟨E,n,hpE 0,hpE 1,hpE 2,hdE,hE,(hn.trans_eq (even_count r))⟩

theorem wild_parameter_bound_odd [Infinite K] [IsAlgClosed L]
    {a b c d : Plane L} {r : ℕ} (hr : 1 ≤ r)
    (hf : (squareForm a b c d).totalDegree ≤ 2*r+1)
    (hs : Squarefree (homogeneousComponent (2*r+1) (squareForm a b c d)))
    (t : Fin 4 → Plane K)
    (h : ∀ i s, (![r+1,r,r,r] i) ≤ s.degree →
      (![a,b,c,d] i).coeff s=algebraMap K L ((t i).coeff s)) :
    ∃ (E : IntermediateField K L) (n : ℕ), InField E a ∧ InField E b ∧ InField E c ∧
      InField E d ∧ Algebra.trdeg K E ≤ (n : Cardinal) ∧
      2*n+finrank L (Plane L ⧸ halfIdeal a b c d) ≤ (2*r+1)*(2*r+2) := by
  classical
  let q := Ideal.Quotient.mkₐ L (halfIdeal a b c d)
  obtain ⟨hfinite,hrank⟩ := halfIdeal_odd_finite hr hf hs
  let := hfinite
  have hm := halfIdeal_mem a b c d
  have hb0 : b ≠ 0 := by
    intro hz
    have hh := (squarefree_odd_leading hr hf hs).1
    exact hh (by rw [hz,map_zero])
  obtain ⟨E,n,hbE,hpE,hE,hn⟩ := four_polynomial_bound q Ideal.Quotient.mk_surjective
    r ![r+1,r,r] b ![a,c,d] (t 1) ![t 0,t 2,t 3] hb0 (h 1)
    (by intro i; fin_cases i
        exact h 0
        exact h 2
        exact h 3)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hm.2.1)
    (by intro i; fin_cases i
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hm.1
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hm.2.2.1
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hm.2.2.2)
    (by intro i
        apply hrank.trans
        apply Nat.mul_le_mul_left 2
        apply Submodule.finrank_mono
        apply filtered_mono
        fin_cases i <;> simp)
  exact ⟨E,n,hpE 0,hbE,hpE 1,hpE 2,hE,(hn.trans_eq (odd_count r))⟩

end PermanentBorder.CurveFamily
namespace PermanentBorder.CurveFamily
open MvPolynomial Module LowPlane PlaneHilbert
variable {L : Type*} [Field L]

lemma pointEvaluation_surjective {ι : Type*} [Fintype ι]
    (x : ι → Fin 2 → L) (hx : Function.Injective x) :
    Function.Surjective (pointEvaluation x) := by
  classical
  have hp : ∀ i j : ι, i ≠ j → ∃ p : MvPolynomial (Fin 2) L,
      eval (x i) p = 1 ∧ eval (x j) p = 0 := by
    intro i j hij
    have hne : ∃ k, x i k ≠ x j k := by
      by_contra! h
      exact hij (hx (funext h))
    obtain ⟨k,hk⟩ := hne
    refine ⟨C (x i k-x j k)⁻¹*(X k-C (x j k)),?_,?_⟩
    · simp only [map_mul,map_sub,eval_C,eval_X]
      exact inv_mul_cancel₀ (sub_ne_zero.mpr hk)
    · simp
  choose p hp using hp
  let P (i : ι) := ∏ j : {j // j ≠ i}, p i j.val (Ne.symm j.property)
  have he (i j : ι) : eval (x j) (P i) = if i=j then 1 else 0 := by
    dsimp [P]
    rw [map_prod]
    split_ifs with hij
    · subst j
      exact Finset.prod_eq_one fun z _ => (hp i z.val (Ne.symm z.property)).1
    · exact Finset.prod_eq_zero (Finset.mem_univ ⟨j,Ne.symm hij⟩)
        (hp i j hij).2
  intro y
  refine ⟨∑ i, C (y i)*P i,?_⟩
  ext j
  simp only [pointEvaluation_apply,map_sum,map_mul,eval_C,he]
  simp

lemma partial_leading (p : MvPolynomial (Fin 2) L) (n : ℕ) (i : Fin 2) :
    homogeneousComponent n (pderiv i p) = pderiv i (homogeneousComponent (n+1) p) := by
  ext s
  simp only [coeff_homogeneousComponent,coeff_pderiv]
  have he : (s+Finsupp.single i 1).degree = s.degree+1 := by
    simp only [map_add,Finsupp.degree_single]
  rw [he]
  split_ifs <;> simp_all

theorem distinct_critical_point_count {ι : Type*} [Fintype ι]
    (x : ι → Fin 2 → L) (hx : Function.Injective x)
    (f : MvPolynomial (Fin 2) L) (k R : ℕ) (hk : 1 ≤ k) (hR : k-1 ≤ 2*R)
    (hf : f.totalDegree ≤ k)
    (hlead : homogeneousComponent k f ≠ 0)
    (hpartial : pderiv 1 (homogeneousComponent k f) ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent k f) (pderiv 1 (homogeneousComponent k f)))
    (hzero : ∀ i, eval (x i) f=0) (hderiv : ∀ i, eval (x i) (pderiv 1 f)=0) :
    Fintype.card ι ≤ 8*finrank L (filtered (pointEvaluation x) R) := by
  let q := pointEvaluation x
  have he : homogeneousComponent (k-1) (pderiv 1 f)=pderiv 1 (homogeneousComponent k f) := by
    simpa only [Nat.sub_add_cancel hk] using partial_leading f (k-1) 1
  have hdeg : (pderiv 1 f).totalDegree ≤ k-1 :=
    FrobeniusPlane.partial_degree (by rwa [Nat.sub_add_cancel hk]) 1
  have hh := finite_of_leading_pair q (pointEvaluation_surjective x hx) hf hdeg
    (by ext i; exact hzero i) (by ext i; exact hderiv i) hlead
    (by rwa [he]) (by rwa [he]) (B := k-1) (by omega) (by omega) (by omega)
  have hrank : finrank L (filtered q (k-1)) ≤ finrank L (filtered q (2*R)) :=
    Submodule.finrank_mono (filtered_mono q hR)
  have hd := filtered_rank_double_le q R
  change Fintype.card ι ≤ 8*finrank L (filtered q R)
  simpa only [Module.finrank_pi,finrank_self,Finset.sum_const,Finset.card_univ,
    smul_eq_mul,mul_one] using (hh.2.trans (by omega))

end PermanentBorder.CurveFamily
namespace PermanentBorder.FrobeniusPlane
open MvPolynomial
variable {K L : Type*} [Field K] [Field L] [CharP K 2] [CharP L 2] [Algebra K L]

omit [CharP K 2] [CharP L 2] in
lemma squareForm_map (a b c d : Plane K) :
    (squareForm a b c d).map (algebraMap K L) =
      squareForm (a.map (algebraMap K L)) (b.map (algebraMap K L))
        (c.map (algebraMap K L)) (d.map (algebraMap K L)) := by
  simp [squareForm]

omit [CharP K 2] [CharP L 2] in
lemma high_coeff_of_top {p : Plane L} {t : Plane K} {n : ℕ}
    (hp : p.totalDegree ≤ n) (ht : t.IsHomogeneous n)
    (he : homogeneousComponent n p = t.map (algebraMap K L)) :
    ∀ s, n ≤ s.degree → p.coeff s=algebraMap K L (t.coeff s) := by
  intro s hs
  by_cases hsn : s.degree=n
  · have hh := congrArg (fun polynomial : Plane L => polynomial.coeff s) he
    simpa only [coeff_homogeneousComponent,hsn,ite_true,coeff_map] using hh
  · have hz : p.coeff s=0 := coeff_eq_zero_of_totalDegree_lt (by change _ < s.degree; omega)
    rw [hz,ht.coeff_eq_zero (by exact fun h => hsn h),map_zero]

omit [CharP K 2] [CharP L 2] in
lemma high_coeff_zero {p : Plane L} {n : ℕ} (h : p.totalDegree < n) :
    ∀ s, n ≤ s.degree → p.coeff s=algebraMap K L ((0 : Plane K).coeff s) := by
  intro s hs
  rw [AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply,map_zero]
  exact coeff_eq_zero_of_totalDegree_lt (by change _ < s.degree; omega)

theorem fixed_half_forms_even [PerfectRing K 2]
    {a b c d : Plane L} {r : ℕ} (hr : 2 ≤ r)
    (hf : (squareForm a b c d).totalDegree ≤ 2*r)
    (H : Plane K) (hH : H.IsHomogeneous (2*r))
    (he : homogeneousComponent (2*r) (squareForm a b c d)=H.map (algebraMap K L)) :
    ∃ t : Fin 4 → Plane K, ∀ i s, (![r,r,r,r-1] i) ≤ s.degree →
      (![a,b,c,d] i).coeff s=algebraMap K L ((t i).coeff s) := by
  obtain ⟨A,B,C,D,hrep⟩ := exists_squareForm H
  have hHdeg : (squareForm A B C D).totalDegree ≤ 2*r := by
    rw [← hrep]
    exact hH.totalDegree_le
  have htop := squareForm_top_even hr hHdeg
  rw [← hrep,homogeneousComponent_of_mem hH,ite_eq_left rfl] at htop
  rw [squareForm_top_even hr hf,htop,squareForm_map] at he
  simp only [map_zero] at he
  obtain ⟨ha,_,_,hd⟩ := squareForm_injective he
  have hdeg := squareForm_degree_bounds (n := 2*r-2)
    (by simpa only [show 2*r-2+2=2*r by omega] using hf)
  refine ⟨![homogeneousComponent r A,0,0,homogeneousComponent (r-1) D],?_⟩
  intro i
  fin_cases i <;> dsimp
  · exact high_coeff_of_top (by omega) (homogeneousComponent_isHomogeneous r A) ha
  · exact high_coeff_zero (by omega)
  · exact high_coeff_zero (by omega)
  · exact high_coeff_of_top (by omega) (homogeneousComponent_isHomogeneous (r-1) D) hd

theorem fixed_half_forms_odd [PerfectRing K 2]
    {a b c d : Plane L} {r : ℕ} (hr : 1 ≤ r)
    (hf : (squareForm a b c d).totalDegree ≤ 2*r+1)
    (H : Plane K) (hH : H.IsHomogeneous (2*r+1))
    (he : homogeneousComponent (2*r+1) (squareForm a b c d)=H.map (algebraMap K L)) :
    ∃ t : Fin 4 → Plane K, ∀ i s, (![r+1,r,r,r] i) ≤ s.degree →
      (![a,b,c,d] i).coeff s=algebraMap K L ((t i).coeff s) := by
  obtain ⟨A,B,C,D,hrep⟩ := exists_squareForm H
  have hHdeg : (squareForm A B C D).totalDegree ≤ 2*r+1 := by
    rw [← hrep]
    exact hH.totalDegree_le
  have htop := squareForm_top_odd hr hHdeg
  rw [← hrep,homogeneousComponent_of_mem hH,ite_eq_left rfl] at htop
  rw [squareForm_top_odd hr hf,htop,squareForm_map] at he
  simp only [map_zero] at he
  obtain ⟨_,hb,hc,_⟩ := squareForm_injective he
  have hdeg := squareForm_degree_bounds (n := 2*r-1)
    (by simpa only [show 2*r-1+2=2*r+1 by omega] using hf)
  refine ⟨![0,homogeneousComponent r B,homogeneousComponent r C,0],?_⟩
  intro i
  fin_cases i <;> dsimp
  · exact high_coeff_zero (by omega)
  · exact high_coeff_of_top (by omega) (homogeneousComponent_isHomogeneous r B) hb
  · exact high_coeff_of_top (by omega) (homogeneousComponent_isHomogeneous r C) hc
  · exact high_coeff_zero (by omega)

end PermanentBorder.FrobeniusPlane

namespace PermanentBorder.IdealColength
open Module
variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

theorem quotient_product_length (I B : Ideal R) (z : R) :
    Module.length K (R ⧸ (I ⊔ Ideal.span {z}*B)) ≤
      Module.length K (R ⧸ (I ⊔ Ideal.span {z})) + Module.length K (R ⧸ B) := by
  let J := I ⊔ Ideal.span {z}*B
  let H := I ⊔ Ideal.span {z}
  have hJH : J ≤ H := sup_le_sup_left (Ideal.mul_le_left) I
  let g : (R ⧸ J) →ₗ[K] (R ⧸ H) := (Ideal.Quotient.factorₐ K hJH).toLinearMap
  have hg : Function.Surjective g := Ideal.Quotient.factor_surjective hJH
  let μ : R →ₗ[K] (R ⧸ J) := (Ideal.Quotient.mkₐ K J).toLinearMap.comp (LinearMap.mulLeft K z)
  have hμ : B.restrictScalars K ≤ LinearMap.ker μ := by
    intro r hr
    change Ideal.Quotient.mk J (z*r) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact (show Ideal.span {z} * B ≤ J from le_sup_right) (Ideal.mul_mem_mul (Ideal.subset_span (by simp)) hr)
  let v : (R ⧸ B) →ₗ[K] (R ⧸ J) := (B.restrictScalars K).liftQ μ hμ
  have hv : LinearMap.range v = LinearMap.ker g := by
    apply le_antisymm
    · rintro _ ⟨a,rfl⟩
      obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective a
      change Ideal.Quotient.mk H (z*r) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ((show Ideal.span {z} ≤ H from le_sup_right) (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))))
    · intro a ha
      obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective a
      have hr : r ∈ H := Ideal.Quotient.eq_zero_iff_mem.mp ha
      obtain ⟨i,hi,j,hj,he⟩ := Submodule.mem_sup.mp hr
      obtain ⟨s,hs⟩ := Ideal.mem_span_singleton'.mp hj
      refine ⟨Ideal.Quotient.mk B s,?_⟩
      change Ideal.Quotient.mk J (z*s) = Ideal.Quotient.mk J r
      rw [← he,← hs,map_add,Ideal.Quotient.eq_zero_iff_mem.mpr ((show I ≤ J from le_sup_left) hi),zero_add]
      congr 1
      ring
  have hlen := Module.length_eq_add_of_exact (LinearMap.ker g).subtype g
    (Submodule.subtype_injective _) hg (LinearMap.exact_subtype_ker_map g)
  have hb : Module.length K (LinearMap.ker g) ≤ Module.length K (R ⧸ B) := by
    rw [← hv]
    exact Module.length_le_of_surjective v.rangeRestrict (by
      rintro ⟨x,y,rfl⟩
      exact ⟨y,rfl⟩)
  calc
    _ = Module.length K (LinearMap.ker g) + Module.length K (R ⧸ H) := hlen
    _ ≤ Module.length K (R ⧸ B) + Module.length K (R ⧸ H) := add_le_add hb le_rfl
    _ = _ := add_comm _ _
end PermanentBorder.IdealColength
namespace PermanentBorder.FrobeniusPlane
open MvPolynomial
variable {K : Type*} [Field K] [CharP K 2]

lemma square_mem_of_mem_span (s : Set (Plane K)) {p : Plane K}
    (hp : p ∈ Ideal.span s) : p^2 ∈ Ideal.span ((fun q : Plane K => q^2) '' s) := by
  have hs : Ideal.span s ≤ Ideal.comap (frobenius (Plane K) 2)
      (Ideal.span ((fun q : Plane K => q^2) '' s)) := by
    apply Ideal.span_le.mpr
    intro x hx
    exact Ideal.subset_span ⟨x,hx,rfl⟩
  exact hs hp

theorem frobenius_quotient_bound [PerfectRing K 2] (J H : Ideal (Plane K))
    [Module.Finite K (Plane K ⧸ J)]
    (hJ : ∀ p ∈ J, p^2 ∈ H) :
    ∃ (_ : Module.Finite K (Plane K ⧸ H)),
      Module.finrank K (Plane K ⧸ H) ≤ 4*Module.finrank K (Plane K ⧸ J) := by
  classical
  let b := Module.finBasis K (Plane K ⧸ J)
  let q := Ideal.Quotient.mkₐ K J
  let v := Ideal.Quotient.mkₐ K H
  let r : Fin (Module.finrank K (Plane K ⧸ J)) → Plane K :=
    fun i => Classical.choose (Ideal.Quotient.mk_surjective (b i))
  have hr : ∀ i, q (r i) = b i := fun i => Classical.choose_spec (Ideal.Quotient.mk_surjective (b i))
  let e : Fin 4 → Plane K := ![1,X 0,X 1,X 0*X 1]
  let u : Fin 4 × Fin (Module.finrank K (Plane K ⧸ J)) → (Plane K ⧸ H) :=
    fun i => v (e i.1 * (r i.2)^2)
  let W := Submodule.span K (Set.range u)
  have hsquare (p : Plane K) (j : Fin 4) : v (e j*p^2) ∈ W := by
    let c := b.repr (q p)
    let t : Plane K := ∑ i, c i • r i
    have ht : q t = q p := by
      simp only [t,map_sum,map_smul,hr]
      exact b.sum_repr (q p)
    have hz : p-t ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp (by
      change q (p-t) = 0
      rw [map_sub,ht,sub_self])
    have hpow : v (p^2) = v (t^2) := by
      have hh := Ideal.Quotient.eq_zero_iff_mem.mpr (hJ _ hz)
      change v ((p-t)^2) = 0 at hh
      rw [sub_pow_char,map_sub] at hh
      exact sub_eq_zero.mp hh
    have hsum : v (e j*p^2) = ∑ i, (c i)^2 • u (j,i) := by
      rw [map_mul,hpow,← map_mul]
      simp only [t,sum_pow_char,Finset.mul_sum,map_sum,smul_pow,mul_smul_comm,map_smul,u]
    rw [hsum]
    exact W.sum_mem (fun i _ => W.smul_mem _ (Submodule.subset_span ⟨(j,i),rfl⟩))
  have htop : W = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a,b,c,d,rfl⟩ := exists_squareForm p
    change v (squareForm a b c d) ∈ W
    simp only [squareForm,map_add]
    exact W.add_mem (W.add_mem (W.add_mem (by simpa [e] using hsquare a 0)
      (by simpa [e] using hsquare b 1)) (by simpa [e] using hsquare c 2))
      (by simpa [e] using hsquare d 3)
  have hfg : (⊤ : Submodule K (Plane K ⧸ H)).FG := by
    rw [← htop]
    exact Submodule.fg_span (Set.finite_range u)
  let hfinite : Module.Finite K (Plane K ⧸ H) := Module.Finite.of_fg_top hfg
  refine ⟨hfinite,?_⟩
  simpa using finrank_le_of_span_eq_top htop
end PermanentBorder.FrobeniusPlane
namespace PermanentBorder.CurveFamily
open MvPolynomial Module
variable {K : Type*} [Field K]

noncomputable def zeroEvaluation (I : Ideal (MvPolynomial (Fin 2) K)) :
    (MvPolynomial (Fin 2) K ⧸ I) →ₐ[K] (zeroLocus K I → K) :=
  Ideal.Quotient.liftₐ I (pointEvaluation (fun x : zeroLocus K I => x.val)) (by
    intro p hp
    ext x
    exact (mem_zeroLocus_iff.mp x.property) p hp)

lemma zeroEvaluation_surjective (I : Ideal (MvPolynomial (Fin 2) K))
    [Fintype (zeroLocus K I)] : Function.Surjective (zeroEvaluation I) := by
  intro z
  obtain ⟨p,hp⟩ := pointEvaluation_surjective (fun x : zeroLocus K I => x.val)
    Subtype.val_injective z
  exact ⟨Ideal.Quotient.mk I p,hp⟩

lemma finite_zeroLocus (I : Ideal (MvPolynomial (Fin 2) K))
    [Module.Finite K (MvPolynomial (Fin 2) K ⧸ I)] : Finite (zeroLocus K I) := by
  let v : zeroLocus K I → ((MvPolynomial (Fin 2) K ⧸ I) →ₐ[K] K) := fun x =>
    Ideal.Quotient.liftₐ I (aeval x.val) (mem_zeroLocus_iff.mp x.property)
  apply Finite.of_injective v
  intro x y hxy
  apply Subtype.ext
  funext i
  have h := congrArg (fun g : (MvPolynomial (Fin 2) K ⧸ I) →ₐ[K] K =>
    g (Ideal.Quotient.mk I (X i))) hxy
  simpa [v] using h

lemma zero_card_le_finrank (I : Ideal (MvPolynomial (Fin 2) K))
    [Module.Finite K (MvPolynomial (Fin 2) K ⧸ I)] [Fintype (zeroLocus K I)] :
    Fintype.card (zeroLocus K I) ≤ finrank K (MvPolynomial (Fin 2) K ⧸ I) := by
  simpa only [Module.finrank_pi, finrank_self, Finset.sum_const, Finset.card_univ,
    smul_eq_mul,mul_one] using
    LinearMap.finrank_le_finrank_of_surjective (f := (zeroEvaluation I).toLinearMap)
      (zeroEvaluation_surjective I)

lemma radical_length_eq_zero_card [IsAlgClosed K] (I : Ideal (MvPolynomial (Fin 2) K))
    [Fintype (zeroLocus K I)] :
    Module.length K (MvPolynomial (Fin 2) K ⧸ I.radical) = Fintype.card (zeroLocus K I) := by
  let g : MvPolynomial (Fin 2) K →ₐ[K] (zeroLocus K I → K) :=
    pointEvaluation (fun x : zeroLocus K I => x.val)
  have hg : Function.Surjective g := pointEvaluation_surjective _ Subtype.val_injective
  have hker : RingHom.ker g = I.radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := K) I]
    ext p
    simp only [RingHom.mem_ker]
    constructor
    · intro hp x hx
      have hh := congrFun hp ⟨x,hx⟩
      exact hh
    · intro hp
      ext x
      exact hp x.val x.property
  let e := Ideal.quotientEquivAlgOfEq K hker.symm
  let e' := Ideal.quotientKerAlgEquivOfSurjective hg
  rw [(e.trans e').toLinearEquiv.length_eq]
  simp [Module.length_eq_finrank]

end PermanentBorder.CurveFamily

end OAI

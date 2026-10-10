import OAI.NumberTheory.PowerFree.PairBoundaries

namespace OAI

namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators

noncomputable def pairToLaurent {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) : PairRing k q →+* AddMonoidAlgebra R (Fin n → ℤ) :=
  Ideal.Quotient.lift _ (pairLaurentMap k q) (by
    change Ideal.span (Set.range (pairRelation k q)) ≤ RingHom.ker (pairLaurentMap k q)
    apply Ideal.span_le.mpr
    rintro p ⟨i,rfl⟩
    exact pairLaurentMap_relation k q i)

noncomputable def pairCoordinate {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) (i : Fin n) : PairRing k q :=
  Ideal.Quotient.mk _ (X (Sum.inl i))

@[simp] theorem pairToLaurent_coordinate {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) (i : Fin n) :
    pairToLaurent k q (pairCoordinate k q i) =
      AddMonoidAlgebra.single (Pi.single i 1) 1 := by
  simp [pairToLaurent,pairCoordinate,pairLaurentMap]

@[simp] theorem pairToLaurent_C {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) (r : R) :
    pairToLaurent k q (Ideal.Quotient.mk _ (C r)) =
      AddMonoidAlgebra.single 0 r := by
  simp [pairToLaurent,pairLaurentMap]

theorem pairToLaurent_injective {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (k : ℕ) (q : Fin n → R) (hq : ∀ i, q i ≠ 0) :
    Function.Injective (pairToLaurent k q) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [pair_ideal_eq_ker k q hq]
  exact hx

theorem pairToLaurent_prod_coordinate {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) (m : Fin n → ℕ) :
    pairToLaurent k q (∏ i, pairCoordinate k q i ^ m i) =
      AddMonoidAlgebra.single (fun i => (m i : ℤ)) 1 := by
  classical
  simp only [map_prod,map_pow,pairToLaurent_coordinate,AddMonoidAlgebra.single_pow,
    one_pow,AddMonoidAlgebra.prod_single,Finset.prod_const_one]
  congr 1
  ext j
  simp [Finset.sum_apply,Pi.single_apply]

theorem pairLaurent_fractions {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) (z : AddMonoidAlgebra R (Fin n → ℤ)) :
    ∃ x y : PairRing k q, y ∈ Submonoid.closure (Set.range (pairCoordinate k q)) ∧
      z * pairToLaurent k q y = pairToLaurent k q x := by
  classical
  induction z using AddMonoidAlgebra.induction_on with
  | of e =>
    refine ⟨∏ i, pairCoordinate k q i ^ (e i).toNat,
      ∏ i, pairCoordinate k q i ^ (-e i).toNat,?_,?_⟩
    · exact Submonoid.prod_mem _ fun i _ => Submonoid.pow_mem _
        (Submonoid.subset_closure (show pairCoordinate k q i ∈
          Set.range (pairCoordinate k q) from ⟨i,rfl⟩)) _
    · change AddMonoidAlgebra.single e 1 * _ = _
      rw [pairToLaurent_prod_coordinate,pairToLaurent_prod_coordinate,
        AddMonoidAlgebra.single_mul_single,one_mul]
      congr 1
      ext i
      simp only [Pi.add_apply]
      omega
  | add z w hz hw =>
    obtain ⟨x,a,ha,hx⟩ := hz
    obtain ⟨y,b,hb,hy⟩ := hw
    refine ⟨x*b+y*a,a*b,Submonoid.mul_mem _ ha hb,?_⟩
    rw [map_add,map_mul,map_mul,map_mul,← hx,← hy]
    ring
  | smul r z hz =>
    obtain ⟨x,a,ha,hx⟩ := hz
    refine ⟨Ideal.Quotient.mk _ (C r)*x,a,ha,?_⟩
    rw [map_mul,pairToLaurent_C,← hx,← mul_assoc]
    congr 1
    ext e
    simp

theorem pairLaurent_isLocalization {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (k : ℕ) (q : Fin n → R) (hq : ∀ i, q i ≠ 0) :
    let : Algebra (PairRing k q) (AddMonoidAlgebra R (Fin n → ℤ)) :=
      (pairToLaurent k q).toAlgebra
    IsLocalization (Submonoid.closure (Set.range (pairCoordinate k q)))
      (AddMonoidAlgebra R (Fin n → ℤ)) := by
  let : Algebra (PairRing k q) (AddMonoidAlgebra R (Fin n → ℤ)) :=
    (pairToLaurent k q).toAlgebra
  apply (isLocalization_iff _ _).mpr
  refine ⟨?_,?_,?_⟩
  · intro y
    change IsUnit (pairToLaurent k q y.val)
    have hv : ∀ a ∈ Submonoid.closure (Set.range (pairCoordinate k q)),
        IsUnit (pairToLaurent k q a) := by
      intro a ha
      induction ha using Submonoid.closure_induction with
      | mem a ha =>
        obtain ⟨i,rfl⟩ := ha
        rw [pairToLaurent_coordinate]
        exact ⟨⟨AddMonoidAlgebra.single (Pi.single i 1) 1,
          AddMonoidAlgebra.single (-(Pi.single i 1)) 1,
          by simp [AddMonoidAlgebra.single_mul_single,AddMonoidAlgebra.one_def],
          by simp [AddMonoidAlgebra.single_mul_single,AddMonoidAlgebra.one_def]⟩,rfl⟩
      | one => simp
      | mul a b ha hb iha ihb => simpa only [map_mul] using iha.mul ihb
    exact hv y.val y.property
  · intro z
    obtain ⟨x,y,hy,hxy⟩ := pairLaurent_fractions k q z
    exact ⟨(x,⟨y,hy⟩),hxy⟩
  · intro x y he
    exact ⟨1,by simpa only [OneMemClass.coe_one,one_mul] using pairToLaurent_injective k q hq he⟩

end
section
open MvPolynomial

theorem pair_coordinate_prime {n : ℕ} {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] {k : ℕ} (hk : 0 < k)
    (q : Fin n → R) (φ : R →+* S) (i : Fin n) (hq0 : ∀ j, q j ≠ 0)
    (hker : RingHom.ker φ = Ideal.span {q i})
    (hq : ∀ j, j ≠ i → φ (q j) ≠ 0) :
    Prime (Ideal.Quotient.mk (Ideal.span (Set.range (pairRelation k q))) (X (Sum.inl i))) := by
  let I := Ideal.span (Set.range (pairRelation k q))
  let : I.IsPrime := pair_ideal_isPrime k q hq0
  have hprime : (I ⊔ Ideal.span {X (Sum.inl i)}).IsPrime :=
    pair_boundary_ideal_isPrime hk q φ i hker hq
  have hx0 : Ideal.Quotient.mk I (X (Sum.inl i)) ≠ 0 := by
    intro hx
    have hm := Ideal.Quotient.eq_zero_iff_mem.mp hx
    change X (Sum.inl i) ∈ Ideal.span (Set.range (pairRelation k q)) at hm
    rw [pair_ideal_eq_ker k q hq0] at hm
    change pairLaurentMap k q (X (Sum.inl i)) = 0 at hm
    simp [pairLaurentMap,AddMonoidAlgebra.single_eq_zero] at hm
  apply (Ideal.span_singleton_prime hx0).mp
  have : (I ⊔ Ideal.span {X (Sum.inl i)}).IsPrime := hprime
  have hp := Ideal.isPrime_map_quotientMk_of_isPrime
    (I := I) (p := I ⊔ Ideal.span {X (Sum.inl i)}) le_sup_left
  simpa only [Ideal.map_sup,Ideal.map_quotient_self,bot_sup_eq,Ideal.map_span,
    Set.image_singleton] using hp

theorem pair_root_coordinate_prime {n : ℕ} {K : Type*} [Field K]
    {k : ℕ} (hk : 0 < k) (θ : Fin n → K) (hθ : Function.Injective θ) (i : Fin n) :
    Prime (Ideal.Quotient.mk (Ideal.span (Set.range (pairRelation k
      (fun j => Polynomial.X-Polynomial.C (θ j)))) ) (X (Sum.inl i))) := by
  apply pair_coordinate_prime hk (fun j => Polynomial.X-Polynomial.C (θ j))
    (Polynomial.evalRingHom (θ i)) i
  · exact fun j => Polynomial.X_sub_C_ne_zero (θ j)
  · exact Polynomial.ker_evalRingHom _
  · intro j hj
    change Polynomial.eval (θ i) (Polynomial.X-Polynomial.C (θ j)) ≠ 0
    simp only [Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,sub_ne_zero]
    exact fun h => hj (hθ h.symm)

end

theorem extract_finite_nonunit_factors {R : Type*} [CommRing R] [IsDomain R]
    [WfDvdMonoid R] (s : Finset R) (hs : ∀ a ∈ s, ¬ IsUnit a)
    {c : R} (hc : c ≠ 0) :
    ∃ a ∈ Submonoid.closure (s : Set R), ∃ c' : R,
      c' ≠ 0 ∧ c = a*c' ∧ ∀ p ∈ s, ¬ p ∣ c' := by
  classical
  induction s using Finset.induction_on generalizing c with
  | empty => exact ⟨1,Submonoid.one_mem _,c,hc,by simp,by simp⟩
  | @insert p s hp ih =>
    obtain ⟨a,ha,q,hq,he,hnd⟩ := ih (fun r hr => hs r (Finset.mem_insert_of_mem hr)) hc
    obtain ⟨v,c',hn,he'⟩ := WfDvdMonoid.max_power_factor' hq (hs p (Finset.mem_insert_self ..))
    have hc' : c' ≠ 0 := by intro h; simp [he',h] at hq
    refine ⟨a*p^v,Submonoid.mul_mem _ ?_ ?_,c',hc',?_,?_⟩
    · exact Submonoid.closure_mono (by simp only [Finset.coe_insert]; exact Set.subset_insert p _) ha
    · exact Submonoid.pow_mem _ (Submonoid.subset_closure (Finset.mem_insert_self ..)) v
    · rw [he,he',mul_assoc]
    · intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hr
      · exact hn
      · intro hrc
        apply hnd r hr
        rw [he']
        exact dvd_mul_of_dvd_right hrc _

theorem extract_prime_equation_from_open {R S : Type*}
    [CommRing R] [IsDomain R] [WfDvdMonoid R] [CommRing S] [Algebra R S]
    (s : Finset R) [IsLocalization (Submonoid.closure (s : Set R)) S]
    (hs : ∀ a ∈ s, Prime a) {F : R} (hF : F ≠ 0)
    (hlocal : ((Ideal.span {F}).map (algebraMap R S)).IsPrime) :
    ∃ e ∈ Submonoid.closure (s : Set R), ∃ c : R,
      c ≠ 0 ∧ F = e*c ∧ (∀ a ∈ s, ¬ a ∣ c) ∧
      (Ideal.span {c}).IsPrime ∧
      ((Ideal.span {F}).map (algebraMap R S)) =
        ((Ideal.span {c}).map (algebraMap R S)) := by
  obtain ⟨e,he,c,hc,hFc,hdiv⟩ :=
    extract_finite_nonunit_factors s (fun a ha => (hs a ha).not_isUnit) hF
  have hu : IsUnit (algebraMap R S e) := IsLocalization.map_units S (⟨e,he⟩ : Submonoid.closure (s : Set R))
  have heq : ((Ideal.span {F}).map (algebraMap R S)) =
      ((Ideal.span {c}).map (algebraMap R S)) := by
    rw [hFc,Ideal.map_span,Ideal.map_span,Set.image_singleton,Set.image_singleton,map_mul]
    exact Ideal.span_singleton_mul_left_unit hu _
  refine ⟨e,he,c,hc,hFc,hdiv,?_,heq⟩
  apply principal_isPrime_of_localization_coordinates (S := S) (s : Set R) c hs hdiv
  rwa [← heq]

open MvPolynomial

theorem rootPair_extract_prime_cut {n : ℕ} {K : Type*} [Field K]
    {k : ℕ} (hk : 0 < k) (θ : Fin n → K) (hθ : Function.Injective θ) :
    let q : Fin n → Polynomial K := fun j => Polynomial.X-Polynomial.C (θ j)
    ∀ F : PairRing k q, F ≠ 0 →
      (Ideal.span {pairToLaurent k q F}).IsPrime →
      ∃ e ∈ Submonoid.closure (Set.range (pairCoordinate k q)), ∃ c : PairRing k q,
        c ≠ 0 ∧ F = e*c ∧ (∀ i, ¬ pairCoordinate k q i ∣ c) ∧
        (Ideal.span {c}).IsPrime ∧
        (Ideal.span {pairToLaurent k q F}) = (Ideal.span {pairToLaurent k q c}) := by
  classical
  dsimp only
  let q : Fin n → Polynomial K := fun j => Polynomial.X-Polynomial.C (θ j)
  change ∀ F : PairRing k q, _
  intro F hF hlocal
  let : (Ideal.span (Set.range (pairRelation k q))).IsPrime :=
    pair_ideal_isPrime k q (fun j => Polynomial.X_sub_C_ne_zero (θ j))
  let : Algebra (PairRing k q) (AddMonoidAlgebra (Polynomial K) (Fin n → ℤ)) :=
    (pairToLaurent k q).toAlgebra
  let s : Finset (PairRing k q) := Finset.univ.image (pairCoordinate k q)
  have hs : (s : Set (PairRing k q)) = Set.range (pairCoordinate k q) := by
    simp [s]
  let : IsLocalization (Submonoid.closure (s : Set (PairRing k q)))
      (AddMonoidAlgebra (Polynomial K) (Fin n → ℤ)) := by
    rw [hs]
    exact pairLaurent_isLocalization k q (fun j => Polynomial.X_sub_C_ne_zero (θ j))
  have hsp : ∀ a ∈ s, Prime a := by
    intro a ha
    have har : a ∈ Set.range (pairCoordinate k q) := by rw [← hs]; exact ha
    obtain ⟨i,rfl⟩ := har
    exact pair_root_coordinate_prime hk θ hθ i
  have hl : ((Ideal.span {F}).map
      (algebraMap (PairRing k q) (AddMonoidAlgebra (Polynomial K) (Fin n → ℤ)))).IsPrime := by
    simpa only [Ideal.map_span,Set.image_singleton,RingHom.algebraMap_toAlgebra] using hlocal
  obtain ⟨e,he,c,hc,hFc,hdiv,hprime,heq⟩ :=
    extract_prime_equation_from_open s hsp hF hl
  refine ⟨e,?_,c,hc,hFc,?_,hprime,?_⟩
  · rwa [← hs]
  · intro i
    apply hdiv
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  · simpa only [Ideal.map_span,Set.image_singleton,RingHom.algebraMap_toAlgebra] using heq

open MvPolynomial

noncomputable def pairEvaluation {n : ℕ} {K R S : Type*} [Field K]
    [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (k : ℕ) (q : Fin n → R) (f : R →ₐ[K] S) (a b : Fin n → S)
    (h : ∀ i, a i ^ k * b i = f (q i)) : PairRing k q →ₐ[K] S :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aevalTower f (Sum.elim a b)) (by
    change Ideal.span _ ≤ RingHom.ker (MvPolynomial.aevalTower f (Sum.elim a b)).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change MvPolynomial.aevalTower f (Sum.elim a b) (pairRelation k q i) = 0
    simp only [pairRelation,map_sub,map_mul,map_pow,MvPolynomial.aevalTower_X,
      MvPolynomial.aevalTower_C,Sum.elim_inl,Sum.elim_inr,h,sub_self])

@[simp] theorem pairEvaluation_mk {n : ℕ} {K R S : Type*} [Field K]
    [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (k : ℕ) (q : Fin n → R) (f : R →ₐ[K] S) (a b : Fin n → S)
    (h : ∀ i, a i ^ k * b i = f (q i)) (p : MvPolynomial (Fin n ⊕ Fin n) R) :
    pairEvaluation k q f a b h (Ideal.Quotient.mk _ p) =
      MvPolynomial.aevalTower f (Sum.elim a b) p := rfl

@[simp] theorem pairEvaluation_coeff {n : ℕ} {K R S : Type*} [Field K]
    [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (k : ℕ) (q : Fin n → R) (f : R →ₐ[K] S) (a b : Fin n → S)
    (h : ∀ i, a i ^ k * b i = f (q i)) (r : R) :
    pairEvaluation k q f a b h (pairCoeffMap k q r) = f r := by
  change MvPolynomial.aevalTower f (Sum.elim a b) (MvPolynomial.C r) = f r
  exact MvPolynomial.aevalTower_C _ _ _

theorem pairEvaluation_ext {n : ℕ} {K R S : Type*} [Field K]
    [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (k : ℕ) (q : Fin n → R) (f g : PairRing k q →ₐ[K] S)
    (hC : ∀ r, f (pairCoeffMap k q r) = g (pairCoeffMap k q r))
    (ha : ∀ i, f (Ideal.Quotient.mk _ (X (Sum.inl i))) =
      g (Ideal.Quotient.mk _ (X (Sum.inl i))))
    (hb : ∀ i, f (Ideal.Quotient.mk _ (X (Sum.inr i))) =
      g (Ideal.Quotient.mk _ (X (Sum.inr i)))) : f = g := by
  apply AlgHom.ext
  intro r
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective r
  induction p using MvPolynomial.induction_on with
  | C c => exact hC c
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,hp]
    cases i with
    | inl j => rw [ha]
    | inr j => rw [hb]

theorem pairCoordinate_equation {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) (i : Fin n) :
    (Ideal.Quotient.mk (Ideal.span (Set.range (pairRelation k q))) (X (Sum.inl i)))^k *
      Ideal.Quotient.mk _ (X (Sum.inr i)) = pairCoeffMap k q (q i) := by
  have h : Ideal.Quotient.mk (Ideal.span (Set.range (pairRelation k q)))
      (pairRelation k q i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)
  simpa only [pairRelation,map_sub,map_mul,map_pow,sub_eq_zero,pairCoeffMap,RingHom.comp_apply] using h

end QuarticPowerFree

end OAI

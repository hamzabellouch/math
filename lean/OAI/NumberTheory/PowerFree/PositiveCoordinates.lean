import OAI.NumberTheory.PowerFree.PrincipalLifts

namespace OAI

namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators

def positiveExponent {n : ℕ} : (Fin n →₀ ℕ) →+ (Fin n → ℤ) where
  toFun e i := e i
  map_zero' := by ext i; simp
  map_add' e f := by ext i; simp

noncomputable def positiveLaurentMap {n : ℕ} {R : Type*} [CommRing R] :
    MvPolynomial (Fin n) R →+* AddMonoidAlgebra R (Fin n → ℤ) :=
  AddMonoidAlgebra.mapDomainRingHom R positiveExponent

@[simp] theorem positiveLaurentMap_monomial {n : ℕ} {R : Type*} [CommRing R]
    (e : Fin n →₀ ℕ) (r : R) :
    positiveLaurentMap (monomial e r) = AddMonoidAlgebra.single (fun i => (e i : ℤ)) r := by
  exact AddMonoidAlgebra.mapDomain_single

@[simp] theorem positiveLaurentMap_C {n : ℕ} {R : Type*} [CommRing R] (r : R) :
    positiveLaurentMap (C r : MvPolynomial (Fin n) R) = AddMonoidAlgebra.single 0 r := by
  change positiveLaurentMap (monomial 0 r) = AddMonoidAlgebra.single (fun _ => (0 : ℤ)) r
  exact positiveLaurentMap_monomial 0 r

@[simp] theorem positiveLaurentMap_X {n : ℕ} {R : Type*} [CommRing R] (i : Fin n) :
    positiveLaurentMap (X i : MvPolynomial (Fin n) R) =
      AddMonoidAlgebra.single (Pi.single i 1) 1 := by
  classical
  rw [X,positiveLaurentMap_monomial]
  congr 1
  ext j
  simp [Finsupp.single_apply,Pi.single_apply,eq_comm]

theorem positiveLaurentMap_injective {n : ℕ} {R : Type*} [CommRing R] :
    Function.Injective (positiveLaurentMap : MvPolynomial (Fin n) R →+* _) := by
  apply AddMonoidAlgebra.mapDomain_injective
  intro e f h
  ext i
  have hi : (e i : ℤ) = (f i : ℤ) := congrFun h i
  exact_mod_cast hi

theorem positiveLaurentMap_prod_X {n : ℕ} {R : Type*} [CommRing R] (m : Fin n → ℕ) :
    positiveLaurentMap (∏ i, (X i : MvPolynomial (Fin n) R)^m i) =
      AddMonoidAlgebra.single (fun i => (m i : ℤ)) 1 := by
  classical
  simp only [map_prod,map_pow,positiveLaurentMap_X,AddMonoidAlgebra.single_pow,
    one_pow,AddMonoidAlgebra.prod_single,Finset.prod_const_one]
  congr 1
  ext j
  simp [Finset.sum_apply,Pi.single_apply]

theorem positiveLaurent_fractions {n : ℕ} {R : Type*} [CommRing R]
    (z : AddMonoidAlgebra R (Fin n → ℤ)) :
    ∃ x y : MvPolynomial (Fin n) R, y ∈ Submonoid.closure (Set.range X) ∧
      z * positiveLaurentMap y = positiveLaurentMap x := by
  classical
  induction z using AddMonoidAlgebra.induction_on with
  | of e =>
    refine ⟨∏ i, X i ^ (e i).toNat, ∏ i, X i ^ (-e i).toNat,?_,?_⟩
    · exact Submonoid.prod_mem _ fun i _ => Submonoid.pow_mem _
        (Submonoid.subset_closure (show X i ∈ Set.range (X : Fin n → MvPolynomial (Fin n) R) from ⟨i,rfl⟩)) _
    · change AddMonoidAlgebra.single e 1 * _ = _
      rw [positiveLaurentMap_prod_X,positiveLaurentMap_prod_X,
        AddMonoidAlgebra.single_mul_single,one_mul]
      congr 1
      ext i
      simp only [Pi.add_apply]
      omega
  | add z w hz hw =>
    obtain ⟨x,a,ha,hx⟩ := hz
    obtain ⟨y,b,hb,hy⟩ := hw
    refine ⟨x*b+y*a,a*b,Submonoid.mul_mem _ ha hb,?_⟩
    rw [map_add,map_mul,map_mul,map_mul,←hx,←hy]
    ring
  | smul r z hz =>
    obtain ⟨x,a,ha,hx⟩ := hz
    refine ⟨C r*x,a,ha,?_⟩
    rw [map_mul,positiveLaurentMap_C,←hx,←mul_assoc]
    congr 1
    ext e
    simp

theorem positiveLaurent_isLocalization {n : ℕ} {R : Type*} [CommRing R] :
    let : Algebra (MvPolynomial (Fin n) R) (AddMonoidAlgebra R (Fin n → ℤ)) :=
      positiveLaurentMap.toAlgebra
    IsLocalization (Submonoid.closure (Set.range (X : Fin n → MvPolynomial (Fin n) R)))
      (AddMonoidAlgebra R (Fin n → ℤ)) := by
  let : Algebra (MvPolynomial (Fin n) R) (AddMonoidAlgebra R (Fin n → ℤ)) :=
    positiveLaurentMap.toAlgebra
  apply (isLocalization_iff _ _).mpr
  refine ⟨?_,?_,?_⟩
  · intro y
    change IsUnit (positiveLaurentMap y.val)
    have hu : ∀ a ∈ Submonoid.closure (Set.range (X : Fin n → MvPolynomial (Fin n) R)),
        IsUnit (positiveLaurentMap a) := by
      intro a ha
      induction ha using Submonoid.closure_induction with
      | mem a ha =>
        obtain ⟨i,rfl⟩ := ha
        rw [positiveLaurentMap_X]
        exact ⟨⟨AddMonoidAlgebra.single (Pi.single i 1) 1,
          AddMonoidAlgebra.single (-(Pi.single i 1)) 1,
          by simp [AddMonoidAlgebra.single_mul_single,AddMonoidAlgebra.one_def],
          by simp [AddMonoidAlgebra.single_mul_single,AddMonoidAlgebra.one_def]⟩,rfl⟩
      | one => simp
      | mul a b ha hb iha ihb => simpa only [map_mul] using iha.mul ihb
    exact hu y.val y.property
  · intro z
    obtain ⟨x,y,hy,hxy⟩ := positiveLaurent_fractions z
    exact ⟨(x,⟨y,hy⟩),hxy⟩
  · intro x y he
    exact ⟨1,by simpa only [OneMemClass.coe_one,one_mul] using positiveLaurentMap_injective he⟩

end
open MvPolynomial

noncomputable def positiveToPair {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) : MvPolynomial (Fin n) R →+* PairRing k q :=
  MvPolynomial.eval₂Hom (pairCoeffMap k q) (pairCoordinate k q)

@[simp] theorem positiveToPair_C {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) (r : R) :
    positiveToPair k q (C r) = pairCoeffMap k q r := by
  simp [positiveToPair]

@[simp] theorem positiveToPair_X {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) (i : Fin n) :
    positiveToPair k q (X i) = pairCoordinate k q i := by
  simp [positiveToPair]

theorem positiveToPair_toLaurent {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) (p : MvPolynomial (Fin n) R) :
    pairToLaurent k q (positiveToPair k q p) = positiveLaurentMap p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [pairCoeffMap]
  | add p r hp hr => simp only [map_add,hp,hr]
  | mul_X p i hp => simp only [map_mul,hp,positiveToPair_X,pairToLaurent_coordinate,positiveLaurentMap_X]

theorem pair_laurent_evaluation {n : ℕ} {R L : Type*} [CommRing R] [Field L]
    (k : ℕ) (q : Fin n → R) (ψ : PairRing k q →+* L)
    (ℓ : AddMonoidAlgebra R (Fin n → ℤ) →+* L)
    (ha : ∀ i, ψ (pairCoordinate k q i) ≠ 0)
    (hcomp : ∀ p, ℓ (positiveLaurentMap p) = ψ (positiveToPair k q p)) :
    ℓ.comp (pairToLaurent k q) = ψ := by
  have hC (r : R) : ℓ (pairToLaurent k q (pairCoeffMap k q r)) = ψ (pairCoeffMap k q r) := by
    simpa only [←positiveToPair_toLaurent k q,positiveToPair_C] using hcomp (C r)
  have hA (i : Fin n) : ℓ (pairToLaurent k q (pairCoordinate k q i)) = ψ (pairCoordinate k q i) := by
    simpa only [←positiveToPair_toLaurent k q,positiveToPair_X] using hcomp (X i)
  have hB (i : Fin n) : ℓ (pairToLaurent k q (Ideal.Quotient.mk _ (X (Sum.inr i)))) =
      ψ (Ideal.Quotient.mk _ (X (Sum.inr i))) := by
    apply mul_left_cancel₀ (pow_ne_zero k (ha i))
    have he1 := congrArg (fun x => ℓ (pairToLaurent k q x)) (pairCoordinate_equation k q i)
    have he2 := congrArg ψ (pairCoordinate_equation k q i)
    simp only [map_mul,map_pow] at he1 he2
    change ℓ (pairToLaurent k q (pairCoordinate k q i)) ^ k * _ = _ at he1
    rw [hA,hC] at he1
    exact he1.trans he2.symm
  apply RingHom.ext
  intro x
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C r => exact hC r
  | add p r hp hr => simpa only [map_add] using congrArg₂ (·+·) hp hr
  | mul_X p i hp =>
    simp only [RingHom.comp_apply,map_mul,hp]
    cases i with
    | inl j => rw [show Ideal.Quotient.mk _ (X (Sum.inl j)) = pairCoordinate k q j from rfl,hA]
    | inr j => rw [hB]

theorem positiveLaurent_kernel {n : ℕ} {R L : Type*} [CommRing R] [Field L]
    (φ : MvPolynomial (Fin n) R →+* L) (ha : ∀ i, φ (X i) ≠ 0) :
    ∃ ℓ : AddMonoidAlgebra R (Fin n → ℤ) →+* L,
      (∀ p, ℓ (positiveLaurentMap p) = φ p) ∧
      RingHom.ker ℓ = (RingHom.ker φ).map positiveLaurentMap := by
  let : Algebra (MvPolynomial (Fin n) R) (AddMonoidAlgebra R (Fin n → ℤ)) :=
    positiveLaurentMap.toAlgebra
  let M := Submonoid.closure (Set.range (X : Fin n → MvPolynomial (Fin n) R))
  let : IsLocalization M (AddMonoidAlgebra R (Fin n → ℤ)) := positiveLaurent_isLocalization
  have hu : ∀ y : M, IsUnit (φ y.val) := by
    intro y
    have hh : ∀ a ∈ M, IsUnit (φ a) := by
      intro a ha'
      induction ha' using Submonoid.closure_induction with
      | mem a ha' =>
        obtain ⟨i,rfl⟩ := ha'
        exact isUnit_iff_ne_zero.mpr (ha i)
      | one => simp
      | mul a b ha' hb' iha ihb => simpa only [map_mul] using iha.mul ihb
    exact hh y.val y.property
  let ℓ : AddMonoidAlgebra R (Fin n → ℤ) →+* L := IsLocalization.lift hu
  have hc : ∀ p, ℓ (positiveLaurentMap p) = φ p := IsLocalization.lift_eq hu
  refine ⟨ℓ,hc,?_⟩
  have hk : (RingHom.ker ℓ).under (MvPolynomial (Fin n) R) = RingHom.ker φ := by
    ext p
    change ℓ (positiveLaurentMap p) = 0 ↔ φ p = 0
    rw [hc]
  have hm := IsLocalization.map_under M (AddMonoidAlgebra R (Fin n → ℤ)) (RingHom.ker ℓ)
  rw [hk] at hm
  exact hm.symm

theorem rootPair_projection_kernel {n : ℕ} {K L : Type*} [Field K] [Field L]
    {k : ℕ} (hk : 0 < k) (θ : Fin n → K) (hθ : Function.Injective θ)
    (ψ : PairRing k (fun j => Polynomial.X-Polynomial.C (θ j)) →+* L)
    (ha : ∀ i, ψ (pairCoordinate k _ i) ≠ 0)
    (F : MvPolynomial (Fin n) (Polynomial K)) (hF : F ≠ 0)
    (hker : ∀ p, ψ (positiveToPair k _ p) = 0 ↔ F ∣ p) :
    ∃ c : PairRing k (fun j => Polynomial.X-Polynomial.C (θ j)),
      c ≠ 0 ∧ c ∣ positiveToPair k _ F ∧
      (∀ i, ¬ pairCoordinate k _ i ∣ c) ∧ RingHom.ker ψ = Ideal.span {c} := by
  let q : Fin n → Polynomial K := fun j => Polynomial.X-Polynomial.C (θ j)
  let : (Ideal.span (Set.range (pairRelation k q))).IsPrime :=
    pair_ideal_isPrime k q (fun j => Polynomial.X_sub_C_ne_zero (θ j))
  let φ := ψ.comp (positiveToPair k q)
  have haφ : ∀ i, φ (X i) ≠ 0 := by simpa only [φ,RingHom.comp_apply,positiveToPair_X] using ha
  obtain ⟨ℓ,hℓ,hkerℓ⟩ := positiveLaurent_kernel φ haφ
  have hℓpair : ℓ.comp (pairToLaurent k q) = ψ := pair_laurent_evaluation k q ψ ℓ ha hℓ
  have hkerφ : RingHom.ker φ = Ideal.span {F} := by
    ext p
    exact (hker p).trans Ideal.mem_span_singleton.symm
  rw [hkerφ,Ideal.map_span,Set.image_singleton] at hkerℓ
  have hpos : positiveToPair k q F ≠ 0 := by
    intro h
    have hh := congrArg (pairToLaurent k q) h
    rw [positiveToPair_toLaurent,map_zero] at hh
    exact hF (positiveLaurentMap_injective (hh.trans (map_zero positiveLaurentMap).symm))
  have hlocal : (Ideal.span {pairToLaurent k q (positiveToPair k q F)}).IsPrime := by
    rw [positiveToPair_toLaurent,←hkerℓ]
    exact RingHom.ker_isPrime ℓ
  obtain ⟨e,he,c,hc,hFc,hdiv,hprime,heq⟩ := rootPair_extract_prime_cut hk θ hθ
    (positiveToPair k q F) hpos hlocal
  refine ⟨c,hc,⟨e,by simpa [mul_comm] using hFc⟩,hdiv,?_⟩
  let : Algebra (PairRing k q) (AddMonoidAlgebra (Polynomial K) (Fin n → ℤ)) :=
    (pairToLaurent k q).toAlgebra
  let : IsLocalization (Submonoid.closure (Set.range (pairCoordinate k q)))
      (AddMonoidAlgebra (Polynomial K) (Fin n → ℤ)) :=
    pairLaurent_isLocalization k q (fun j => Polynomial.X_sub_C_ne_zero (θ j))
  have hp : ∀ a ∈ Set.range (pairCoordinate k q), Prime a := by
    rintro a ⟨i,rfl⟩
    exact pair_root_coordinate_prime hk θ hθ i
  have hd : ∀ a ∈ Set.range (pairCoordinate k q), ¬ a ∣ c := by
    rintro a ⟨i,rfl⟩
    exact hdiv i
  have hs := principal_under_map_coordinates (S := AddMonoidAlgebra (Polynomial K) (Fin n → ℤ))
    (Set.range (pairCoordinate k q)) c hp hd
  have hceq : RingHom.ker ℓ = Ideal.map (pairToLaurent k q) (Ideal.span {c}) := by
    rw [Ideal.map_span,Set.image_singleton,←heq,positiveToPair_toLaurent,←hkerℓ]
  rw [←hs]
  ext x
  change ψ x = 0 ↔ pairToLaurent k q x ∈ Ideal.map (pairToLaurent k q) (Ideal.span {c})
  rw [←hceq]
  change ψ x = 0 ↔ ℓ (pairToLaurent k q x) = 0
  rw [←RingHom.comp_apply,hℓpair]

open MvPolynomial
open scoped BigOperators

theorem homogeneous_aeval_monomial {σ K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (L : R →ₐ[K] Polynomial R) (z : σ → R) (w : σ → ℕ)
    (hz : ∀ i, L (z i) = Polynomial.monomial (w i) (z i))
    (m : σ →₀ ℕ) (a : K) :
    L (MvPolynomial.aeval z (monomial m a)) =
      Polynomial.monomial (Finsupp.weight w m) (MvPolynomial.aeval z (monomial m a)) := by
  let f : K →ₐ[K] R := Algebra.ofId K R
  have hf : MvPolynomial.aevalTower f z = MvPolynomial.aeval z := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  have hL : L.comp (MvPolynomial.aeval z) =
      MvPolynomial.aevalTower (L.comp f) (fun i => Polynomial.monomial (w i) (z i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa only [AlgHom.coe_comp,Function.comp_apply,aeval_X,aevalTower_X] using hz i
  have ha : (L.comp f) a = Polynomial.monomial 0 (f a) := by
    simp only [AlgHom.coe_comp,Function.comp_apply,f,Algebra.ofId_apply,L.commutes]
    rfl
  have hh := aevalTower_monomial_homogeneous f (L.comp f) z w m a 0 ha
  rw [←hL,hf] at hh
  simpa only [Nat.zero_add,AlgHom.coe_comp,Function.comp_apply] using hh

theorem polynomial_homogeneous_lift {σ K R S : Type*} [Field K] [CommRing R]
    [CommRing S] [Algebra K R] [Algebra K S]
    (L : R →ₐ[K] Polynomial R) (t : R) (ht : L t = Polynomial.monomial 1 t)
    (φ : R →ₐ[K] S) (hφ : φ t = 1)
    (z : σ → R) (w : σ → ℕ) (W : ℕ) (hw : ∀ i, w i ≤ W)
    (hz : ∀ i, L (z i) = Polynomial.monomial (w i) (z i))
    (p : MvPolynomial σ K) :
    ∃ c : R, L c = Polynomial.monomial (W*p.totalDegree) c ∧
      φ c = MvPolynomial.aeval (φ ∘ z) p := by
  classical
  let D := W*p.totalDegree
  have hm (m) (hm : m ∈ p.support) : Finsupp.weight w m ≤ D := by
    calc Finsupp.weight w m = ∑ i ∈ m.support, w i*m i := by
          simp [Finsupp.weight, Finsupp.linearCombination_apply, Finsupp.sum, mul_comm]
      _ ≤ ∑ i ∈ m.support, W*m i := Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_right _ (hw i))
      _ = W * ∑ i ∈ m.support, m i := by rw [Finset.mul_sum]
      _ ≤ D := Nat.mul_le_mul_left _ (le_totalDegree hm)
  let a (m : σ →₀ ℕ) := MvPolynomial.aeval z (monomial m (p.coeff m))
  let v (m : σ →₀ ℕ) := a m * t^(D-Finsupp.weight w m)
  have hv (m) (hm' : m ∈ p.support) : L (v m) = Polynomial.monomial D (v m) := by
    dsimp [v,a]
    rw [map_mul,homogeneous_aeval_monomial L z w hz,map_pow,ht,
      Polynomial.monomial_pow,one_mul,Polynomial.monomial_mul_monomial,Nat.add_sub_of_le (hm m hm')]
  refine ⟨∑ m ∈ p.support, v m,?_,?_⟩
  · simp only [map_sum]
    exact Finset.sum_congr rfl (fun m hm' => hv m hm')
  · have hvφ (m) : φ (v m) = MvPolynomial.aeval (φ ∘ z) (monomial m (p.coeff m)) := by
      simp only [v,map_mul,map_pow,hφ,one_pow,mul_one,a]
      have he : φ.comp (MvPolynomial.aeval z) = MvPolynomial.aeval (φ ∘ z) := by
        apply MvPolynomial.algHom_ext
        intro i
        simp
      exact AlgHom.congr_fun he _
    rw [map_sum]
    simp only [hvφ]
    rw [←map_sum,←p.as_sum]

end QuarticPowerFree

end OAI

import OAI.NumberTheory.PowerFree.LaurentCoordinates

namespace OAI

namespace QuarticPowerFree

section
open MvPolynomial

noncomputable def pairLeft {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) (i : Fin n) : PairRing k q :=
  Ideal.Quotient.mk _ (X (Sum.inl i))

noncomputable def pairRight {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) (i : Fin n) : PairRing k q :=
  Ideal.Quotient.mk _ (X (Sum.inr i))

@[simp] theorem pairEvaluation_left {n : ℕ} {K R S : Type*} [Field K]
    [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (k : ℕ) (q : Fin n → R) (f : R →ₐ[K] S) (a b : Fin n → S)
    (h : ∀ i, a i ^ k * b i = f (q i)) (i : Fin n) :
    pairEvaluation k q f a b h (pairLeft k q i) = a i := by
  simp [pairLeft]

@[simp] theorem pairEvaluation_right {n : ℕ} {K R S : Type*} [Field K]
    [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (k : ℕ) (q : Fin n → R) (f : R →ₐ[K] S) (a b : Fin n → S)
    (h : ∀ i, a i ^ k * b i = f (q i)) (i : Fin n) :
    pairEvaluation k q f a b h (pairRight k q i) = b i := by
  simp [pairRight]

@[simp] theorem pairCoeffMap_scalar {n : ℕ} {K R : Type*} [Field K]
    [CommRing R] [Algebra K R] (k : ℕ) (q : Fin n → R) (r : K) :
    pairCoeffMap k q (algebraMap K R r) = algebraMap K (PairRing k q) r := rfl

noncomputable def rootPairQ {n : ℕ} {K : Type*} [Field K]
    (θ : Fin n → K) (i : Fin n) : Polynomial K :=
  Polynomial.X - Polynomial.C (θ i)

abbrev RootPair {n : ℕ} {K : Type*} [Field K] (k : ℕ) (θ : Fin n → K) :=
  PairRing k (rootPairQ θ)

noncomputable def coneDifference {n : ℕ} {K : Type*} [Field K]
    (θ : Fin (n+1) → K) (j : Fin n) : K := θ 0 - θ j.succ

abbrev PairAffine {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin n → K) :=
  PairCone k A B θ ⧸ Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (X 2) - 1}

noncomputable def pairAffineMk {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin n → K) : PairCone k A B θ →ₐ[K] PairAffine k A B θ :=
  Ideal.Quotient.mkₐ K _

@[simp] theorem pairAffineMk_t {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin n → K) :
    pairAffineMk k A B θ (pairCoeffMap k (pairConeQ k A B θ) (X 2)) = 1 := by
  have h : pairAffineMk k A B θ (pairCoeffMap k (pairConeQ k A B θ) (X 2) - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  simpa only [map_sub,map_one,sub_eq_zero] using h

noncomputable def pairAffineLeft {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin n → K) (i : Fin (n+1)) : PairAffine k A B θ :=
  pairAffineMk k A B θ (pairConeA k A B θ i)

noncomputable def pairAffineRight {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin n → K) (i : Fin (n+1)) : PairAffine k A B θ :=
  pairAffineMk k A B θ (pairConeB k A B θ i)

lemma pairAffine_equation {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin n → K) (j : Fin n) :
    pairAffineLeft k A B θ j.succ ^ k * pairAffineRight k A B θ j.succ =
      pairAffineLeft k A B θ 0 ^ k * pairAffineRight k A B θ 0 +
        @algebraMap K (PairAffine k A B θ) inferInstance inferInstance inferInstance (θ j) := by
  exact pairCone_mapped_equation (S := PairAffine k A B θ)
    k A B θ (pairAffineMk k A B θ) (pairAffineMk_t k A B θ) j

lemma rootPair_equation {n : ℕ} {K : Type*} [Field K]
    (k : ℕ) (θ : Fin n → K) (i : Fin n) :
    pairLeft k (rootPairQ θ) i ^ k * pairRight k (rootPairQ θ) i =
      pairCoeffMap k (rootPairQ θ) Polynomial.X - algebraMap K (RootPair k θ) (θ i) := by
  have h := pairCoordinate_equation k (rootPairQ θ) i
  change pairLeft k (rootPairQ θ) i ^ k * pairRight k (rootPairQ θ) i = _ at h
  simpa only [rootPairQ,map_sub,Polynomial.C_eq_algebraMap,pairCoeffMap_scalar] using h

noncomputable def rootPairToAffine {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) :
    RootPair k θ →ₐ[K] PairAffine k A B (coneDifference θ) :=
  pairEvaluation (K := K) (S := PairAffine k A B (coneDifference θ)) k (rootPairQ θ)
    (Polynomial.aeval (pairAffineLeft k A B (coneDifference θ) 0 ^ k *
      pairAffineRight k A B (coneDifference θ) 0 + algebraMap K _ (θ 0)))
    (pairAffineLeft k A B (coneDifference θ))
    (pairAffineRight k A B (coneDifference θ)) (by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [rootPairQ,map_sub,Polynomial.aeval_X,Polynomial.aeval_C]
        ring
      · rw [pairAffine_equation]
        simp only [rootPairQ,map_sub,Polynomial.aeval_X,Polynomial.aeval_C,coneDifference,map_sub]
        ring)

noncomputable def pairConeToRoot {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) :
    PairCone k A B (coneDifference θ) →ₐ[K] RootPair k θ :=
  pairEvaluation k (pairConeQ k A B (coneDifference θ))
    (MvPolynomial.aeval ![pairLeft k (rootPairQ θ) 0,pairRight k (rootPairQ θ) 0,1])
    (fun j => pairLeft k (rootPairQ θ) j.succ)
    (fun j => pairRight k (rootPairQ θ) j.succ) (by
      intro i
      simp only [pairConeQ,map_add,map_mul,map_pow,MvPolynomial.aeval_X,
        MvPolynomial.aeval_C,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,one_pow,mul_one]
      rw [rootPair_equation,rootPair_equation]
      simp [coneDifference,sub_eq_add_neg,add_assoc])

@[simp] theorem pairConeToRoot_t {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) :
    pairConeToRoot k A B θ (pairCoeffMap k (pairConeQ k A B (coneDifference θ)) (X 2)) = 1 := by
  simp [pairConeToRoot]

@[simp] theorem pairConeToRoot_left {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) (i : Fin (n+1)) :
    pairConeToRoot k A B θ (pairConeA k A B (coneDifference θ) i) =
      pairLeft k (rootPairQ θ) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [pairConeA,pairConeToRoot]
  · change pairEvaluation _ _ _ _ _ _ (pairLeft _ _ j) = _
    simp

@[simp] theorem pairConeToRoot_right {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) (i : Fin (n+1)) :
    pairConeToRoot k A B θ (pairConeB k A B (coneDifference θ) i) =
      pairRight k (rootPairQ θ) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [pairConeB,pairConeToRoot]
  · change pairEvaluation _ _ _ _ _ _ (pairRight _ _ j) = _
    simp

noncomputable def pairAffineToRoot {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) :
    PairAffine k A B (coneDifference θ) →ₐ[K] RootPair k θ :=
  Ideal.Quotient.liftₐ _ (pairConeToRoot k A B θ) (by
    change Ideal.span _ ≤ RingHom.ker (pairConeToRoot k A B θ).toRingHom
    rw [Ideal.span_singleton_le_iff_mem]
    change pairConeToRoot k A B θ (_ - 1) = 0
    simp)

@[simp] theorem pairAffineToRoot_mk {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) (p : PairCone k A B (coneDifference θ)) :
    pairAffineToRoot k A B θ (pairAffineMk k A B (coneDifference θ) p) =
      pairConeToRoot k A B θ p := rfl

noncomputable def pairCoeffHom {n : ℕ} {K R : Type*} [Field K]
    [CommRing R] [Algebra K R] (k : ℕ) (q : Fin n → R) : R →ₐ[K] PairRing k q where
  toRingHom := pairCoeffMap k q
  commutes' := pairCoeffMap_scalar k q

@[simp] theorem rootPairToAffine_left {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) (i : Fin (n+1)) :
    rootPairToAffine k A B θ (pairLeft k (rootPairQ θ) i) =
      pairAffineLeft k A B (coneDifference θ) i := by
  simp [rootPairToAffine]

@[simp] theorem rootPairToAffine_right {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) (i : Fin (n+1)) :
    rootPairToAffine k A B θ (pairRight k (rootPairQ θ) i) =
      pairAffineRight k A B (coneDifference θ) i := by
  simp [rootPairToAffine]

@[simp] theorem pairAffineToRoot_left {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) (i : Fin (n+1)) :
    pairAffineToRoot k A B θ (pairAffineLeft k A B (coneDifference θ) i) =
      pairLeft k (rootPairQ θ) i := by
  simp [pairAffineLeft]

@[simp] theorem pairAffineToRoot_right {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) (i : Fin (n+1)) :
    pairAffineToRoot k A B θ (pairAffineRight k A B (coneDifference θ) i) =
      pairRight k (rootPairQ θ) i := by
  simp [pairAffineRight]

theorem pairAffineToRoot_leftInverse {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) :
    Function.LeftInverse (pairAffineToRoot k A B θ) (rootPairToAffine k A B θ) := by
  have h : (pairAffineToRoot k A B θ).comp (rootPairToAffine k A B θ) =
      AlgHom.id K (RootPair k θ) := by
    apply pairEvaluation_ext (K := K) k (rootPairQ θ)
    · have hc : ((pairAffineToRoot k A B θ).comp (rootPairToAffine k A B θ)).comp
            (pairCoeffHom (K := K) k (rootPairQ θ)) =
          (AlgHom.id K (RootPair k θ)).comp (pairCoeffHom (K := K) k (rootPairQ θ)) := by
        apply Polynomial.algHom_ext
        change pairAffineToRoot k A B θ
          (rootPairToAffine k A B θ (pairCoeffMap k (rootPairQ θ) Polynomial.X)) =
          pairCoeffMap k (rootPairQ θ) Polynomial.X
        simp only [rootPairToAffine,pairEvaluation_coeff,Polynomial.aeval_X,map_add,
          map_mul,map_pow,pairAffineToRoot_left,pairAffineToRoot_right,AlgHom.commutes,
          rootPair_equation,sub_add_cancel]
      intro r
      exact AlgHom.congr_fun hc r
    · intro i
      change pairAffineToRoot k A B θ (rootPairToAffine k A B θ (pairLeft _ _ i)) = _
      simp only [rootPairToAffine_left,pairAffineToRoot_left]
      rfl
    · intro i
      change pairAffineToRoot k A B θ (rootPairToAffine k A B θ (pairRight _ _ i)) = _
      simp only [rootPairToAffine_right,pairAffineToRoot_right]
      rfl
  intro x
  exact AlgHom.congr_fun h x

theorem rootPairToAffine_comp_cone {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) :
    (rootPairToAffine k A B θ).comp (pairConeToRoot k A B θ) =
      pairAffineMk k A B (coneDifference θ) := by
  apply pairEvaluation_ext (K := K) (S := PairAffine k A B (coneDifference θ)) k (pairConeQ k A B (coneDifference θ))
  · have hc : ((rootPairToAffine k A B θ).comp (pairConeToRoot k A B θ)).comp
          (pairCoeffHom (K := K) k (pairConeQ k A B (coneDifference θ))) =
        (pairAffineMk k A B (coneDifference θ)).comp
          (pairCoeffHom (K := K) k (pairConeQ k A B (coneDifference θ))) := by
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i
      · change rootPairToAffine k A B θ (pairConeToRoot k A B θ
            (pairConeA k A B (coneDifference θ) 0)) = _
        simp only [pairConeToRoot_left,rootPairToAffine_left,pairAffineLeft]
        rfl
      · change rootPairToAffine k A B θ (pairConeToRoot k A B θ
            (pairConeB k A B (coneDifference θ) 0)) = _
        simp only [pairConeToRoot_right,rootPairToAffine_right,pairAffineRight]
        rfl
      · change rootPairToAffine k A B θ (pairConeToRoot k A B θ
            (pairCoeffMap k (pairConeQ k A B (coneDifference θ)) (X 2))) = _
        simp only [pairConeToRoot_t,map_one]
        exact (pairAffineMk_t k A B (coneDifference θ)).symm
    intro r
    exact AlgHom.congr_fun hc r
  · intro i
    change rootPairToAffine k A B θ (pairConeToRoot k A B θ
      (pairConeA k A B (coneDifference θ) i.succ)) = _
    simp only [pairConeToRoot_left,rootPairToAffine_left,pairAffineLeft]
    rfl
  · intro i
    change rootPairToAffine k A B θ (pairConeToRoot k A B θ
      (pairConeB k A B (coneDifference θ) i.succ)) = _
    simp only [pairConeToRoot_right,rootPairToAffine_right,pairAffineRight]
    rfl

theorem pairAffineToRoot_rightInverse {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) :
    Function.RightInverse (pairAffineToRoot k A B θ) (rootPairToAffine k A B θ) := by
  intro x
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact AlgHom.congr_fun (rootPairToAffine_comp_cone k A B θ) p

noncomputable def rootPairAffineEquiv {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) :
    RootPair k θ ≃ₐ[K] PairAffine k A B (coneDifference θ) :=
  { rootPairToAffine k A B θ with
    invFun := pairAffineToRoot k A B θ
    left_inv := pairAffineToRoot_leftInverse k A B θ
    right_inv := pairAffineToRoot_rightInverse k A B θ }

end

theorem homogeneous_dehomogenization_zero {K R : Type*} [Field K] [CommRing R]
    [IsDomain R] [Algebra K R] (L : R →ₐ[K] Polynomial R)
    {t x : R} {D : ℕ} (ht0 : t ≠ 0)
    (ht : L t = Polynomial.monomial 1 t)
    (hx : L x = Polynomial.monomial D x)
    (hzero : Ideal.Quotient.mk (Ideal.span {t-1}) x = 0) : x = 0 := by
  let S := Localization.Away t
  let a : R →+* S := algebraMap R S
  let z : S := IsLocalization.Away.invSelf t
  let ev : R →+* S := (Polynomial.eval₂RingHom a z).comp L.toRingHom
  have het : ev (t-1) = 0 := by
    rw [map_sub,map_one,sub_eq_zero]
    change Polynomial.eval₂ a z (L t) = 1
    rw [ht,Polynomial.eval₂_monomial,pow_one]
    exact IsLocalization.Away.mul_invSelf t
  have hker : Ideal.span {t-1} ≤ RingHom.ker ev :=
    Ideal.span_le.mpr (by rintro _ rfl; exact het)
  have he : a x * z^D = 0 := by
    have h := hker (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
    change Polynomial.eval₂ a z (L x) = 0 at h
    rwa [hx,Polynomial.eval₂_monomial] at h
  have hz : z*a t = 1 := by
    rw [mul_comm]
    exact IsLocalization.Away.mul_invSelf t
  have hax : a x = 0 := by
    have h := congrArg (fun y : S => y*(a t)^D) he
    simpa only [mul_assoc,←mul_pow,hz,one_pow,mul_one,zero_mul] using h
  apply IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors ht0)
  simpa only [map_zero] using hax

theorem homogeneous_dehomogenization_eq {K R : Type*} [Field K] [CommRing R]
    [IsDomain R] [Algebra K R] (L : R →ₐ[K] Polynomial R)
    {t x y : R} {D : ℕ} (ht0 : t ≠ 0)
    (ht : L t = Polynomial.monomial 1 t)
    (hx : L x = Polynomial.monomial D x)
    (hy : L y = Polynomial.monomial D y)
    (he : Ideal.Quotient.mk (Ideal.span {t-1}) x =
      Ideal.Quotient.mk (Ideal.span {t-1}) y) : x = y := by
  apply sub_eq_zero.mp
  apply homogeneous_dehomogenization_zero L (D := D) ht0 ht
  · simp only [map_sub,hx,hy]
  · simp only [map_sub,he,sub_self]

theorem saturated_homogeneous_minimal_degree {K R : Type*} [Field K] [CommRing R]
    [IsDomain R] [Algebra K R] (L : R →ₐ[K] Polynomial R)
    {t x y : R} {D E : ℕ} (ht0 : t ≠ 0)
    (ht : L t = Polynomial.monomial 1 t)
    (hx : L x = Polynomial.monomial D x)
    (hy : L y = Polynomial.monomial E y) (hxt : ¬ t ∣ x)
    (he : Ideal.Quotient.mk (Ideal.span {t-1}) x =
      Ideal.Quotient.mk (Ideal.span {t-1}) y) : D ≤ E := by
  by_contra hn
  have hED : E < D := by omega
  have hEq : x = y*t^(D-E) := by
    apply homogeneous_dehomogenization_eq L ht0 ht hx
    · simp only [map_mul,map_pow,hy,ht,Polynomial.monomial_pow,one_mul,
        Polynomial.monomial_mul_monomial,Nat.add_sub_of_le (Nat.le_of_lt hED)]
    · have htone : Ideal.Quotient.mk (Ideal.span {t-1}) t = 1 := by
        have h : Ideal.Quotient.mk (Ideal.span {t-1}) (t-1) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
        simpa only [map_sub,map_one,sub_eq_zero] using h
      simp only [map_mul,map_pow,htone,one_pow,mul_one,he]
  apply hxt
  rw [hEq]
  exact dvd_mul_of_dvd_right (dvd_pow_self t (by omega)) y

theorem pairAffine_divisor_bounded_lift {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K)
    (r : PairCone k A B θ) (M : ℕ)
    (hM : ∀ i ∈ ((pairConeBasis k A B hB θ).repr r).support, pairBasisWeight A B i ≤ M)
    (hr : pairAffineMk k A B θ r ≠ 0)
    (x : PairAffine k A B θ) (hdiv : x ∣ pairAffineMk k A B θ r) :
    ∃ u v : ℕ, ∃ c : PairCone k A B θ, A*u+B*v ≤ M ∧
      pairConeScale k A B θ c = Polynomial.monomial (A*u+B*v) c ∧
      pairAffineMk k A B θ c = x ∧ c ≠ 0 ∧
      ¬ pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2) ∣ c := by
  let : (Ideal.span (Set.range (pairRelation k (pairConeQ k A B θ)))).IsPrime :=
    pair_ideal_isPrime k _ (pairConeQ_ne_zero k A B hB θ)
  obtain ⟨y,hxy⟩ := hdiv
  have hx0 : x ≠ 0 := by intro h; exact hr (hxy.trans (by rw [h]; exact zero_mul y))
  have hy0 : y ≠ 0 := by intro h; exact hr (hxy.trans (by rw [h]; exact mul_zero x))
  obtain ⟨rx,hrx⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨ry,hry⟩ := Ideal.Quotient.mk_surjective y
  have hrx0 : Ideal.Quotient.mk _ rx ≠ 0 := hrx ▸ hx0
  have hry0 : Ideal.Quotient.mk _ ry ≠ 0 := hry ▸ hy0
  obtain ⟨u,v,cx,hcx,hcxe,hcx0,hcxt⟩ := pairCone_minimal_lift k A B hB θ rx hrx0
  obtain ⟨u',v',cy,hcy,hcye,hcy0,hcyt⟩ := pairCone_minimal_lift k A B hB θ ry hry0
  have hcxmap : pairAffineMk k A B θ cx = x := hcxe.trans hrx
  have hcymap : pairAffineMk k A B θ cy = y := hcye.trans hry
  let t := pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)
  have htp : Prime t := pairCone_t_prime k A B hB θ
  obtain ⟨cr,hcr,hcre⟩ := basis_homogeneous_lift_at_degree (S := PairAffine k A B θ)
    (pairConeScale k A B θ) (pairConeBasis k A B hB θ) (pairBasisWeight A B)
    (pairConeBasis_homogeneous k A B hB θ) t (pairCone_t_homogeneous k A B θ)
    (pairAffineMk k A B θ) (pairAffineMk_t k A B θ) r M hM
  have hhom : pairConeScale k A B θ (cx*cy) =
      Polynomial.monomial ((A*u+B*v)+(A*u'+B*v')) (cx*cy) := by
    simp only [map_mul,hcx,hcy,Polynomial.monomial_mul_monomial]
  have hnt : ¬ t ∣ cx*cy := fun h => (htp.dvd_or_dvd h).elim hcxt hcyt
  have he : Ideal.Quotient.mk (Ideal.span {t-1}) (cx*cy) =
      Ideal.Quotient.mk (Ideal.span {t-1}) cr := by
    change pairAffineMk k A B θ (cx*cy) = pairAffineMk k A B θ cr
    rw [map_mul,hcxmap,hcymap,hcre,←hxy]
  have hle := saturated_homogeneous_minimal_degree (pairConeScale k A B θ)
    htp.ne_zero (pairCone_t_homogeneous k A B θ) hhom hcr hnt he
  exact ⟨u,v,cx,(Nat.le_add_right _ _).trans hle,hcx,hcxmap,hcx0,hcxt⟩

end QuarticPowerFree

end OAI

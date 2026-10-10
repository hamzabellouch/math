import OAI.NumberTheory.PowerFree.HomogeneousLifts

namespace OAI

namespace QuarticPowerFree

section
open scoped BigOperators

theorem basis_homogeneous_lift_at_degree {ι K R S : Type*} [Field K] [CommRing R]
    [CommRing S] [Algebra K R] [Algebra K S]
    (L : R →ₐ[K] Polynomial R) (b : Module.Basis ι K R) (w : ι → ℕ)
    (hb : ∀ i, L (b i) = Polynomial.monomial (w i) (b i))
    (t : R) (ht : L t = Polynomial.monomial 1 t)
    (φ : R →ₐ[K] S) (hφ : φ t = 1) (r : R) (D : ℕ)
    (hD : ∀ i ∈ (b.repr r).support, w i ≤ D) :
    ∃ c : R, L c = Polynomial.monomial D c ∧ φ c = φ r := by
  classical
  let s := (b.repr r).support
  let c := ∑ i ∈ s, (b.repr r i) • (b i * t^(D-w i))
  refine ⟨c,?_,?_⟩
  · dsimp only [c]
    simp only [map_sum,map_smul,map_mul,map_pow,hb,ht]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Polynomial.monomial_pow,one_mul,Polynomial.monomial_mul_monomial,
      Nat.add_sub_of_le (hD i hi),Polynomial.smul_monomial]
  · dsimp only [c]
    simp only [map_sum,map_smul,map_mul,map_pow,hφ,one_pow,mul_one]
    simpa only [s,Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul]
      using congrArg φ (b.linearCombination_repr r)

theorem minimal_homogeneous_lift_bounded {ι K R S : Type*} [Field K] [CommRing R]
    [IsDomain R] [CommRing S] [Algebra K R] [Algebra K S]
    (L : R →ₐ[K] Polynomial R) (b : Module.Basis ι K R) (w : ι → ℕ)
    (hb : ∀ i, L (b i) = Polynomial.monomial (w i) (b i))
    (t : R) (ht0 : t ≠ 0) (ht : L t = Polynomial.monomial 1 t)
    (φ : R →ₐ[K] S) (hφ : φ t = 1) (r : R) (hr : φ r ≠ 0) (M : ℕ)
    (hM : ∀ i ∈ (b.repr r).support, w i ≤ M) :
    ∃ D : ℕ, ∃ c : R, D ≤ M ∧ L c = Polynomial.monomial D c ∧
      φ c = φ r ∧ c ≠ 0 ∧ ¬ t ∣ c := by
  classical
  have hbound := basis_homogeneous_lift_at_degree L b w hb t ht φ hφ r M hM
  have hex : ∃ D : ℕ, ∃ c : R, L c = Polynomial.monomial D c ∧ φ c = φ r :=
    ⟨M,hbound⟩
  let D := Nat.find hex
  obtain ⟨c,hc,hcr⟩ := Nat.find_spec hex
  have hc0 : c ≠ 0 := by
    intro h
    apply hr
    rw [← hcr,h,map_zero]
  refine ⟨D,c,Nat.find_min' hex hbound,hc,hcr,hc0,?_⟩
  rintro ⟨x,hx⟩
  have hDpos : 0 < D := by
    by_contra h
    have hD : D = 0 := by omega
    have he := congrArg (fun p : Polynomial R => p.coeff 0) hc
    change (L c).coeff 0 = (Polynomial.monomial D c).coeff 0 at he
    have hzero : (L c).coeff 0 = 0 := by
      rw [hx,map_mul,ht]
      simp [Polynomial.mul_coeff_zero]
    have he' : (0 : R) = c := by
      simpa only [hD,hzero,Polynomial.coeff_monomial_same] using he
    exact hc0 he'.symm
  have hdegree : L x = Polynomial.monomial (D-1) x :=
    homogeneous_division L ht0 ht (hx ▸ hc) hDpos
  have hxr : φ x = φ r := by
    rw [hx,map_mul,hφ,one_mul] at hcr
    exact hcr
  have hh : D ≤ D-1 := Nat.find_min' hex ⟨x,hdegree,hxr⟩
  omega

end

section

theorem pairCone_bounded_lift {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K)
    (r : PairCone k A B θ) (M : ℕ)
    (hM : ∀ i ∈ ((pairConeBasis k A B hB θ).repr r).support, pairBasisWeight A B i ≤ M)
    (hr : Ideal.Quotient.mk
      (Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1}) r ≠ 0) :
    ∃ u v : ℕ, ∃ c : PairCone k A B θ,
      A*u+B*v ≤ M ∧
      pairConeScale k A B θ c = Polynomial.monomial (A*u+B*v) c ∧
      Ideal.Quotient.mk
        (Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1}) c =
      Ideal.Quotient.mk
        (Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1}) r ∧
      c ≠ 0 ∧ ¬ pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2) ∣ c := by
  let : (Ideal.span (Set.range (pairRelation k (pairConeQ k A B θ)))).IsPrime :=
    pair_ideal_isPrime k _ (pairConeQ_ne_zero k A B hB θ)
  let t := pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)
  let I : Ideal (PairCone k A B θ) := Ideal.span {t-1}
  let φ : PairCone k A B θ →ₐ[K] (PairCone k A B θ) ⧸ I := Ideal.Quotient.mkₐ K I
  have ht : φ t = 1 := by
    have h : φ (t-1) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton _))
    simpa only [map_sub,map_one,sub_eq_zero] using h
  obtain ⟨D,c,hD,hc,hcr,hc0,hct⟩ := minimal_homogeneous_lift_bounded (K := K)
    (R := PairCone k A B θ) (S := (PairCone k A B θ) ⧸ I)
    (pairConeScale k A B θ) (pairConeBasis k A B hB θ) (pairBasisWeight A B)
    (pairConeBasis_homogeneous k A B hB θ) t (pairCone_t_prime k A B hB θ).ne_zero
    (pairCone_t_homogeneous k A B θ) φ ht r (show φ r ≠ 0 from hr) M hM
  obtain ⟨u,v,he⟩ := pairCone_homogeneous_degree k A B hB θ c D hc hct
  exact ⟨u,v,c,he ▸ hD,he ▸ hc,hcr,hc0,hct⟩

theorem pairCone_cut_hilbert_uniform {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hA : 0 < A) (hB : 0 < B) (u v : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (θ : Fin n → K) (c : PairCone k A B θ), c ≠ 0 →
      pairConeScale k A B θ c = Polynomial.monomial (A*u+B*v) c →
      ∀ T : ℕ, A*u+B*v ≤ T →
      |(Module.finrank K ((homogeneousSpace (pairConeScale k A B θ) T).map
        (Ideal.Quotient.mkₐ K (Ideal.span {c})).toLinearMap) : ℝ) -
        ((A*u+B*v : ℕ):ℝ)*((k*A+B : ℕ):ℝ)^n /
          (((n+1).factorial:ℝ)*(A:ℝ)^(n+1)*(B:ℝ)^(n+1))*(T:ℝ)^(n+1)| ≤
        C*((T:ℝ)+1)^n := by
  obtain ⟨C,hC0,herror⟩ := pairFilteredDifference_hilbert_error (h := n) (k := k) hA hB u v
  refine ⟨C,hC0,fun θ c hc hC T hT => ?_⟩
  let : (Ideal.span (Set.range (pairRelation k (pairConeQ k A B θ)))).IsPrime :=
    pair_ideal_isPrime k _ (pairConeQ_ne_zero k A B hB θ)
  let := pairCone_finite k A B hA hB θ (A*u+B*v+(T-(A*u+B*v)))
  have he := homogeneous_principal_finrank (pairConeScale k A B θ)
    (A*u+B*v) (T-(A*u+B*v)) c hc hC
  rw [Nat.add_sub_of_le hT, pairCone_finrank k A B hA hB θ,
    pairCone_finrank k A B hA hB θ] at he
  have he' := congrArg (Nat.cast : ℕ → ℝ) he
  push_cast at he'
  have h := herror T
  simp only [ite_eq_left hT] at h
  rw [← he', add_sub_cancel_right] at h
  exact h

theorem pairAffine_cut_hilbert_uniform {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hA : 0 < A) (hB : 0 < B) (u v : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (θ : Fin n → K) (c : PairCone k A B θ), c ≠ 0 →
      pairConeScale k A B θ c = Polynomial.monomial (A*u+B*v) c →
      ¬ pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2) ∣ c →
      ∀ T : ℕ, A*u+B*v ≤ T →
      |(Module.finrank K ((homogeneousSpace (pairConeScale k A B θ) T).map
        (Ideal.Quotient.mkₐ K (Ideal.span {c} ⊔
         Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1})).toLinearMap) : ℝ) -
        ((A*u+B*v : ℕ):ℝ)*((k*A+B : ℕ):ℝ)^n /
          (((n+1).factorial:ℝ)*(A:ℝ)^(n+1)*(B:ℝ)^(n+1))*(T:ℝ)^(n+1)| ≤
        C*((T:ℝ)+1)^n := by
  obtain ⟨C,hC0,herror⟩ := pairCone_cut_hilbert_uniform (n := n) (K := K) k A B hA hB u v
  refine ⟨C,hC0,fun θ c hc hC hinfty T hT => ?_⟩
  let : (Ideal.span (Set.range (pairRelation k (pairConeQ k A B θ)))).IsPrime :=
    pair_ideal_isPrime k _ (pairConeQ_ne_zero k A B hB θ)
  let := pairCone_finite k A B hA hB θ T
  rw [homogeneous_dehomogenization_finrank (pairConeScale k A B θ)
    (pairCone_t_prime k A B hB θ) hinfty (pairCone_t_homogeneous k A B θ) hC]
  exact herror θ c hc hC T hT

theorem pairAffine_bounded_hilbert_uniform {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hA : 0 < A) (hB : 0 < B) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (θ : Fin n → K) (r : PairCone k A B θ),
      (∀ i ∈ ((pairConeBasis k A B hB θ).repr r).support, pairBasisWeight A B i ≤ M) →
      Ideal.Quotient.mk
        (Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1}) r ≠ 0 →
      ∃ u v : ℕ, A*u+B*v ≤ M ∧ ∀ T : ℕ, M ≤ T →
      |(Module.finrank K ((homogeneousSpace (pairConeScale k A B θ) T).map
        (Ideal.Quotient.mkₐ K (Ideal.span {r} ⊔
         Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1})).toLinearMap) : ℝ) -
        ((A*u+B*v : ℕ):ℝ)*((k*A+B : ℕ):ℝ)^n /
          (((n+1).factorial:ℝ)*(A:ℝ)^(n+1)*(B:ℝ)^(n+1))*(T:ℝ)^(n+1)| ≤
        C*((T:ℝ)+1)^n := by
  classical
  choose C hC0 hC using fun u v =>
    pairAffine_cut_hilbert_uniform (n := n) (K := K) k A B hA hB u v
  let Ctotal : ℝ := ∑ u ∈ Finset.range (M+1), ∑ v ∈ Finset.range (M+1), C u v
  have htotal : 0 ≤ Ctotal := Finset.sum_nonneg fun u _ =>
    Finset.sum_nonneg fun v _ => hC0 u v
  refine ⟨Ctotal,htotal,fun θ r hM hr => ?_⟩
  obtain ⟨u,v,c,hD,hc,hcr,hc0,hct⟩ := pairCone_bounded_lift k A B hB θ r M hM hr
  have hu : u ≤ M := le_trans (le_trans (by simpa using Nat.mul_le_mul_right u hA)
    (Nat.le_add_right (A*u) (B*v))) hD
  have hv : v ≤ M := le_trans (le_trans (by simpa using Nat.mul_le_mul_right v hB)
    (Nat.le_add_left (B*v) (A*u))) hD
  have hsum : C u v ≤ Ctotal := by
    calc C u v ≤ ∑ j ∈ Finset.range (M+1), C u j :=
          Finset.single_le_sum (fun j _ => hC0 u j) (Finset.mem_range.mpr (by omega))
      _ ≤ Ctotal := Finset.single_le_sum (fun i _ =>
          Finset.sum_nonneg (fun j _ => hC0 i j)) (Finset.mem_range.mpr (by omega))
  have he : (Ideal.span {c} ⊔
      Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1} : Ideal (PairCone k A B θ)) =
      Ideal.span {r} ⊔
      Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1} :=
    span_sup_eq_of_quotient_eq _ c r hcr
  refine ⟨u,v,hD,fun T hT => ?_⟩
  have hbound := hC u v θ c hc0 hc hct T (hD.trans hT)
  rw [he] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_right hsum (by positivity))

open scoped BigOperators

noncomputable def pairAExponent {n k : ℕ} (i : PairBasisIndex n k) : Fin (n+1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => (pairIndexToTuple i j).1)

lemma pair_b_exponents_zero {n k A B D : ℕ} (i : PairBasisIndex n k)
    (hi : pairBasisWeight A B i = D) (hD : D < B) :
    ∀ j, (pairIndexToTuple i j).2 = 0 := by
  intro j
  have hj : A*(pairIndexToTuple i j).1+B*(pairIndexToTuple i j).2 ≤
      ∑ l, (A*(pairIndexToTuple i l).1+B*(pairIndexToTuple i l).2) :=
    Finset.single_le_sum (f := fun l : Fin (n+1) => A*(pairIndexToTuple i l).1+B*(pairIndexToTuple i l).2)
      (fun l _ => Nat.zero_le _) (Finset.mem_univ j)
  rw [pairBasisWeight_eq] at hi
  by_contra hn
  have hb : B ≤ B*(pairIndexToTuple i j).2 := by
    simpa using Nat.mul_le_mul_left B (show 1 ≤ (pairIndexToTuple i j).2 by omega)
  omega

lemma pairAExponent_injective_low {n k A B D : ℕ} (hD : D < B) :
    Function.Injective (fun i : { i : PairBasisIndex n k // pairBasisWeight A B i = D } =>
      pairAExponent i.val) := by
  intro i j he
  have ha (l) : (pairIndexToTuple i.val l).1 = (pairIndexToTuple j.val l).1 :=
    congrArg (fun m : Fin (n+1) →₀ ℕ => m l) he
  have hb := pair_b_exponents_zero i.val i.property hD
  have hb' := pair_b_exponents_zero j.val j.property hD
  have htup : pairIndexToTuple i.val = pairIndexToTuple j.val := by
    funext l
    exact Prod.ext (ha l) ((hb l).trans (hb' l).symm)
  have hi := i.property
  have hj := j.property
  rw [pairBasisWeight_eq,htup] at hi
  rw [pairBasisWeight_eq] at hj
  have ht : i.val.1 2 = j.val.1 2 := by omega
  apply Subtype.ext
  calc i.val = tupleBasisIndex (pairIndexToTuple i.val) (i.val.1 2)
        (pairIndexToTuple_normal i.val) := (tupleBasisIndex_pairIndexToTuple i.val).symm
    _ = tupleBasisIndex (pairIndexToTuple j.val) (j.val.1 2)
        (pairIndexToTuple_normal j.val) := by congr 1
    _ = j.val := tupleBasisIndex_pairIndexToTuple j.val

noncomputable def pairConeA {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin n → K) : Fin (n+1) → PairCone k A B θ :=
  Fin.cons (pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 0))
    (fun j => Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inl j)))

lemma monomial_eq_univ_prod {σ R : Type*} [Fintype σ] [CommSemiring R]
    (m : σ →₀ ℕ) (r : R) : MvPolynomial.monomial m r =
      MvPolynomial.C r * ∏ j, MvPolynomial.X j ^ m j := by
  rw [MvPolynomial.monomial_eq]
  congr 1
  exact Finsupp.prod_fintype _ _ (fun j => pow_zero _)

lemma pairConeBasis_map_low {n : ℕ} {K S : Type*} [Field K] [CommRing S] [Algebra K S]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K)
    (φ : PairCone k A B θ →ₐ[K] S)
    (ht : φ (pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)) = 1)
    (i : PairBasisIndex n k) (hb : ∀ j, (pairIndexToTuple i j).2 = 0) :
    φ (pairConeBasis k A B hB θ i) =
      MvPolynomial.aeval (φ ∘ pairConeA k A B θ) (MvPolynomial.monomial (pairAExponent i) (1 : K)) := by
  classical
  simp only [pairConeBasis,Module.Basis.smulTower_apply,pairNormalBasis_smul]
  change φ (Ideal.Quotient.mk _ (MvPolynomial.monomial i.2.val (MvPolynomial.monomial i.1 (1 : K)))) = _
  simp only [monomial_eq_univ_prod,map_mul,map_prod,map_pow,map_one,one_mul,
    MvPolynomial.aeval_X]
  have h0 : i.1 1 = 0 := hb 0
  have hs (j : Fin n) : i.2.val (Sum.inr j) = 0 := hb j.succ
  have ht' : φ (Ideal.Quotient.mk _ (MvPolynomial.C (MvPolynomial.X 2))) = 1 := ht
  simp only [Fintype.prod_sum_type]
  simp only [hs,pow_zero,Finset.prod_const_one,mul_one]
  simp [Fin.prod_univ_succ,h0,ht',pairAExponent,pairConeA,pairIndexToTuple,pairCoeffMap]

end

theorem pairCone_low_degree_injective {n : ℕ} {K S : Type*} [Field K]
    [CommRing S] [Algebra K S] (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K)
    (φ : PairCone k A B θ →ₐ[K] S)
    (ht : φ (pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)) = 1)
    (ha : AlgebraicIndependent K (φ ∘ pairConeA k A B θ))
    (c : PairCone k A B θ) (D : ℕ) (hD : D < B)
    (hc : pairConeScale k A B θ c = Polynomial.monomial D c) (hφ : φ c = 0) : c = 0 := by
  classical
  let b := pairConeBasis k A B hB θ
  let w := pairBasisWeight (n := n) (k := k) A B
  let e : {i : PairBasisIndex n k // w i = D} → PairCone k A B θ := fun i => b i.val
  have hlin : LinearIndependent K (φ.toLinearMap ∘ e) := by
    have hf := (MvPolynomial.basisMonomials (Fin (n+1)) K).linearIndependent.map'
      (MvPolynomial.aeval (φ ∘ pairConeA k A B θ)).toLinearMap
      (LinearMap.ker_eq_bot.mpr (algebraicIndependent_iff_injective_aeval.mp ha))
    have hg := hf.comp (fun i : {i : PairBasisIndex n k // w i = D} => pairAExponent i.val)
      (pairAExponent_injective_low hD)
    have hfun : (φ.toLinearMap ∘ e) =
        ((MvPolynomial.aeval (φ ∘ pairConeA k A B θ)).toLinearMap ∘
          (MvPolynomial.basisMonomials (Fin (n+1)) K)) ∘
            (fun i : {i : PairBasisIndex n k // w i = D} => pairAExponent i.val) := by
      funext i
      exact pairConeBasis_map_low k A B hB θ φ ht i.val
        (pair_b_exponents_zero i.val i.property hD)
    rw [hfun]
    exact hg
  have hdis := Submodule.range_ker_disjoint hlin
  have hspan : homogeneousSpace (pairConeScale k A B θ) D =
      Submodule.span K (Set.range e) := by
    rw [homogeneousSpace_eq_basis_span (pairConeScale k A B θ) b w
      (pairConeBasis_homogeneous k A B hB θ)]
    congr 1
    ext x
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,hi⟩,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨i.val,i.property,rfl⟩
  have hmem : c ∈ Submodule.span K (Set.range e) := by
    rw [← hspan]
    exact hc
  have hzero : c ∈ (⊥ : Submodule K (PairCone k A B θ)) :=
    (disjoint_iff_inf_le.mp hdis) ⟨hmem,hφ⟩
  exact hzero

theorem pairCone_independent_lift {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K) (r : PairCone k A B θ)
    (hr : Ideal.Quotient.mk
      (Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1}) r ≠ 0)
    (ha : AlgebraicIndependent K
      ((Ideal.Quotient.mkₐ K (Ideal.span {r} ⊔
        Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1})) ∘
          pairConeA k A B θ)) :
    ∃ u v : ℕ, ∃ c : PairCone k A B θ,
      B ≤ A*u+B*v ∧
      pairConeScale k A B θ c = Polynomial.monomial (A*u+B*v) c ∧
      Ideal.Quotient.mk
        (Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1}) c =
      Ideal.Quotient.mk
        (Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1}) r ∧
      c ≠ 0 ∧ ¬ pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2) ∣ c := by
  obtain ⟨u,v,c,hc,hcr,hc0,hct⟩ := pairCone_minimal_lift k A B hB θ r hr
  let I : Ideal (PairCone k A B θ) :=
    Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1}
  let J : Ideal (PairCone k A B θ) := Ideal.span {r} ⊔ I
  let φ : PairCone k A B θ →ₐ[K] (PairCone k A B θ) ⧸ J := Ideal.Quotient.mkₐ K J
  have ht : φ (pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)) = 1 := by
    have h : φ (pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        ((show I ≤ J from le_sup_right) (Ideal.subset_span (Set.mem_singleton _)))
    simpa only [map_sub,map_one,sub_eq_zero] using h
  have hφr : φ r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    ((show Ideal.span {r} ≤ J from le_sup_left) (Ideal.subset_span (Set.mem_singleton _)))
  have hφc : φ c = 0 := by
    have hcrI : (Ideal.Quotient.mk I) c = (Ideal.Quotient.mk I) r := hcr
    have hmem : c-r ∈ I := Ideal.Quotient.eq.mp hcrI
    have hmemJ : c-r ∈ J := (show I ≤ J from le_sup_right) hmem
    have hzero : φ (c-r) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmemJ
    have h : φ c = φ r := by simpa only [map_sub,sub_eq_zero] using hzero
    exact h.trans hφr
  have hD : B ≤ A*u+B*v := by
    by_contra hn
    apply hc0
    apply pairCone_low_degree_injective (S := (PairCone k A B θ) ⧸ J)
      k A B hB θ φ ht
    · exact ha
    · exact lt_of_not_ge hn
    · exact hc
    · exact hφc
  exact ⟨u,v,c,hD,hc,hcr,hc0,hct⟩

end QuarticPowerFree

end OAI

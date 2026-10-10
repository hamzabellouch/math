import OAI.NumberTheory.PowerFree.QuarticPairs

namespace OAI

namespace QuarticPowerFree

section
open scoped BigOperators

lemma pairCone_mapped_equation {n : ℕ} {K S : Type*} [Field K] [CommRing S] [Algebra K S]
    (k A B : ℕ) (θ : Fin n → K) (φ : PairCone k A B θ →ₐ[K] S)
    (ht : φ (pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)) = 1)
    (j : Fin n) :
    φ (pairConeA k A B θ j.succ)^k * φ (pairConeB k A B θ j.succ) =
      φ (pairConeA k A B θ 0)^k * φ (pairConeB k A B θ 0) + algebraMap K S (θ j) := by
  have h : Ideal.Quotient.mk (Ideal.span (Set.range (pairRelation k (pairConeQ k A B θ))))
      (pairRelation k (pairConeQ k A B θ) j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self j))
  have he := congrArg φ h
  simp only [pairRelation,map_sub,map_mul,map_pow,map_zero,sub_eq_zero] at he
  change φ (pairConeA k A B θ j.succ)^k * φ (pairConeB k A B θ j.succ) =
    φ (pairCoeffMap k (pairConeQ k A B θ) (pairConeQ k A B θ j)) at he
  rw [he]
  have hcoef (r : K) : φ (pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.C r)) =
      algebraMap K S r := φ.commutes r
  simp only [pairConeQ,map_add,map_mul,map_pow,hcoef,ht,one_pow,mul_one]
  rfl

theorem quartic_pair_small_field {K R S : Type*} [Field K] [CommRing R] [Field S]
    [Algebra K R] [Algebra K S]
    (A B : ℕ) (hB : 0 < B) (θ : Fin 1 → K)
    (φ : PairCone 2 A B θ →ₐ[K] R) (ψ : PairCone 2 A B θ →ₐ[K] S)
    (htφ : φ (pairCoeffMap 2 (pairConeQ 2 A B θ) (MvPolynomial.X 2)) = 1)
    (htψ : ψ (pairCoeffMap 2 (pairConeQ 2 A B θ) (MvPolynomial.X 2)) = 1)
    (c : PairCone 2 A B θ) (D : ℕ)
    (hc : pairConeScale 2 A B θ c = Polynomial.monomial D c)
    (hφ : φ c ≠ 0) (hψ : ψ c = 0)
    (ha : AlgebraicIndependent K (ψ ∘ pairConeA 2 A B θ))
    (h3 : D < 3*A) (h2 : D < 2*B) (hmix : D < A+B) :
    ∀ j, ψ (pairConeB 2 A B θ j) ∈
      IntermediateField.adjoin K (Set.range (ψ ∘ pairConeA 2 A B θ)) := by
  obtain ⟨q,hq,b,hb,hrel⟩ := pairCone_small_relation 2 A B hB θ φ ψ htφ htψ
    c D hc hφ hψ ha h3 h2 hmix
  let a' : Fin 2 → S := ψ ∘ pairConeA 2 A B θ
  let b' : Fin 2 → S := ψ ∘ pairConeB 2 A B θ
  let N : S := a' 0^2*b' 0
  let θ' : Fin 2 → K := ![0,-θ 0]
  have hcoeff : b 0 ≠ 0 ∨ b 1 ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hb
    funext j
    fin_cases j <;> simp [hn]
  have heq : ∀ j, a' j^2*b' j = N-algebraMap K S (θ' j) := by
    intro j
    fin_cases j
    · simp [N,θ']
    · change ψ (pairConeA 2 A B θ 1)^2 * ψ (pairConeB 2 A B θ 1) =
        ψ (pairConeA 2 A B θ 0)^2 * ψ (pairConeB 2 A B θ 0) - algebraMap K S (-θ 0)
      have hj : (0 : Fin 1).succ = (1 : Fin 2) := by decide
      simpa only [map_neg,sub_neg_eq_add,hj] using pairCone_mapped_equation 2 A B θ ψ htψ 0
  have hrel' : algebraMap K S (b 0)*b' 0 + algebraMap K S (b 1)*b' 1 =
      MvPolynomial.aeval a' q := by
    change (∑ j : Fin 2, algebraMap K S (b j)*b' j) = MvPolynomial.aeval a' q at hrel
    rwa [Fin.sum_univ_two] at hrel
  exact (quartic_paired_field a' b' ha N θ' b hcoeff q heq hrel').2

theorem pairAffine_bounded_cut_data {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hA : 0 < A) (hB : 0 < B) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (θ : Fin n → K) (r : PairCone k A B θ),
      (∀ i ∈ ((pairConeBasis k A B hB θ).repr r).support, pairBasisWeight A B i ≤ M) →
      Ideal.Quotient.mk
        (Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1}) r ≠ 0 →
      ∃ u v : ℕ, ∃ c : PairCone k A B θ,
      A*u+B*v ≤ M ∧
      pairConeScale k A B θ c = Polynomial.monomial (A*u+B*v) c ∧
      Ideal.Quotient.mk
        (Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1}) c =
      Ideal.Quotient.mk
        (Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1}) r ∧
      c ≠ 0 ∧ ¬ pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2) ∣ c ∧
      ∀ T : ℕ, M ≤ T →
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
  refine ⟨u,v,c,hD,hc,hcr,hc0,hct,fun T hT => ?_⟩
  have hbound := hC u v θ c hc0 hc hct T (hD.trans hT)
  rw [he] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_right hsum (by positivity))

lemma pairCone_affine_eq_map {n : ℕ} {K S : Type*} [Field K] [CommRing S] [Algebra K S]
    (k A B : ℕ) (θ : Fin n → K) (ψ : PairCone k A B θ →ₐ[K] S)
    (ht : ψ (pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)) = 1)
    {c r : PairCone k A B θ}
    (hcr : Ideal.Quotient.mk
      (Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1}) c =
      Ideal.Quotient.mk
      (Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1}) r) :
    ψ c = ψ r := by
  have hI : Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1} ≤
      RingHom.ker ψ.toRingHom := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change ψ (_-1) = 0
    simp only [map_sub, map_one, ht, sub_self]
  have hz : ψ (c-r) = 0 := hI (Ideal.Quotient.eq.mp hcr)
  simpa only [map_sub,sub_eq_zero] using hz

end

theorem quartic_bounded_pair_alternative {K S : Type*} [Field K] [Field S] [Algebra K S]
    (A B : ℕ) (hA : 0 < A) (hB : 0 < B) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (θ : Fin 1 → K) (r : PairCone 2 A B θ)
      (ψ : PairCone 2 A B θ →ₐ[K] S),
      (∀ i ∈ ((pairConeBasis 2 A B hB θ).repr r).support, pairBasisWeight A B i ≤ M) →
      Ideal.Quotient.mk
        (Ideal.span {pairCoeffMap 2 (pairConeQ 2 A B θ) (MvPolynomial.X 2)-1}) r ≠ 0 →
      ψ (pairCoeffMap 2 (pairConeQ 2 A B θ) (MvPolynomial.X 2)) = 1 →
      ψ r = 0 → AlgebraicIndependent K (ψ ∘ pairConeA 2 A B θ) →
      ∃ D : ℕ, B ≤ D ∧ D ≤ M ∧
      (∀ T : ℕ, M ≤ T →
      |(Module.finrank K ((homogeneousSpace (pairConeScale 2 A B θ) T).map
        (Ideal.Quotient.mkₐ K (Ideal.span {r} ⊔
         Ideal.span {pairCoeffMap 2 (pairConeQ 2 A B θ) (MvPolynomial.X 2)-1})).toLinearMap) : ℝ) -
        (D:ℝ)*((2*A+B : ℕ):ℝ) /
          (2*(A:ℝ)^2*(B:ℝ)^2)*(T:ℝ)^2| ≤ C*((T:ℝ)+1)) ∧
      (min (3*A) (min (2*B) (A+B)) ≤ D ∨
        ∀ j, ψ (pairConeB 2 A B θ j) ∈
          IntermediateField.adjoin K (Set.range (ψ ∘ pairConeA 2 A B θ))) := by
  obtain ⟨C,hC0,hC⟩ := pairAffine_bounded_cut_data (n := 1) (K := K) 2 A B hA hB M
  refine ⟨C,hC0,fun θ r ψ hM hr htψ hψr ha => ?_⟩
  obtain ⟨u,v,c,hD,hc,hcr,hc0,hct,hE⟩ := hC θ r hM hr
  have hψc : ψ c = 0 := (pairCone_affine_eq_map 2 A B θ ψ htψ hcr).trans hψr
  have hDB : B ≤ A*u+B*v := by
    by_contra hn
    apply hc0
    apply pairCone_low_degree_injective (S := S) 2 A B hB θ ψ htψ
    · exact ha
    · exact lt_of_not_ge hn
    · exact hc
    · exact hψc
  refine ⟨A*u+B*v,hDB,hD,fun T hT => ?_,?_⟩
  · simpa using hE T hT
  · by_cases hlarge : min (3*A) (min (2*B) (A+B)) ≤ A*u+B*v
    · exact Or.inl hlarge
    · right
      let I : Ideal (PairCone 2 A B θ) :=
        Ideal.span {pairCoeffMap 2 (pairConeQ 2 A B θ) (MvPolynomial.X 2)-1}
      let φ : PairCone 2 A B θ →ₐ[K] (PairCone 2 A B θ) ⧸ I := Ideal.Quotient.mkₐ K I
      have htφ : φ (pairCoeffMap 2 (pairConeQ 2 A B θ) (MvPolynomial.X 2)) = 1 := by
        have hz : φ (pairCoeffMap 2 (pairConeQ 2 A B θ) (MvPolynomial.X 2)-1) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
        simpa only [map_sub,map_one,sub_eq_zero] using hz
      have hφc : φ c ≠ 0 := by
        intro hz
        exact hr (hcr.symm.trans hz)
      have hs : A*u+B*v < min (3*A) (min (2*B) (A+B)) := lt_of_not_ge hlarge
      apply quartic_pair_small_field (R := (PairCone 2 A B θ) ⧸ I)
        A B hB θ φ ψ htφ htψ c (A*u+B*v) hc
      · exact hφc
      · exact hψc
      · exact ha
      · exact hs.trans_le (min_le_left _ _)
      · exact hs.trans_le ((min_le_right _ _).trans (min_le_left _ _))
      · exact hs.trans_le ((min_le_right _ _).trans (min_le_right _ _))

open MvPolynomial
open scoped Classical

def pairBoundaryExponent {n : ℕ} (k : ℕ) (i : Fin n)
    (m : (Fin n ⊕ Fin n) →₀ ℕ) : (Fin n → ℤ) × ℕ :=
  (fun j => if j = i then 0 else pairExponent k m j, m (Sum.inr i))

theorem pairBoundaryExponent_injective {n k : ℕ} {i : Fin n}
    {m m' : (Fin n ⊕ Fin n) →₀ ℕ}
    (hm : PairNormal k m) (hm' : PairNormal k m')
    (hmi : m (Sum.inl i) = 0) (hmi' : m' (Sum.inl i) = 0)
    (h : pairBoundaryExponent k i m = pairBoundaryExponent k i m') : m = m' := by
  apply pairExponent_injective_normal hm hm'
  have hb := congrArg Prod.snd h
  have ha := congrArg Prod.fst h
  funext j
  by_cases hj : j = i
  · subst j
    simp_all [pairExponent, pairBoundaryExponent]
  · simpa [pairBoundaryExponent, hj] using congrFun ha j

noncomputable def pairBoundaryMap {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (k : ℕ) (q : Fin n → R) (φ : R →+* S) (i : Fin n) :
    MvPolynomial (Fin n ⊕ Fin n) R →+* AddMonoidAlgebra S ((Fin n → ℤ) × ℕ) :=
  eval₂Hom ((AddMonoidAlgebra.singleZeroRingHom).comp φ)
    (Sum.elim
      (fun j => AddMonoidAlgebra.single ((if j=i then 0 else Pi.single j 1), 0)
        (if j=i then 0 else 1))
      (fun j => AddMonoidAlgebra.single ((if j=i then 0 else Pi.single j (-(k:ℤ))),
        if j=i then 1 else 0) (if j=i then 1 else φ (q j))))

theorem pairBoundaryMap_monomial {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (k : ℕ) (q : Fin n → R) (φ : R →+* S) (i : Fin n)
    (m : (Fin n ⊕ Fin n) →₀ ℕ) (c : R) :
    pairBoundaryMap k q φ i (monomial m c) =
      AddMonoidAlgebra.single (pairBoundaryExponent k i m)
        (φ c * (0:S) ^ m (Sum.inl i) * ∏ j ∈ Finset.univ.erase i, φ (q j)^m (Sum.inr j)) := by
  classical
  have hs (g : Fin n → ℤ) (j : Fin n) :
      (∑ x, if x = i then 0 else if j = x then g x else 0) =
        if j = i then 0 else g j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  rw [pairBoundaryMap, eval₂Hom_monomial, Finsupp.prod_fintype _ _ (by simp)]
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
    AddMonoidAlgebra.single_pow, AddMonoidAlgebra.prod_single,
    AddMonoidAlgebra.single_mul_single]
  change AddMonoidAlgebra.single (0 : (Fin n → ℤ) × ℕ) (φ c) * _ = _
  rw [AddMonoidAlgebra.single_mul_single, zero_add]
  congr 1
  · ext j
    · by_cases hj : j = i
      · subst j
        simp [pairBoundaryExponent, Prod.fst_sum, Finset.sum_apply,
          ite_apply, Pi.single_apply, nsmul_eq_mul, hs]
      · simp [pairBoundaryExponent, pairExponent, Prod.fst_sum, Finset.sum_apply,
          ite_apply, Pi.single_apply, nsmul_eq_mul, mul_comm, sub_eq_add_neg, hj, hs]
    · simp [pairBoundaryExponent, Prod.snd_sum]
  · have ha : (∏ j : Fin n, (if j = i then (0 : S) else 1) ^ m (Sum.inl j)) =
        (0 : S) ^ m (Sum.inl i) := by
      rw [Finset.prod_eq_single i]
      · simp
      · intro j _ hj
        simp [hj]
      · simp
    have hb : (∏ j : Fin n, (if j = i then 1 else φ (q j)) ^ m (Sum.inr j)) =
        ∏ j ∈ Finset.univ.erase i, φ (q j) ^ m (Sum.inr j) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      simp only [ite_true, one_pow, one_mul]
      apply Finset.prod_congr rfl
      intro j hj
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj
      simp [hj]
    rw [ha, hb]
    ring

theorem pairBoundaryMap_relation {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    {k : ℕ} (hk : 0 < k) (q : Fin n → R) (φ : R →+* S) (i : Fin n)
    (hqi : φ (q i) = 0) (j : Fin n) :
    pairBoundaryMap k q φ i (pairRelation k q j) = 0 := by
  classical
  simp only [pairRelation, map_sub, map_mul, map_pow]
  simp only [pairBoundaryMap, eval₂Hom_X', eval₂Hom_C, Sum.elim_inl, Sum.elim_inr,
    RingHom.comp_apply, AddMonoidAlgebra.singleZeroRingHom_apply]
  by_cases hj : j = i
  · subst j
    simp [hqi, Nat.ne_of_gt hk]
  · simp only [hj, ite_false, AddMonoidAlgebra.single_pow,
      AddMonoidAlgebra.single_mul_single, one_pow, one_mul]
    have he : k • (Pi.single j (1 : ℤ), (0 : ℕ)) +
        (Pi.single j (-(k : ℤ)), (0 : ℕ)) = (0 : (Fin n → ℤ) × ℕ) := by
      ext a
      · by_cases ha : a = j <;> simp [ha]
      · simp
    rw [he]
    exact sub_self _

theorem pairBoundaryMap_normal_coeff {n : ℕ} {R S : Type*} [CommRing R]
    [CommRing S] [IsDomain S] (k : ℕ) (q : Fin n → R) (φ : R →+* S) (i : Fin n)
    (hq : ∀ j, j ≠ i → φ (q j) ≠ 0)
    (r : MvPolynomial (Fin n ⊕ Fin n) R)
    (hr : ∀ m ∈ r.support, PairNormal k m) (he : pairBoundaryMap k q φ i r = 0)
    (m : (Fin n ⊕ Fin n) →₀ ℕ) (hmi : m (Sum.inl i) = 0) : φ (r.coeff m) = 0 := by
  classical
  by_cases hm : m ∈ r.support
  · have hc : (pairBoundaryMap k q φ i r).coeff (pairBoundaryExponent k i m) =
        φ (r.coeff m) * ∏ j ∈ Finset.univ.erase i, φ (q j) ^ m (Sum.inr j) := by
      conv_lhs => rw [r.as_sum, map_sum]
      rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
        Finset.sum_eq_single_of_mem m hm]
      · simp [pairBoundaryMap_monomial, hmi, AddMonoidAlgebra.coeff_single]
      · intro m' hm' hne
        by_cases hmi' : m' (Sum.inl i) = 0
        · have hE : pairBoundaryExponent k i m' ≠ pairBoundaryExponent k i m :=
            fun hh => hne (pairBoundaryExponent_injective (hr m' hm') (hr m hm) hmi' hmi hh)
          simp [pairBoundaryMap_monomial, AddMonoidAlgebra.coeff_single, hE]
        · simp [pairBoundaryMap_monomial, hmi']
    rw [he] at hc
    have hp : (∏ j ∈ Finset.univ.erase i, φ (q j) ^ m (Sum.inr j)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun j hj => pow_ne_zero _ (hq j (Finset.mem_erase.mp hj).1))
    exact (mul_eq_zero.mp hc.symm).resolve_right hp
  · simp [notMem_support_iff.mp hm]

theorem pair_boundary_ideal_eq_ker {n : ℕ} {R S : Type*} [CommRing R] [Nontrivial R]
    [CommRing S] [IsDomain S] {k : ℕ} (hk : 0 < k)
    (q : Fin n → R) (φ : R →+* S) (i : Fin n)
    (hker : RingHom.ker φ = Ideal.span {q i})
    (hq : ∀ j, j ≠ i → φ (q j) ≠ 0) :
    Ideal.span (Set.range (pairRelation k q)) ⊔ Ideal.span {X (Sum.inl i)} =
      RingHom.ker (pairBoundaryMap k q φ i) := by
  classical
  let I : Ideal (MvPolynomial (Fin n ⊕ Fin n) R) :=
    Ideal.span (Set.range (pairRelation k q)) ⊔ Ideal.span {X (Sum.inl i)}
  have hqi : φ (q i) = 0 := by
    change q i ∈ RingHom.ker φ
    rw [hker]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hle : I ≤ RingHom.ker (pairBoundaryMap k q φ i) := by
    apply sup_le
    · apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact pairBoundaryMap_relation hk q φ i hqi j
    · apply (Ideal.span_singleton_le_iff_mem _).mpr
      change pairBoundaryMap k q φ i (X (Sum.inl i)) = 0
      simp [pairBoundaryMap]
  have hX : X (Sum.inl i) ∈ I :=
    (show Ideal.span {X (Sum.inl i)} ≤ I from le_sup_right)
      (Ideal.subset_span (Set.mem_singleton _))
  have hC : C (q i) ∈ I := by
    have hp : X (Sum.inl i) ^ k * X (Sum.inr i) ∈ I :=
      I.mul_mem_right _ (I.pow_mem_of_mem hX k hk)
    have hr : pairRelation k q i ∈ I :=
      (show Ideal.span (Set.range (pairRelation k q)) ≤ I from le_sup_left)
        (Ideal.subset_span ⟨i, rfl⟩)
    have hh := I.sub_mem hp hr
    simpa [pairRelation] using hh
  apply le_antisymm hle
  intro p hp
  obtain ⟨g, r, hpr, hr⟩ := pair_normal_form k q p
  have hg : Finsupp.linearCombination _ (pairRelation k q) g ∈ I := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    apply Ideal.sum_mem
    intro j _
    exact I.mul_mem_left _ ((show Ideal.span (Set.range (pairRelation k q)) ≤ I from le_sup_left)
      (Ideal.subset_span ⟨j, rfl⟩))
  have her : pairBoundaryMap k q φ i r = 0 := by
    have he := congrArg (pairBoundaryMap k q φ i) hpr
    rw [map_add, show pairBoundaryMap k q φ i p = 0 from hp,
      show pairBoundaryMap k q φ i (Finsupp.linearCombination _ (pairRelation k q) g) = 0
        from hle hg, zero_add] at he
    exact he.symm
  have hri : r ∈ I := by
    rw [r.as_sum]
    apply Ideal.sum_mem
    intro m _
    by_cases hmi : m (Sum.inl i) = 0
    · have hc := pairBoundaryMap_normal_coeff k q φ i hq r hr her m hmi
      change r.coeff m ∈ RingHom.ker φ at hc
      rw [hker, Ideal.mem_span_singleton] at hc
      obtain ⟨c, hc⟩ := hc
      rw [hc, ← C_mul_monomial]
      exact I.mul_mem_right _ hC
    · exact I.mem_of_dvd (X_dvd_monomial.mpr (Or.inr hmi)) hX
  rw [hpr]
  exact I.add_mem hg hri

theorem pair_boundary_ideal_isPrime {n : ℕ} {R S : Type*} [CommRing R] [Nontrivial R]
    [CommRing S] [IsDomain S] {k : ℕ} (hk : 0 < k)
    (q : Fin n → R) (φ : R →+* S) (i : Fin n)
    (hker : RingHom.ker φ = Ideal.span {q i})
    (hq : ∀ j, j ≠ i → φ (q j) ≠ 0) :
    (Ideal.span (Set.range (pairRelation k q)) ⊔ Ideal.span {X (Sum.inl i)}).IsPrime := by
  rw [pair_boundary_ideal_eq_ker hk q φ i hker hq]
  exact RingHom.ker_isPrime _

end QuarticPowerFree

end OAI

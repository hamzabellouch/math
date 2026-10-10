import OAI.NumberTheory.PowerFree.PairCuts

namespace OAI

namespace QuarticPowerFree

section
open scoped BigOperators

theorem basis_homogeneous_lift {ι K R S : Type*} [Field K] [CommRing R]
    [CommRing S] [Algebra K R] [Algebra K S]
    (L : R →ₐ[K] Polynomial R) (b : Module.Basis ι K R) (w : ι → ℕ)
    (hb : ∀ i, L (b i) = Polynomial.monomial (w i) (b i))
    (t : R) (ht : L t = Polynomial.monomial 1 t)
    (φ : R →ₐ[K] S) (hφ : φ t = 1) (r : R) :
    ∃ D : ℕ, ∃ c : R, L c = Polynomial.monomial D c ∧ φ c = φ r := by
  classical
  let s := (b.repr r).support
  let D := s.sup w
  let c := ∑ i ∈ s, (b.repr r i) • (b i * t^(D-w i))
  have hw : ∀ i ∈ s, w i ≤ D := fun i hi => Finset.le_sup hi
  refine ⟨D,c,?_,?_⟩
  · dsimp only [c]
    simp only [map_sum,map_smul,map_mul,map_pow,hb,ht]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Polynomial.monomial_pow,one_mul,Polynomial.monomial_mul_monomial,
      Nat.add_sub_of_le (hw i hi),Polynomial.smul_monomial]
  · dsimp only [c]
    simp only [map_sum,map_smul,map_mul,map_pow,hφ,one_pow,mul_one]
    simpa only [s,Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul] using congrArg φ (b.linearCombination_repr r)

theorem homogeneous_division {K R : Type*} [Field K] [CommRing R] [IsDomain R]
    [Algebra K R] (L : R →ₐ[K] Polynomial R) {a x : R} {E D : ℕ}
    (ha : a ≠ 0) (hA : L a = Polynomial.monomial E a)
    (hD : L (a*x) = Polynomial.monomial D (a*x)) (hED : E ≤ D) :
    L x = Polynomial.monomial (D-E) x := by
  have he : Polynomial.monomial E a * L x =
      Polynomial.monomial E a * Polynomial.monomial (D-E) x := by
    rw [Polynomial.monomial_mul_monomial,Nat.add_sub_of_le hED,← hD,map_mul,hA]
  exact mul_left_cancel₀ (by simpa using ha) he

end

section

theorem minimal_homogeneous_lift {ι K R S : Type*} [Field K] [CommRing R]
    [IsDomain R] [CommRing S] [Algebra K R] [Algebra K S]
    (L : R →ₐ[K] Polynomial R) (b : Module.Basis ι K R) (w : ι → ℕ)
    (hb : ∀ i, L (b i) = Polynomial.monomial (w i) (b i))
    (t : R) (ht0 : t ≠ 0) (ht : L t = Polynomial.monomial 1 t)
    (φ : R →ₐ[K] S) (hφ : φ t = 1) (r : R) (hr : φ r ≠ 0) :
    ∃ D : ℕ, ∃ c : R, L c = Polynomial.monomial D c ∧
      φ c = φ r ∧ c ≠ 0 ∧ ¬ t ∣ c := by
  classical
  have hex := basis_homogeneous_lift L b w hb t ht φ hφ r
  let D := Nat.find hex
  obtain ⟨c,hc,hcr⟩ := Nat.find_spec hex
  have hc0 : c ≠ 0 := by
    intro h
    apply hr
    rw [← hcr,h,map_zero]
  refine ⟨D,c,hc,hcr,hc0,?_⟩
  rintro ⟨x,hx⟩
  have hDpos : 0 < D := by
    by_contra h
    have hD : D = 0 := by omega
    have he := congrArg (fun p : Polynomial R => p.coeff 0) hc
    change (L c).coeff 0 = (Polynomial.monomial D c).coeff 0 at he
    have hzero : (L c).coeff 0 = 0 := by
      rw [hx,map_mul,ht]
      simp [Polynomial.mul_coeff_zero]
    have he' : (0 : R) = c := by simpa only [hD,hzero,Polynomial.coeff_monomial_same] using he
    exact hc0 he'.symm
  have hdegree : L x = Polynomial.monomial (D-1) x :=
    homogeneous_division L ht0 ht (hx ▸ hc) hDpos
  have hxr : φ x = φ r := by
    rw [hx,map_mul,hφ,one_mul] at hcr
    exact hcr
  have hh : D ≤ D-1 := Nat.find_min' hex ⟨x,hdegree,hxr⟩
  omega

open scoped BigOperators

theorem pairCone_t_dvd_basis {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K) (i : PairBasisIndex n k)
    (hi : 0 < i.1 2) :
    pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2) ∣
      pairConeBasis k A B hB θ i := by
  have hd : (MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) K) ∣
      MvPolynomial.monomial i.1 1 := MvPolynomial.X_dvd_monomial.mpr (Or.inr (Nat.ne_of_gt hi))
  obtain ⟨v,hv⟩ := hd
  refine ⟨Ideal.Quotient.mk _ (MvPolynomial.monomial i.2.val v), ?_⟩
  simp only [pairConeBasis, Module.Basis.smulTower_apply, pairNormalBasis_smul]
  change Ideal.Quotient.mk _ (MvPolynomial.monomial i.2.val (MvPolynomial.monomial i.1 (1 : K))) = _
  rw [hv]
  change _ = Ideal.Quotient.mk _ (MvPolynomial.C (MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) K)) * _
  rw [← map_mul,MvPolynomial.C_mul_monomial]

theorem pairCone_homogeneous_degree {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K)
    (c : PairCone k A B θ) (D : ℕ)
    (hC : pairConeScale k A B θ c = Polynomial.monomial D c)
    (hinfty : ¬ pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2) ∣ c) :
    ∃ u v : ℕ, D = A*u+B*v := by
  classical
  let b := pairConeBasis k A B hB θ
  let t := pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)
  have hi : ∃ i, b.repr c i ≠ 0 ∧ ¬ t ∣ b i := by
    by_contra! hh
    apply hinfty
    rw [← b.linearCombination_repr c,Finsupp.linearCombination_apply,Finsupp.sum]
    apply Finset.dvd_sum
    intro i hi
    obtain ⟨v,hv⟩ := hh i (Finsupp.mem_support_iff.mp hi)
    refine ⟨(b.repr c) i • v, ?_⟩
    rw [hv,mul_smul_comm]
  obtain ⟨i,hi,hnd⟩ := hi
  have ht0 : i.1 2 = 0 := by
    by_contra hh
    exact hnd (pairCone_t_dvd_basis k A B hB θ i (Nat.pos_of_ne_zero hh))
  have hw : pairBasisWeight A B i = D := by
    have hc := homogeneous_coord (pairConeScale k A B θ) b (pairBasisWeight A B)
      (pairConeBasis_homogeneous k A B hB θ) c D i
    rw [hC,Polynomial.coeff_monomial_same] at hc
    by_contra hh
    simp only [hh,ite_false] at hc
    exact hi hc
  refine ⟨∑ j, (pairIndexToTuple i j).1, ∑ j, (pairIndexToTuple i j).2, ?_⟩
  rw [← hw,pairBasisWeight_eq,ht0,zero_add,Finset.sum_add_distrib,
    ← Finset.mul_sum,← Finset.mul_sum]

theorem pairCone_minimal_lift {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K)
    (r : PairCone k A B θ)
    (hr : Ideal.Quotient.mk
      (Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1}) r ≠ 0) :
    ∃ u v : ℕ, ∃ c : PairCone k A B θ,
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
  obtain ⟨D,c,hc,hcr,hc0,hct⟩ := minimal_homogeneous_lift (K := K)
    (R := PairCone k A B θ) (S := (PairCone k A B θ) ⧸ I)
    (pairConeScale k A B θ) (pairConeBasis k A B hB θ) (pairBasisWeight A B)
    (pairConeBasis_homogeneous k A B hB θ) t (pairCone_t_prime k A B hB θ).ne_zero
    (pairCone_t_homogeneous k A B θ) φ ht r (show φ r ≠ 0 from hr)
  obtain ⟨u,v,hD⟩ := pairCone_homogeneous_degree k A B hB θ c D hc hct
  exact ⟨u,v,c,hD ▸ hc,hcr,hc0,hct⟩

end

theorem span_sup_eq_of_quotient_eq {R : Type*} [CommRing R] (I : Ideal R)
    (a b : R) (h : Ideal.Quotient.mk I a = Ideal.Quotient.mk I b) :
    Ideal.span {a} ⊔ I = Ideal.span {b} ⊔ I := by
  have hle (a b : R) (h : Ideal.Quotient.mk I a = Ideal.Quotient.mk I b) :
      Ideal.span {a} ⊔ I ≤ Ideal.span {b} ⊔ I := by
    apply sup_le _ le_sup_right
    apply Ideal.span_le.mpr
    intro r hr
    have hr' : r = a := Set.mem_singleton_iff.mp hr
    subst r
    have hab : a-b ∈ Ideal.span {b} ⊔ I := (show I ≤ Ideal.span {b} ⊔ I from le_sup_right) (Ideal.Quotient.eq.mp h)
    have hb : b ∈ Ideal.span {b} ⊔ I := (show Ideal.span {b} ≤ Ideal.span {b} ⊔ I from le_sup_left) (Ideal.subset_span (Set.mem_singleton _))
    change a ∈ (Ideal.span {b} ⊔ I : Ideal R)
    have hsum := (Ideal.span {b} ⊔ I).add_mem hab hb
    rw [sub_add_cancel] at hsum
    exact hsum
  exact le_antisymm (hle a b h) (hle b a h.symm)

theorem pairAffine_any_cut_hilbert {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hA : 0 < A) (hB : 0 < B) (θ : Fin n → K)
    (r : PairCone k A B θ)
    (hr : Ideal.Quotient.mk
      (Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1}) r ≠ 0) :
    ∃ u v : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, A*u+B*v ≤ T →
      |(Module.finrank K ((homogeneousSpace (pairConeScale k A B θ) T).map
        (Ideal.Quotient.mkₐ K (Ideal.span {r} ⊔
         Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1})).toLinearMap) : ℝ) -
        ((A*u+B*v : ℕ):ℝ)*((k*A+B : ℕ):ℝ)^n /
          (((n+1).factorial:ℝ)*(A:ℝ)^(n+1)*(B:ℝ)^(n+1))*(T:ℝ)^(n+1)| ≤
        C*((T:ℝ)+1)^n := by
  obtain ⟨u,v,c,hc,hcr,hc0,hct⟩ := pairCone_minimal_lift k A B hB θ r hr
  have he : (Ideal.span {c} ⊔
      Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1} : Ideal (PairCone k A B θ)) =
      Ideal.span {r} ⊔
      Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1} :=
    span_sup_eq_of_quotient_eq _ c r hcr
  obtain ⟨C,hC,hbound⟩ := pairAffine_cut_hilbert k A B hA hB θ u v c hc0 hc hct
  refine ⟨u,v,C,hC,?_⟩
  rw [he] at hbound
  exact hbound

theorem connected_homogeneous_isUnit {ι K R : Type*} [Field K] [CommRing R]
    [Algebra K R] (L : R →ₐ[K] Polynomial R)
    (b : Module.Basis ι K R) (w : ι → ℕ) (i0 : ι)
    (hb : ∀ i, L (b i) = Polynomial.monomial (w i) (b i))
    (hw : ∀ i, w i = 0 → i = i0) (hb0 : b i0 = 1)
    (c : R) (hc : L c = Polynomial.monomial 0 c) (hc0 : c ≠ 0) : IsUnit c := by
  classical
  have hs : b.repr c = Finsupp.single i0 (b.repr c i0) := by
    ext i
    by_cases hi : i = i0
    · subst i
      simp
    · have hw0 : w i ≠ 0 := fun h => hi (hw i h)
      have hh := homogeneous_coord L b w hb c 0 i
      rw [hc,Polynomial.coeff_monomial_same,ite_eq_right hw0] at hh
      simp [hi,hh]
  have he : c = algebraMap K R (b.repr c i0) := by
    calc
      c = Finsupp.linearCombination K b (b.repr c) := (b.linearCombination_repr c).symm
      _ = algebraMap K R (b.repr c i0) := by
        rw [hs,Finsupp.linearCombination_single,hb0,← Algebra.algebraMap_eq_smul_one]
        simp
  have ha : b.repr c i0 ≠ 0 := by
    intro h
    exact hc0 (by simpa only [h,map_zero] using he)
  rw [he]
  exact (isUnit_iff_ne_zero.mpr ha).map (algebraMap K R)

open scoped BigOperators

theorem pairBasisWeight_zero {n k A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (i : PairBasisIndex n k) (hi : pairBasisWeight A B i = 0) :
    i = (0,⟨0,by simp [PairNormal]⟩) := by
  rw [pairBasisWeight_eq] at hi
  have ht : i.1 2 = 0 := by omega
  have hs : ∑ j, (A*(pairIndexToTuple i j).1+B*(pairIndexToTuple i j).2) = 0 := by omega
  have hj (j : Fin (n+1)) :
      (pairIndexToTuple i j).1 = 0 ∧ (pairIndexToTuple i j).2 = 0 := by
    have he : A*(pairIndexToTuple i j).1+B*(pairIndexToTuple i j).2 ≤ 0 := by
      calc
        _ ≤ ∑ j, (A*(pairIndexToTuple i j).1+B*(pairIndexToTuple i j).2) :=
          Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ j)
        _ = 0 := hs
    have ha : A*(pairIndexToTuple i j).1 = 0 := by omega
    have hb : B*(pairIndexToTuple i j).2 = 0 := by omega
    exact ⟨(Nat.mul_eq_zero.mp ha).resolve_left (Nat.ne_of_gt hA),
      (Nat.mul_eq_zero.mp hb).resolve_left (Nat.ne_of_gt hB)⟩
  apply Prod.ext
  · ext j
    fin_cases j
    · exact (hj 0).1
    · exact (hj 0).2
    · exact ht
  · apply Subtype.ext
    ext j
    cases j with
    | inl j => exact (hj j.succ).1
    | inr j => exact (hj j.succ).2

theorem pairCone_degree_zero_isUnit {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hA : 0 < A) (hB : 0 < B) (θ : Fin n → K)
    (c : PairCone k A B θ) (hc0 : c ≠ 0)
    (hc : pairConeScale k A B θ c = Polynomial.monomial 0 c) : IsUnit c := by
  let i0 : PairBasisIndex n k := (0,⟨0,by simp [PairNormal]⟩)
  have hb0 : pairConeBasis k A B hB θ i0 = 1 := by
    simp only [pairConeBasis, Module.Basis.smulTower_apply,pairNormalBasis_smul]
    change Ideal.Quotient.mk _ (MvPolynomial.monomial 0
      (MvPolynomial.monomial 0 (1 : K))) = (1 : PairCone k A B θ)
    simp
  exact connected_homogeneous_isUnit (pairConeScale k A B θ)
    (pairConeBasis k A B hB θ) (pairBasisWeight A B) i0
    (pairConeBasis_homogeneous k A B hB θ) (fun i hi => pairBasisWeight_zero hA hB i hi)
    hb0 c hc hc0

theorem pairCone_positive_lift {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hA : 0 < A) (hB : 0 < B) (θ : Fin n → K)
    (r : PairCone k A B θ)
    (hr : Ideal.Quotient.mk
      (Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1}) r ≠ 0)
    (hru : ¬ IsUnit (Ideal.Quotient.mk
      (Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1}) r)) :
    ∃ u v : ℕ, ∃ c : PairCone k A B θ,
      min A B ≤ A*u+B*v ∧
      pairConeScale k A B θ c = Polynomial.monomial (A*u+B*v) c ∧
      Ideal.Quotient.mk
        (Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1}) c =
      Ideal.Quotient.mk
        (Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1}) r ∧
      c ≠ 0 ∧ ¬ pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2) ∣ c := by
  obtain ⟨u,v,c,hc,hcr,hc0,hct⟩ := pairCone_minimal_lift k A B hB θ r hr
  have hD : A*u+B*v ≠ 0 := by
    intro h
    apply hru
    rw [← hcr]
    exact (pairCone_degree_zero_isUnit k A B hA hB θ c hc0 (h ▸ hc)).map _
  have hl : min A B ≤ A*u+B*v := by
    by_cases hu : u = 0
    · have hv : 1 ≤ v := by
        by_contra hh
        have hv0 : v = 0 := by omega
        exact hD (by simp [hu,hv0])
      have hbv : B ≤ B*v := by simpa using Nat.mul_le_mul_left B hv
      exact (min_le_right A B).trans (hbv.trans (Nat.le_add_left _ _))
    · have hua : A ≤ A*u := by simpa using Nat.mul_le_mul_left A (Nat.one_le_iff_ne_zero.mpr hu)
      exact (min_le_left A B).trans (hua.trans (Nat.le_add_right _ _))
  exact ⟨u,v,c,hl,hc,hcr,hc0,hct⟩

end QuarticPowerFree

end OAI

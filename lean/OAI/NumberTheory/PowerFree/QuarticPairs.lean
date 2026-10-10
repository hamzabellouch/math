import OAI.NumberTheory.PowerFree.BoundedLifts

namespace OAI

namespace QuarticPowerFree

section
open scoped BigOperators

noncomputable def pairConeB {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin n → K) : Fin (n+1) → PairCone k A B θ :=
  Fin.cons (pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 1))
    (fun j => Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inr j)))

noncomputable def pairABExponent {n k : ℕ} (i : PairBasisIndex n k) :
    (Fin (n+1) ⊕ Fin (n+1)) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Sum.elim
    (fun j => (pairIndexToTuple i j).1) (fun j => (pairIndexToTuple i j).2))

lemma pairConeBasis_map {n : ℕ} {K S : Type*} [Field K] [CommRing S] [Algebra K S]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K)
    (φ : PairCone k A B θ →ₐ[K] S)
    (ht : φ (pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)) = 1)
    (i : PairBasisIndex n k) :
    φ (pairConeBasis k A B hB θ i) =
      MvPolynomial.aeval (Sum.elim (φ ∘ pairConeA k A B θ) (φ ∘ pairConeB k A B θ))
        (MvPolynomial.monomial (pairABExponent i) (1 : K)) := by
  classical
  simp only [pairConeBasis,Module.Basis.smulTower_apply,pairNormalBasis_smul]
  change φ (Ideal.Quotient.mk _ (MvPolynomial.monomial i.2.val (MvPolynomial.monomial i.1 (1 : K)))) = _
  simp only [monomial_eq_univ_prod,map_mul,map_prod,map_pow,map_one,one_mul,
    MvPolynomial.aeval_X]
  have ht' : φ (Ideal.Quotient.mk _ (MvPolynomial.C (MvPolynomial.X 2))) = 1 := ht
  simp only [Fintype.prod_sum_type]
  simp [Fin.prod_univ_succ,ht',pairABExponent,pairConeA,pairConeB,pairIndexToTuple,pairCoeffMap]
  ring

noncomputable def pairConePolynomial {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K) (c : PairCone k A B θ) :
    MvPolynomial (Fin (n+1) ⊕ Fin (n+1)) K :=
  ((pairConeBasis k A B hB θ).repr c).sum fun i r =>
    MvPolynomial.monomial (pairABExponent i) r

lemma pairConePolynomial_eval {n : ℕ} {K S : Type*} [Field K] [CommRing S] [Algebra K S]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K)
    (φ : PairCone k A B θ →ₐ[K] S)
    (ht : φ (pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)) = 1)
    (c : PairCone k A B θ) :
    MvPolynomial.aeval (Sum.elim (φ ∘ pairConeA k A B θ) (φ ∘ pairConeB k A B θ))
      (pairConePolynomial k A B hB θ c) = φ c := by
  classical
  let b := pairConeBasis k A B hB θ
  have he (i : PairBasisIndex n k) (r : K) :
      MvPolynomial.monomial (pairABExponent i) r =
        r • MvPolynomial.monomial (pairABExponent i) (1 : K) := by
    simp [MvPolynomial.smul_monomial]
  have heval (i : PairBasisIndex n k) (r : K) :
      MvPolynomial.aeval (Sum.elim (φ ∘ pairConeA k A B θ) (φ ∘ pairConeB k A B θ))
        (MvPolynomial.monomial (pairABExponent i) r) = r • φ (b i) := by
    rw [he,map_smul,← pairConeBasis_map k A B hB θ φ ht]
  simp only [pairConePolynomial,Finsupp.sum,map_sum,heval]
  simpa only [b,Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul] using
    congrArg φ (b.linearCombination_repr c)

lemma pairConePolynomial_weight {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K) (c : PairCone k A B θ) (D : ℕ)
    (hc : pairConeScale k A B θ c = Polynomial.monomial D c) :
    ∀ m ∈ (pairConePolynomial k A B hB θ c).support,
      A * (∑ i, m (Sum.inl i)) + B * (∑ j, m (Sum.inr j)) ≤ D := by
  classical
  let b := pairConeBasis k A B hB θ
  have hcoord (i : PairBasisIndex n k) (hi : i ∈ (b.repr c).support) :
      pairBasisWeight A B i = D := by
    have h := homogeneous_coord (pairConeScale k A B θ) b (pairBasisWeight A B)
      (pairConeBasis_homogeneous k A B hB θ) c D i
    simp only [hc,Polynomial.coeff_monomial,ite_true] at h
    by_contra hn
    rw [ite_eq_right hn] at h
    exact (Finsupp.mem_support_iff.mp hi) h
  intro m hm
  have hmem := MvPolynomial.support_sum hm
  obtain ⟨i,hi,hm'⟩ := Finset.mem_biUnion.mp hmem
  have hmi : m = pairABExponent i := by
    exact Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm')
  rw [hmi]
  have he := hcoord i hi
  rw [pairBasisWeight_eq] at he
  change A * (∑ j, (pairIndexToTuple i j).1) + B * (∑ j, (pairIndexToTuple i j).2) ≤ D
  have hsum : (∑ j, (A*(pairIndexToTuple i j).1+B*(pairIndexToTuple i j).2)) =
      A * (∑ j, (pairIndexToTuple i j).1) + B * (∑ j, (pairIndexToTuple i j).2) := by
    simp only [Finset.sum_add_distrib,Finset.mul_sum]
  rw [hsum] at he
  omega

open scoped BigOperators
open MvPolynomial

noncomputable def leftExponent {ι κ : Type*} [Fintype ι]
    (m : (ι ⊕ κ) →₀ ℕ) : ι →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => m (Sum.inl i))

theorem quartic_exponent_classification {ι κ : Type*} [Fintype ι] [Fintype κ]
    (m : (ι ⊕ κ) →₀ ℕ) (A B D : ℕ)
    (hweight : A * (∑ i, m (Sum.inl i)) + B * (∑ j, m (Sum.inr j)) ≤ D)
    (h3 : D < 3*A) (h2 : D < 2*B) (hmix : D < A+B) :
    ((∀ j, m (Sum.inr j) = 0) ∧ (∑ i, m (Sum.inl i)) ≤ 2) ∨
      ∃ j, m = Finsupp.single (Sum.inr j) 1 := by
  classical
  let a := ∑ i, m (Sum.inl i)
  let b := ∑ j, m (Sum.inr j)
  have hb : b ≤ 1 := by
    by_contra hn
    have h := Nat.mul_le_mul_left B (show 2 ≤ b by omega)
    dsimp [a,b] at h
    omega
  by_cases hb0 : b = 0
  · left
    constructor
    · intro j
      have h := Finset.single_le_sum (f := fun j : κ => m (Sum.inr j))
        (fun j _ => Nat.zero_le _) (Finset.mem_univ j)
      change m (Sum.inr j) ≤ b at h
      omega
    · by_contra hn
      have h := Nat.mul_le_mul_left A (show 3 ≤ a by omega)
      dsimp [a] at h
      omega
  · right
    have hb1 : b = 1 := by omega
    have ha0 : a = 0 := by
      by_contra hn
      have h := Nat.mul_le_mul_left A (show 1 ≤ a by omega)
      have hb' : ∑ j, m (Sum.inr j) = 1 := hb1
      rw [hb'] at hweight
      dsimp [a] at h
      omega
    have ha (i : ι) : m (Sum.inl i) = 0 := by
      have h := Finset.single_le_sum (f := fun i : ι => m (Sum.inl i))
        (fun i _ => Nat.zero_le _) (Finset.mem_univ i)
      change m (Sum.inl i) ≤ a at h
      omega
    have hsum : m.sum (fun _ e => e) = 1 := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl),Fintype.sum_sum_type]
      change a+b = 1
      omega
    obtain ⟨j,hj⟩ := (Finsupp.sum_eq_one_iff m).mp hsum
    cases j with
    | inl i =>
        have he := ha i
        simp [hj] at he
    | inr j => exact ⟨j,hj⟩

lemma monomial_left_only {ι κ K : Type*} [Fintype ι] [CommSemiring K]
    (m : (ι ⊕ κ) →₀ ℕ) (c : K) (hm : ∀ j, m (Sum.inr j) = 0) :
    (MvPolynomial.monomial m c : MvPolynomial (ι ⊕ κ) K) =
      rename Sum.inl (MvPolynomial.monomial (leftExponent m) c) := by
  rw [rename_monomial]
  have he : m = Finsupp.mapDomain Sum.inl (leftExponent m) := by
    ext j
    cases j with
    | inl i => simp [leftExponent,Finsupp.mapDomain_apply_of_injective Sum.inl_injective]
    | inr j => simp [Finsupp.mapDomain_of_notMem_range,hm]
  exact congrArg (fun m' => MvPolynomial.monomial m' c) he

theorem quartic_low_polynomial {ι κ K : Type*} [Fintype ι] [Fintype κ] [Field K]
    (p : MvPolynomial (ι ⊕ κ) K) (A B D : ℕ)
    (hweight : ∀ m ∈ p.support,
      A * (∑ i, m (Sum.inl i)) + B * (∑ j, m (Sum.inr j)) ≤ D)
    (h3 : D < 3*A) (h2 : D < 2*B) (hmix : D < A+B) :
    ∃ q : MvPolynomial ι K, q.totalDegree ≤ 2 ∧ ∃ c : κ → K,
      p = rename Sum.inl q + ∑ j, C (c j) * X (Sum.inr j) := by
  classical
  have hterm (m : (ι ⊕ κ) →₀ ℕ) (hm : m ∈ p.support) :
      ∃ q : MvPolynomial ι K, q.totalDegree ≤ 2 ∧ ∃ c : κ → K,
        MvPolynomial.monomial m (p.coeff m) =
          rename Sum.inl q + ∑ j, C (c j) * X (Sum.inr j) := by
    rcases quartic_exponent_classification m A B D (hweight m hm) h3 h2 hmix with h|⟨j,hj⟩
    · refine ⟨MvPolynomial.monomial (leftExponent m) (p.coeff m),?_,fun _ => 0,?_⟩
      · apply (totalDegree_monomial_le _ _).trans
        simpa [Finsupp.sum_fintype,leftExponent] using h.2
      · simpa using monomial_left_only m (p.coeff m) h.1
    · refine ⟨0,by simp,Pi.single j (p.coeff m),?_⟩
      simp only [map_zero,zero_add]
      rw [Finset.sum_eq_single j]
      · simp [hj,MvPolynomial.C_mul_X_eq_monomial]
      · intro l _ hlj
        simp [hlj]
      · simp
  have hsum (s : Finset ((ι ⊕ κ) →₀ ℕ)) (hs : s ⊆ p.support) :
      ∃ q : MvPolynomial ι K, q.totalDegree ≤ 2 ∧ ∃ c : κ → K,
        (∑ m ∈ s, MvPolynomial.monomial m (p.coeff m)) =
          rename Sum.inl q + ∑ j, C (c j) * X (Sum.inr j) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨0,by simp,fun _ => 0,by simp⟩
    | @insert m s hm ih =>
      obtain ⟨q,hq,c,hc⟩ := hterm m (hs (Finset.mem_insert_self _ _))
      obtain ⟨q',hq',c',hc'⟩ := ih (fun i hi => hs (Finset.mem_insert_of_mem hi))
      refine ⟨q+q',(totalDegree_add q q').trans (max_le hq hq'),fun j => c j+c' j,?_⟩
      rw [Finset.sum_insert hm,hc,hc',map_add]
      simp only [map_add,add_mul,Finset.sum_add_distrib]
      abel
  obtain ⟨q,hq,c,hc⟩ := hsum p.support (fun _ h => h)
  refine ⟨q,hq,c,?_⟩
  rw [← hc]
  exact MvPolynomial.as_sum p

end

section
open scoped BigOperators

theorem pairCone_small_relation {n : ℕ} {K R S : Type*} [Field K]
    [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K)
    (φ : PairCone k A B θ →ₐ[K] R) (ψ : PairCone k A B θ →ₐ[K] S)
    (htφ : φ (pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)) = 1)
    (htψ : ψ (pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)) = 1)
    (c : PairCone k A B θ) (D : ℕ)
    (hc : pairConeScale k A B θ c = Polynomial.monomial D c)
    (hφ : φ c ≠ 0) (hψ : ψ c = 0)
    (ha : AlgebraicIndependent K (ψ ∘ pairConeA k A B θ))
    (h3 : D < 3*A) (h2 : D < 2*B) (hmix : D < A+B) :
    ∃ q : MvPolynomial (Fin (n+1)) K, q.totalDegree ≤ 2 ∧
      ∃ b : Fin (n+1) → K, b ≠ 0 ∧
        (∑ j, algebraMap K S (b j) * ψ (pairConeB k A B θ j)) =
          MvPolynomial.aeval (ψ ∘ pairConeA k A B θ) q := by
  classical
  let p := pairConePolynomial k A B hB θ c
  obtain ⟨q,hq,b,hp⟩ := quartic_low_polynomial p A B D
    (pairConePolynomial_weight k A B hB θ c D hc) h3 h2 hmix
  have hψp : MvPolynomial.aeval
      (Sum.elim (ψ ∘ pairConeA k A B θ) (ψ ∘ pairConeB k A B θ)) p = 0 :=
    (pairConePolynomial_eval k A B hB θ ψ htψ c).trans hψ
  have hre : MvPolynomial.aeval (ψ ∘ pairConeA k A B θ) q +
      ∑ j, algebraMap K S (b j) * ψ (pairConeB k A B θ j) = 0 := by
    rw [hp] at hψp
    simpa only [map_add,MvPolynomial.aeval_rename,map_sum,map_mul,
      MvPolynomial.aeval_C,MvPolynomial.aeval_X,Function.comp_def,
      Sum.elim_inl,Sum.elim_inr] using hψp
  have hb : b ≠ 0 := by
    intro hb
    have hq0 : q = 0 := by
      apply algebraicIndependent_iff_injective_aeval.mp ha
      simpa only [hb,Pi.zero_apply,map_zero,zero_mul,Finset.sum_const_zero,add_zero] using hre
    have hp0 : p = 0 := by simp [hp,hq0,hb]
    apply hφ
    rw [← pairConePolynomial_eval k A B hB θ φ htφ c]
    change MvPolynomial.aeval _ p = 0
    rw [hp0,map_zero]
  refine ⟨-q,by simpa only [MvPolynomial.totalDegree_neg] using hq,b,hb,?_⟩
  rw [map_neg]
  exact eq_neg_of_add_eq_zero_right hre

end

open MvPolynomial

theorem paired_denominator_ne_zero {K L : Type*} [Field K] [Field L] [Algebra K L]
    (a : Fin 2 → L) (ha : AlgebraicIndependent K a) (c d : K) (hc : c ≠ 0 ∨ d ≠ 0) :
    algebraMap K L c * a 1 ^ 2 + algebraMap K L d * a 0 ^ 2 ≠ 0 := by
  let p : MvPolynomial (Fin 2) K := C c * X 1^2 + C d * X 0^2
  intro h
  have hp : p = 0 := (algebraicIndependent_iff_injective_aeval.mp ha) (by simpa [p] using h)
  have h1 := congrArg (fun polynomial => polynomial.coeff (Finsupp.single (1 : Fin 2) 2)) hp
  have h0 := congrArg (fun polynomial => polynomial.coeff (Finsupp.single (0 : Fin 2) 2)) hp
  have h01 : (Finsupp.single (0 : Fin 2) 2 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 2 := by
    intro h
    have hh := congrArg (fun m : Fin 2 →₀ ℕ => m 0) h
    simp at hh
  simp [p,X_pow_eq_monomial,h01,Ne.symm h01] at h1 h0
  exact hc.elim (fun h => h h1) (fun h => h h0)

theorem quartic_paired_rational_identity {K L : Type*} [Field K] [Field L] [Algebra K L]
    (a b : Fin 2 → L) (N : L) (θ c : Fin 2 → K) (q : MvPolynomial (Fin 2) K)
    (heq : ∀ i, a i ^ 2 * b i = N-algebraMap K L (θ i))
    (hrel : algebraMap K L (c 0)*b 0 + algebraMap K L (c 1)*b 1 = aeval a q) :
    (algebraMap K L (c 0) * a 1 ^ 2 + algebraMap K L (c 1) * a 0 ^ 2) * N =
      algebraMap K L (c 0*θ 0)*a 1^2 + algebraMap K L (c 1*θ 1)*a 0^2 +
        a 0^2*a 1^2*aeval a q := by
  simp only [map_mul]
  linear_combination -(algebraMap K L (c 0)*a 1^2) * heq 0 -
    (algebraMap K L (c 1)*a 0^2) * heq 1 + a 0^2*a 1^2*hrel

theorem quartic_paired_field {K L : Type*} [Field K] [Field L] [Algebra K L]
    (a b : Fin 2 → L) (ha : AlgebraicIndependent K a) (N : L)
    (θ c : Fin 2 → K) (hc : c 0 ≠ 0 ∨ c 1 ≠ 0) (q : MvPolynomial (Fin 2) K)
    (heq : ∀ i, a i ^ 2 * b i = N-algebraMap K L (θ i))
    (hrel : algebraMap K L (c 0)*b 0 + algebraMap K L (c 1)*b 1 = aeval a q) :
    N ∈ IntermediateField.adjoin K (Set.range a) ∧
      ∀ i, b i ∈ IntermediateField.adjoin K (Set.range a) := by
  let F := IntermediateField.adjoin K (Set.range a)
  let r : MvPolynomial (Fin 2) K :=
    C (c 0*θ 0)*X 1^2 + C (c 1*θ 1)*X 0^2 + X 0^2*X 1^2*q
  let s : MvPolynomial (Fin 2) K := C (c 0)*X 1^2 + C (c 1)*X 0^2
  have hs : aeval a s ≠ 0 := by
    simpa only [s,map_add,map_mul,map_pow,aeval_C,aeval_X] using
      paired_denominator_ne_zero a ha (c 0) (c 1) hc
  have hN : N = aeval a r / aeval a s := by
    apply (eq_div_iff hs).mpr
    simp only [r,s,map_add,map_mul,map_pow,aeval_C,aeval_X]
    rw [mul_comm N]
    simpa only [map_mul] using quartic_paired_rational_identity a b N θ c q heq hrel
  have hNF : N ∈ F := (IntermediateField.mem_adjoin_range_iff K a N).mpr ⟨r,s,hN⟩
  refine ⟨hNF,?_⟩
  intro i
  have ha0 : a i ≠ 0 := by
    intro h
    have hh : (X i : MvPolynomial (Fin 2) K) = 0 :=
      (algebraicIndependent_iff_injective_aeval.mp ha) (by simpa using h)
    exact X_ne_zero i hh
  have hb : b i = (N-algebraMap K L (θ i)) / a i^2 := by
    apply (eq_div_iff (pow_ne_zero _ ha0)).mpr
    simpa [mul_comm] using heq i
  rw [hb]
  have hai : a i ∈ F := IntermediateField.subset_adjoin K _ (Set.mem_range_self i)
  exact F.div_mem (F.sub_mem hNF (F.algebraMap_mem (θ i)))
    (by simpa only [pow_two] using F.mul_mem hai hai)

end QuarticPowerFree

end OAI

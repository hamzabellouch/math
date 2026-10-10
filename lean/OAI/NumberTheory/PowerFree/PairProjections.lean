import OAI.NumberTheory.PowerFree.PositiveCoordinates

namespace OAI

namespace QuarticPowerFree

section

section
open MvPolynomial

noncomputable def positiveToPairHom {n : ℕ} {K R : Type*} [Field K] [CommRing R]
    [Algebra K R] (k : ℕ) (q : Fin n → R) : MvPolynomial (Fin n) R →ₐ[K] PairRing k q :=
  MvPolynomial.aevalTower (pairCoeffHom (K := K) k q) (pairCoordinate k q)

theorem positiveToPairHom_apply {n : ℕ} {K R : Type*} [Field K] [CommRing R]
    [Algebra K R] (k : ℕ) (q : Fin n → R) (p : MvPolynomial (Fin n) R) :
    positiveToPairHom (K := K) k q p = positiveToPair k q p := rfl

theorem positiveToPair_option {n : ℕ} {K : Type*} [Field K]
    (k : ℕ) (θ : Fin n → K) (p : MvPolynomial (Option (Fin n)) K) :
    positiveToPair k (rootPairQ θ) (optionEquivRight K (Fin n) p) =
      MvPolynomial.aeval (fun i => i.elim (pairCoeffMap k (rootPairQ θ) Polynomial.X)
        (pairLeft k (rootPairQ θ))) p := by
  have he : (positiveToPairHom (K := K) k (rootPairQ θ)).comp
      (optionEquivRight K (Fin n)).toAlgHom =
      MvPolynomial.aeval (fun i => i.elim (pairCoeffMap k (rootPairQ θ) Polynomial.X)
        (pairLeft k (rootPairQ θ))) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | none => simp [positiveToPairHom_apply]
    | some i => simp [positiveToPairHom_apply,pairLeft,pairCoordinate]
  exact AlgHom.congr_fun he p

theorem pairConeA_homogeneous {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin n → K) (i : Fin (n+1)) :
    pairConeScale k A B θ (pairConeA k A B θ i) =
      Polynomial.monomial A (pairConeA k A B θ i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [pairConeA,pairConeScale,pairScale_coeff,weightedScale_X,triplePairWeights]
  · change pairScalePre k A B (pairConeQ k A B θ) (weightedScale (triplePairWeights A B))
      (X (Sum.inl j)) = _
    simp [pairScalePre,pairConeA]

theorem pairConeB_homogeneous {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin n → K) (i : Fin (n+1)) :
    pairConeScale k A B θ (pairConeB k A B θ i) =
      Polynomial.monomial B (pairConeB k A B θ i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [pairConeB,pairConeScale,pairScale_coeff,weightedScale_X,triplePairWeights]
  · change pairScalePre k A B (pairConeQ k A B θ) (weightedScale (triplePairWeights A B))
      (X (Sum.inr j)) = _
    simp [pairScalePre,pairConeB]

noncomputable def pairConeN {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) : PairCone k A B (coneDifference θ) :=
  pairConeA k A B (coneDifference θ) 0 ^ k * pairConeB k A B (coneDifference θ) 0 +
    algebraMap K _ (θ 0) * (pairCoeffMap k (pairConeQ k A B (coneDifference θ)) (X 2))^(k*A+B)

theorem pairConeN_homogeneous {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) :
    pairConeScale k A B (coneDifference θ) (pairConeN k A B θ) =
      Polynomial.monomial (k*A+B) (pairConeN k A B θ) := by
  simp only [pairConeN,map_add,map_mul,map_pow,pairConeA_homogeneous,pairConeB_homogeneous,
    pairCone_t_homogeneous,Polynomial.monomial_pow,Polynomial.monomial_mul_monomial,one_mul]
  rw [AlgHom.commutes]
  change Polynomial.monomial (A*k+B) _ + Polynomial.C (algebraMap K _ (θ 0)) *
    Polynomial.monomial (k*A+B) _ = _
  rw [Polynomial.C_mul_monomial,mul_comm A k,←map_add]

@[simp] theorem pairConeToRoot_N {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) :
    pairConeToRoot k A B θ (pairConeN k A B θ) = pairCoeffMap k (rootPairQ θ) Polynomial.X := by
  simp only [pairConeN,map_add,map_mul,map_pow,pairConeToRoot_left,pairConeToRoot_right,
    pairConeToRoot_t,one_pow,mul_one,AlgHom.commutes,rootPair_equation,sub_add_cancel]

theorem rootPair_projection_homogeneous_lift {n : ℕ} {K : Type*} [Field K]
    {k : ℕ} (hk : 0 < k) (A B : ℕ) (θ : Fin (n+1) → K)
    (p : MvPolynomial (Option (Fin (n+1))) K) :
    ∃ c : PairCone k A B (coneDifference θ),
      pairConeScale k A B (coneDifference θ) c =
        Polynomial.monomial ((k*A+B)*p.totalDegree) c ∧
      pairConeToRoot k A B θ c = positiveToPair k (rootPairQ θ)
        (optionEquivRight K (Fin (n+1)) p) := by
  let z : Option (Fin (n+1)) → PairCone k A B (coneDifference θ) :=
    fun i => i.elim (pairConeN k A B θ) (pairConeA k A B (coneDifference θ))
  let w : Option (Fin (n+1)) → ℕ := fun i => i.elim (k*A+B) (fun _ => A)
  have hw : ∀ i, w i ≤ k*A+B := by
    rintro (_|i)
    · exact le_rfl
    · exact (show A ≤ k*A by simpa using Nat.mul_le_mul_right A hk).trans (Nat.le_add_right _ _)
  have hz : ∀ i, pairConeScale k A B (coneDifference θ) (z i) = Polynomial.monomial (w i) (z i) := by
    rintro (_|i)
    · exact pairConeN_homogeneous k A B θ
    · exact pairConeA_homogeneous k A B (coneDifference θ) i
  obtain ⟨c,hc,hφc⟩ := polynomial_homogeneous_lift (pairConeScale k A B (coneDifference θ))
    (pairCoeffMap k (pairConeQ k A B (coneDifference θ)) (X 2))
    (pairCone_t_homogeneous k A B (coneDifference θ)) (pairConeToRoot k A B θ)
    (pairConeToRoot_t k A B θ) z w (k*A+B) hw hz p
  refine ⟨c,hc,?_⟩
  rw [hφc,positiveToPair_option]
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  cases i <;> simp [z,Function.comp_def]

theorem pairConeToRoot_surjective {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) : Function.Surjective (pairConeToRoot k A B θ) := by
  intro x
  obtain ⟨p,hp⟩ := Ideal.Quotient.mk_surjective (rootPairAffineEquiv k A B θ x)
  refine ⟨p,?_⟩
  have he : pairAffineMk k A B (coneDifference θ) p = rootPairAffineEquiv k A B θ x := hp
  apply (rootPairAffineEquiv k A B θ).injective
  exact (AlgHom.congr_fun (rootPairToAffine_comp_cone k A B θ) p).trans he

theorem pairConeToRoot_kernel {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) :
    RingHom.ker (pairConeToRoot k A B θ).toRingHom =
      Ideal.span {pairCoeffMap k (pairConeQ k A B (coneDifference θ)) (X 2)-1} := by
  ext x
  change pairConeToRoot k A B θ x = 0 ↔ _
  rw [←Ideal.Quotient.eq_zero_iff_mem]
  change pairConeToRoot k A B θ x = 0 ↔ pairAffineMk k A B (coneDifference θ) x = 0
  have h := AlgHom.congr_fun (rootPairToAffine_comp_cone k A B θ) x
  rw [←h]
  exact ((rootPairAffineEquiv k A B θ).map_eq_zero_iff).symm

theorem rootPair_bounded_cone_kernel {n : ℕ} {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k : ℕ} (hk : 0 < k) (A B : ℕ) (hB : 0 < B)
    (θ : Fin (n+1) → K) (hθ : Function.Injective θ)
    (ψ : RootPair k θ →ₐ[K] L) (ha : ∀ i, ψ (pairLeft k (rootPairQ θ) i) ≠ 0)
    (p : MvPolynomial (Option (Fin (n+1))) K) (hp : p ≠ 0)
    (hker : ∀ q, ψ (positiveToPair k (rootPairQ θ) q) = 0 ↔
      optionEquivRight K (Fin (n+1)) p ∣ q) :
    ∃ u v : ℕ, ∃ c : PairCone k A B (coneDifference θ),
      A*u+B*v ≤ (k*A+B)*p.totalDegree ∧
      pairConeScale k A B (coneDifference θ) c = Polynomial.monomial (A*u+B*v) c ∧
      c ≠ 0 ∧ ¬ pairCoeffMap k (pairConeQ k A B (coneDifference θ)) (X 2) ∣ c ∧
      RingHom.ker (ψ.comp (pairConeToRoot k A B θ)).toRingHom =
        Ideal.span {c} ⊔ Ideal.span {pairCoeffMap k (pairConeQ k A B (coneDifference θ)) (X 2)-1} := by
  obtain ⟨x,hx,hdiv,hcoord,hxker⟩ := rootPair_projection_kernel hk θ hθ ψ.toRingHom ha
    (optionEquivRight K (Fin (n+1)) p) ((optionEquivRight K (Fin (n+1))).map_eq_zero_iff.not.mpr hp) hker
  obtain ⟨r,hr,hre⟩ := rootPair_projection_homogeneous_lift hk A B θ p
  have hM : ∀ i ∈ ((pairConeBasis k A B hB (coneDifference θ)).repr r).support,
      pairBasisWeight A B i ≤ (k*A+B)*p.totalDegree := by
    intro i hi
    have hh := homogeneous_coord (pairConeScale k A B (coneDifference θ))
      (pairConeBasis k A B hB (coneDifference θ)) (pairBasisWeight A B)
      (pairConeBasis_homogeneous k A B hB (coneDifference θ)) r ((k*A+B)*p.totalDegree) i
    simp only [hr,Polynomial.coeff_monomial,ite_true] at hh
    have he : pairBasisWeight A B i = (k*A+B)*p.totalDegree := by
      by_contra hn
      rw [ite_eq_right hn] at hh
      exact (Finsupp.mem_support_iff.mp hi) hh
    exact he.le
  have hpos : positiveToPair k (rootPairQ θ) (optionEquivRight K (Fin (n+1)) p) ≠ 0 := by
    intro hh
    have he := congrArg (pairToLaurent k (rootPairQ θ)) hh
    rw [positiveToPair_toLaurent,map_zero] at he
    exact hp ((optionEquivRight K (Fin (n+1))).injective
      (positiveLaurentMap_injective (he.trans (map_zero positiveLaurentMap).symm)))
  have he (r) : rootPairAffineEquiv k A B θ (pairConeToRoot k A B θ r) =
      pairAffineMk k A B (coneDifference θ) r :=
    AlgHom.congr_fun (rootPairToAffine_comp_cone k A B θ) r
  have hr0 : pairAffineMk k A B (coneDifference θ) r ≠ 0 := by
    rw [←he,hre]
    exact (rootPairAffineEquiv k A B θ).map_eq_zero_iff.not.mpr hpos
  have hd : rootPairAffineEquiv k A B θ x ∣ pairAffineMk k A B (coneDifference θ) r := by
    rw [←he,hre]
    exact map_dvd (rootPairAffineEquiv k A B θ) hdiv
  obtain ⟨u,v,c,hD,hc,hce,hc0,hct⟩ := pairAffine_divisor_bounded_lift k A B hB
    (coneDifference θ) r ((k*A+B)*p.totalDegree) hM hr0 (rootPairAffineEquiv k A B θ x) hd
  have hcx : pairConeToRoot k A B θ c = x := (rootPairAffineEquiv k A B θ).injective
    ((he c).trans hce)
  refine ⟨u,v,c,hD,hc,hc0,hct,?_⟩
  have hspan : Ideal.span {x} = Ideal.map (pairConeToRoot k A B θ).toRingHom
      (Ideal.span {c}) := by
    rw [Ideal.map_span,Set.image_singleton]
    exact congrArg (fun y : RootPair k θ => Ideal.span {y}) hcx.symm
  change (RingHom.ker ψ.toRingHom).comap (pairConeToRoot k A B θ).toRingHom = _
  have hxker' : (RingHom.ker ψ.toRingHom : Ideal (RootPair k θ)) = Ideal.span {x} := hxker
  rw [hxker',hspan,
    Ideal.comap_map_of_surjective (pairConeToRoot k A B θ).toRingHom (pairConeToRoot_surjective k A B θ)]
  congr 1
  exact pairConeToRoot_kernel k A B θ

end
open scoped BigOperators

theorem finrank_map_eq_of_kernel_eq {K R S T : Type*} [Field K]
    [AddCommGroup R] [AddCommGroup S] [AddCommGroup T]
    [Module K R] [Module K S] [Module K T]
    (f : R →ₗ[K] S) (g : R →ₗ[K] T) (hker : LinearMap.ker f = LinearMap.ker g)
    (V : Submodule K R) : Module.finrank K (V.map f) = Module.finrank K (V.map g) := by
  have he : LinearMap.ker (f.domRestrict V) = LinearMap.ker (g.domRestrict V) := by
    ext x
    change x.val ∈ LinearMap.ker f ↔ x.val ∈ LinearMap.ker g
    rw [hker]
  rw [←LinearMap.range_domRestrict,←LinearMap.range_domRestrict,
    ←(f.domRestrict V).quotKerEquivRange.finrank_eq,
    ←(g.domRestrict V).quotKerEquivRange.finrank_eq,he]

theorem finrank_map_quotient_kernel {K R S : Type*} [Field K]
    [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (φ : R →ₐ[K] S) (I : Ideal R) (hker : RingHom.ker φ.toRingHom = I)
    (V : Submodule K R) :
    Module.finrank K (V.map (Ideal.Quotient.mkₐ K I).toLinearMap) =
      Module.finrank K (V.map φ.toLinearMap) := by
  apply finrank_map_eq_of_kernel_eq
  ext x
  change Ideal.Quotient.mk I x = 0 ↔ φ x = 0
  rw [Ideal.Quotient.eq_zero_iff_mem,←hker]
  rfl

theorem rootPair_actual_hilbert_uniform {n : ℕ} {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k : ℕ} (hk : 0 < k) (A B : ℕ) (hA : 0 < A) (hB : 0 < B) (E : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (θ : Fin (n+1) → K), Function.Injective θ →
      ∀ (ψ : RootPair k θ →ₐ[K] L), (∀ i, ψ (pairLeft k (rootPairQ θ) i) ≠ 0) →
      ∀ (p : MvPolynomial (Option (Fin (n+1))) K), p ≠ 0 → p.totalDegree ≤ E →
      (∀ q, ψ (positiveToPair k (rootPairQ θ) q) = 0 ↔
        MvPolynomial.optionEquivRight K (Fin (n+1)) p ∣ q) →
      ∃ u v : ℕ, min A B ≤ A*u+B*v ∧ A*u+B*v ≤ (k*A+B)*E ∧
        ∀ T : ℕ, (k*A+B)*E ≤ T →
        |(Module.finrank K ((homogeneousSpace (pairConeScale k A B (coneDifference θ)) T).map
          (ψ.comp (pairConeToRoot k A B θ)).toLinearMap) : ℝ) -
          ((A*u+B*v : ℕ):ℝ)*((k*A+B : ℕ):ℝ)^n /
            (((n+1).factorial:ℝ)*(A:ℝ)^(n+1)*(B:ℝ)^(n+1))*(T:ℝ)^(n+1)| ≤
          C*((T:ℝ)+1)^n := by
  classical
  let M := (k*A+B)*E
  choose C hC0 hC using fun u v =>
    pairAffine_cut_hilbert_uniform (n := n) (K := K) k A B hA hB u v
  let Ctotal : ℝ := ∑ u ∈ Finset.range (M+1), ∑ v ∈ Finset.range (M+1), C u v
  have htotal : 0 ≤ Ctotal := Finset.sum_nonneg fun u _ =>
    Finset.sum_nonneg fun v _ => hC0 u v
  refine ⟨Ctotal,htotal,fun θ hθ ψ ha p hp hpE hker => ?_⟩
  obtain ⟨u,v,c,hD,hc,hc0,hct,hkerφ⟩ := rootPair_bounded_cone_kernel hk A B hB θ hθ ψ ha p hp hker
  let φ := ψ.comp (pairConeToRoot k A B θ)
  have hφc : φ c = 0 := by
    apply (show c ∈ RingHom.ker φ.toRingHom ↔ φ c = 0 from Iff.rfl).mp
    rw [hkerφ]
    exact (show Ideal.span {c} ≤ _ from le_sup_left) (Ideal.subset_span (Set.mem_singleton _))
  have hDpos : A*u+B*v ≠ 0 := by
    intro hh
    have hu := (pairCone_degree_zero_isUnit k A B hA hB (coneDifference θ) c hc0 (hh ▸ hc)).map φ
    exact hu.ne_zero hφc
  have hDlower : min A B ≤ A*u+B*v := by
    by_cases hu : u = 0
    · have hv : 1 ≤ v := by
        by_contra hh
        have hv0 : v = 0 := by omega
        exact hDpos (by simp [hu,hv0])
      exact (min_le_right A B).trans ((show B ≤ B*v by simpa using Nat.mul_le_mul_left B hv).trans (Nat.le_add_left _ _))
    · exact (min_le_left A B).trans ((show A ≤ A*u by simpa using Nat.mul_le_mul_left A (Nat.one_le_iff_ne_zero.mpr hu)).trans (Nat.le_add_right _ _))
  have hbound : A*u+B*v ≤ M := hD.trans (Nat.mul_le_mul_left _ hpE)
  have hu : u ≤ M := le_trans (le_trans (by simpa using Nat.mul_le_mul_right u hA)
    (Nat.le_add_right (A*u) (B*v))) hbound
  have hv : v ≤ M := le_trans (le_trans (by simpa using Nat.mul_le_mul_right v hB)
    (Nat.le_add_left (B*v) (A*u))) hbound
  have hsum : C u v ≤ Ctotal := by
    calc C u v ≤ ∑ j ∈ Finset.range (M+1), C u j :=
          Finset.single_le_sum (fun j _ => hC0 u j) (Finset.mem_range.mpr (by omega))
      _ ≤ Ctotal := Finset.single_le_sum (fun i _ =>
          Finset.sum_nonneg (fun j _ => hC0 i j)) (Finset.mem_range.mpr (by omega))
  refine ⟨u,v,hDlower,hbound,fun T hT => ?_⟩
  have hh := hC u v (coneDifference θ) c hc0 hc hct T (hbound.trans hT)
  rw [finrank_map_quotient_kernel φ _ hkerφ] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hsum (by positivity))

end

open MvPolynomial
open scoped BigOperators

theorem weightedSpace_mul_mem {σ K : Type*} [Field K]
    (w : σ → ℕ) {p q : MvPolynomial σ K} {A B : ℕ}
    (hp : p ∈ weightedSpace w A) (hq : q ∈ weightedSpace w B) :
    p*q ∈ weightedSpace w (A+B) := by
  rw [mem_weightedSpace] at hp hq ⊢
  by_cases hp0 : p = 0
  · simp [hp0,weightedTotalDegree_zero]
  by_cases hq0 : q = 0
  · simp [hq0,weightedTotalDegree_zero]
  rw [weightedTotalDegree_mul_exact w p q hp0 hq0]
  exact Nat.add_le_add hp hq

theorem weightedSpace_one {σ K : Type*} [Field K] (w : σ → ℕ) :
    (1 : MvPolynomial σ K) ∈ weightedSpace w 0 := by
  intro m hm
  have hm0 : m = 0 := Finset.mem_singleton.mp (support_one.subset hm)
  simp [hm0]

theorem weightedSpace_pow_mem {σ K : Type*} [Field K]
    (w : σ → ℕ) {p : MvPolynomial σ K} {A : ℕ}
    (hp : p ∈ weightedSpace w A) (e : ℕ) : p^e ∈ weightedSpace w (A*e) := by
  induction e with
  | zero => simpa using weightedSpace_one w
  | succ e ih => simpa only [pow_succ,Nat.mul_succ] using weightedSpace_mul_mem w ih hp

theorem weightedSpace_prod_mem {σ ι K : Type*} [Field K]
    (w : σ → ℕ) (s : Finset ι) (p : ι → MvPolynomial σ K) (A : ι → ℕ)
    (hp : ∀ i ∈ s, p i ∈ weightedSpace w (A i)) :
    ∏ i ∈ s, p i ∈ weightedSpace w (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using weightedSpace_one w
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi,Finset.sum_insert hi]
    exact weightedSpace_mul_mem w (hp i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem weightedSpace_mono {σ K : Type*} [CommSemiring K]
    (w : σ → ℕ) {A B : ℕ} (h : A ≤ B) :
    weightedSpace (K := K) w A ≤ weightedSpace w B := by
  intro p hp m hm
  exact (hp hm).trans h

theorem weightedSpace_aeval {σ τ K : Type*} [Fintype σ] [Field K]
    (w : σ → ℕ) (v : τ → ℕ) (z : σ → MvPolynomial τ K)
    (hz : ∀ i, z i ∈ weightedSpace v (w i))
    (p : MvPolynomial σ K) (T : ℕ) (hp : p ∈ weightedSpace w T) :
    MvPolynomial.aeval z p ∈ weightedSpace v T := by
  classical
  rw [p.as_sum,map_sum]
  apply Submodule.sum_mem
  intro m hm
  rw [aeval_monomial,Finsupp.prod_fintype _ _ (by simp)]
  rw [←Algebra.smul_def]
  apply Submodule.smul_mem
  apply weightedSpace_mono v (hp hm)
  have hh := weightedSpace_prod_mem v Finset.univ (fun i => z i ^ m i)
    (fun i => w i * m i) (fun i _ => weightedSpace_pow_mem v (hz i) (m i))
  have he : Finsupp.weight w m = ∑ i, w i * m i := by
    rw [Finsupp.weight_eq_sum]
    simp only [nsmul_eq_mul,Nat.cast_id,mul_comm]
  rwa [he]

theorem totalSpace_aeval {σ τ K : Type*} [Fintype σ] [Field K]
    (z : σ → MvPolynomial τ K) (D : ℕ) (hz : ∀ i, (z i).totalDegree ≤ D)
    (p : MvPolynomial σ K) (T : ℕ) (hp : p ∈ totalSpace T) :
    MvPolynomial.aeval z p ∈ totalSpace (D*T) := by
  have hz' (i) : z i ∈ weightedSpace (fun _ => 1) D := by
    rw [mem_weightedSpace]
    change weightedTotalDegree 1 (z i) ≤ D
    rw [weightedTotalDegree_one]
    exact hz i
  have hp' : p ∈ weightedSpace (fun _ => D) (D*T) := by
    intro m hm
    calc Finsupp.weight (fun _ => D) m = D * m.sum (fun _ e => e) := by
          rw [Finsupp.weight_eq_sum,Finsupp.sum_fintype _ _ (by simp),Finset.mul_sum]
          exact Finset.sum_congr rfl (fun _ _ => by simp [mul_comm])
      _ ≤ D*T := Nat.mul_le_mul_left D ((le_totalDegree hm).trans (mem_totalSpace.mp hp))
  have hh := weightedSpace_aeval (fun _ => D) (fun _ => 1) z hz' p (D*T) hp'
  rw [mem_weightedSpace] at hh
  change weightedTotalDegree 1 (MvPolynomial.aeval z p) ≤ D*T at hh
  rwa [weightedTotalDegree_one,←mem_totalSpace] at hh

end QuarticPowerFree

end OAI

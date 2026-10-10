import OAI.NumberTheory.PowerFree.MediumDegree

namespace OAI

namespace QuarticPowerFree

section

section
open scoped Classical

lemma independent_one_transcendental {K A : Type*} [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] (t : A) (ht : Transcendental K t) : LinearIndependent K ![1,t] := by
  apply (LinearIndependent.pair_iff' (one_ne_zero : (1:A) ≠ 0)).mpr
  intro c hc
  apply ht
  have he : algebraMap K A c = t := by simpa only [Algebra.algebraMap_eq_smul_one] using hc
  rw [←he]
  exact isAlgebraic_algebraMap c

lemma affine_left_dichotomy {d : ℕ} {K A : Type*} [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] (a : Fin d → A) (s : Fin d) (ht : Transcendental K (a s)) :
    (∃ i : Fin d, LinearIndependent K (fun o : Option (Fin 2) => o.elim 1 (fun j => if j=0 then a i else a s))) ∨
    ∃ c b : Fin d → K, ∀ i, a i = algebraMap K A (c i)*a s+algebraMap K A (b i) := by
  classical
  by_cases hh : ∃ i, a i ∉ Submodule.span K ({1,a s}:Set A)
  · obtain ⟨i,hi⟩ := hh
    left
    refine ⟨i,?_⟩
    have hr : Set.range (![1,a s] : Fin 2 → A) = {1,a s} := by
      ext z
      simp only [Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff]
      constructor
      · rintro ⟨j,rfl⟩; fin_cases j <;> simp
      · rintro (rfl|rfl)
        · exact ⟨0,rfl⟩
        · exact ⟨1,rfl⟩
    have hl : LinearIndependent K (Fin.cons (a i) ![1,a s]) :=
      linearIndependent_finCons.mpr ⟨independent_one_transcendental (a s) ht,by rwa [hr]⟩
    let e : Option (Fin 2) → Fin 3 := fun o => o.elim 1 (fun j => if j=0 then 0 else 2)
    have he : Function.Injective e := by decide
    have h := hl.comp e he
    convert h using 1
    funext o
    cases o with
    | none => rfl
    | some j => fin_cases j <;> rfl
  · right
    push Not at hh
    choose b c he using fun i => Submodule.mem_span_pair.mp (hh i)
    refine ⟨c,b,fun i => ?_⟩
    have hi := he i
    simp only [Algebra.smul_def,mul_one] at hi
    rw [←hi]
    ring

end

open MvPolynomial
open scoped Classical BigOperators

theorem norm_surface_left_basis {n d : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] (k : ℕ)
    (a b : Fin d → MvPolynomial (Fin n) K) (q : MvPolynomial (Fin n) K) (θ : Fin d → K)
    (ha : ∀ i, Ideal.Quotient.mk I (a i) ≠ 0)
    (heq : ∀ i, Ideal.Quotient.mk I (a i)^k*Ideal.Quotient.mk I (b i) =
      Ideal.Quotient.mk I q-algebraMap K _ (θ i))
    (hg : Algebra.adjoin K (Set.range (fun i => Ideal.Quotient.mk I (a i)) ∪
        Set.range (fun i => Ideal.Quotient.mk I (b i))) = ⊤)
    (hq : Transcendental K (Ideal.Quotient.mk I q)) (hdim : affineDimension I = 2) :
    ∃ s : Fin d, AlgebraicIndependent K (Fin.cases (Ideal.Quotient.mk I q)
      (fun _ : Fin 1 => Ideal.Quotient.mk I (a s))) := by
  let := pair_projection_isAlgebraic k (fun i => Ideal.Quotient.mk I (a i))
    (fun i => Ideal.Quotient.mk I (b i)) (Ideal.Quotient.mk I q) θ ha heq hg
  obtain ⟨m,j,hj,_,htr⟩ := left_coordinates_transcendence_selection
    (fun i => Ideal.Quotient.mk I (a i)) (Ideal.Quotient.mk I q) hq
  have he := hilbert_natDegree_eq_trdeg I (coordinateHilbert I) (coordinateHilbert_eventually I)
  rw [htr] at he
  have hm : affineDimension I = m+1 := by exact_mod_cast he
  have h1 : m = 1 := by omega
  subst m
  refine ⟨j 0,?_⟩
  convert hj using 1
  funext i
  refine Fin.cases ?_ (fun n => ?_) i
  · rfl
  · have : n = 0 := Subsingleton.elim _ _
    subst n
    rfl

lemma conjugate_affine_slope_ne_zero {n d : ℕ} {K : Type*} [Field K] [CharZero K]
    (v : Fin d → K) (hv : LinearIndependent ℚ v) (σ : K →+* ℂ)
    (x : Fin d → Fin n) (I : Ideal (MvPolynomial (Fin n) ℂ))
    (c b : ℂ) (t : MvPolynomial (Fin n) ℂ ⧸ I)
    (he : Ideal.Quotient.mk I (coordinateLinearForm x (σ ∘ v)) = algebraMap ℂ _ c*t+algebraMap ℂ _ b)
    (z w : Fin n → ℤ) (hz : PointOn I z) (hw : PointOn I w)
    (hne : (fun i => z (x i)) ≠ (fun i => w (x i))) : c ≠ 0 := by
  intro hc
  rw [hc,map_zero,zero_mul,zero_add] at he
  have hh : MvPolynomial.aeval (fun j => (z j:ℂ)) (coordinateLinearForm x (σ ∘ v)) =
      MvPolynomial.aeval (fun j => (w j:ℂ)) (coordinateLinearForm x (σ ∘ v)) := by
    rw [polynomial_constant_at_point I _ b he.symm z hz,polynomial_constant_at_point I _ b he.symm w hw]
  simp only [coordinateLinearForm,map_sum,map_mul,aeval_C,aeval_X,Function.comp_apply,
    Algebra.algebraMap_self,RingHom.id_apply] at hh
  exact hne (integer_conjugate_form_injective v hv σ hh)

end

section

section
open scoped BigOperators Classical
open MvPolynomial

lemma pairAExponent_sum_low {n k A B D : ℕ} (i : PairBasisIndex n k)
    (hi : pairBasisWeight A B i = D) (hDA : D < 2*A) (hDB : D < B) :
    (pairAExponent i).sum (fun _ e => e) ≤ 1 := by
  have hb := pair_b_exponents_zero i hi hDB
  rw [pairBasisWeight_eq] at hi
  simp only [hb,mul_zero,add_zero] at hi
  have hs : (pairAExponent i).sum (fun _ e => e) = ∑ j, (pairIndexToTuple i j).1 := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    rfl
  rw [hs]
  rw [←Finset.mul_sum] at hi
  have : A * ∑ j, (pairIndexToTuple i j).1 < 2*A := by omega
  nlinarith

noncomputable def affineExponent {σ : Type*} : Option σ → σ →₀ ℕ :=
  fun o => o.elim 0 (fun i => Finsupp.single i 1)

lemma affineExponent_injective {σ : Type*} : Function.Injective (affineExponent (σ := σ)) := by
  classical
  intro i j h
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j =>
      have hh := congrArg (fun m : σ →₀ ℕ => m j) h
      simp [affineExponent] at hh
  | some i =>
    cases j with
    | none =>
      have hh := congrArg (fun m : σ →₀ ℕ => m i) h
      simp [affineExponent] at hh
    | some j =>
      by_contra hn
      have hne : i ≠ j := fun hij => hn (congrArg some hij)
      have hh := congrArg (fun m : σ →₀ ℕ => m i) h
      simp [affineExponent,hne] at hh

lemma exists_affineExponent {σ : Type*} (m : σ →₀ ℕ)
    (hm : m.sum (fun _ e => e) ≤ 1) : ∃ i, m = affineExponent i := by
  classical
  by_cases hz : m.sum (fun _ e => e) = 0
  · refine ⟨none,?_⟩
    change m = 0
    ext i
    by_cases hi : i ∈ m.support
    · have hbound := Finset.single_le_sum (f := fun j => m j)
        (fun j _ => Nat.zero_le _) hi
      change ∑ j ∈ m.support, m j = 0 at hz
      simp only [Finsupp.zero_apply]
      omega
    · exact Finsupp.notMem_support_iff.mp hi
  · obtain ⟨i,hi⟩ := (Finsupp.sum_eq_one_iff m).mp (by omega)
    exact ⟨some i,hi⟩

theorem pairCone_low_affine_degree_injective {n : ℕ} {K S : Type*} [Field K]
    [CommRing S] [Algebra K S] (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K)
    (φ : PairCone k A B θ →ₐ[K] S)
    (ht : φ (pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)) = 1)
    (ha : LinearIndependent K (fun o : Option (Fin (n+1)) => o.elim 1 (φ ∘ pairConeA k A B θ)))
    (c : PairCone k A B θ) (D : ℕ) (hDA : D < 2*A) (hDB : D < B)
    (hc : pairConeScale k A B θ c = Polynomial.monomial D c) (hφ : φ c = 0) : c = 0 := by
  classical
  let b := pairConeBasis k A B hB θ
  let w := pairBasisWeight (n := n) (k := k) A B
  let e : {i : PairBasisIndex n k // w i = D} → PairCone k A B θ := fun i => b i.val
  choose j hj using fun i : {i : PairBasisIndex n k // w i = D} =>
    exists_affineExponent (pairAExponent i.val) (pairAExponent_sum_low i.val i.property hDA hDB)
  have hjinj : Function.Injective j := by
    intro i l hil
    apply pairAExponent_injective_low hDB
    change pairAExponent i.val = pairAExponent l.val
    rw [hj i,hj l,hil]
  have hlin : LinearIndependent K (φ.toLinearMap ∘ e) := by
    have hg := ha.comp j hjinj
    convert hg using 1
    funext i
    change φ (b i.val) = _
    rw [pairConeBasis_map_low k A B hB θ φ ht i.val
      (pair_b_exponents_zero i.val i.property hDB),hj i]
    change MvPolynomial.aeval (φ ∘ pairConeA k A B θ)
      (MvPolynomial.monomial (affineExponent (j i)) 1) = (j i).elim 1 (φ ∘ pairConeA k A B θ)
    cases hji : j i with
    | none => simp [affineExponent]
    | some l => change MvPolynomial.aeval _ (MvPolynomial.X l) = _; simp
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

end
universe u v
open scoped BigOperators
theorem rootPair_actual_hilbert_uniform_affine {n : ℕ} {K : Type u} [Field K]
    {k : ℕ} (hk : 0 < k) (A B : ℕ) (hA : 0 < A) (hB : 0 < B) (E : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : Type v) [Field L] [Algebra K L], ∀ (θ : Fin (n+1) → K), Function.Injective θ →
      ∀ (ψ : RootPair k θ →ₐ[K] L), (∀ i, ψ (pairLeft k (rootPairQ θ) i) ≠ 0) →
      LinearIndependent K (fun o : Option (Fin (n+1)) => o.elim 1 (ψ ∘ pairLeft k (rootPairQ θ))) →
      ∀ (p : MvPolynomial (Option (Fin (n+1))) K), p ≠ 0 → p.totalDegree ≤ E →
      (∀ q, ψ (positiveToPair k (rootPairQ θ) q) = 0 ↔
        MvPolynomial.optionEquivRight K (Fin (n+1)) p ∣ q) →
      ∃ u v : ℕ, min (2*A) B ≤ A*u+B*v ∧ A*u+B*v ≤ (k*A+B)*E ∧
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
  refine ⟨Ctotal,htotal,fun L _ _ θ hθ ψ ha hind p hp hpE hker => ?_⟩
  obtain ⟨u,v,c,hD,hc,hc0,hct,hkerφ⟩ := rootPair_bounded_cone_kernel hk A B hB θ hθ ψ ha p hp hker
  let φ := ψ.comp (pairConeToRoot k A B θ)
  have hφc : φ c = 0 := by
    apply (show c ∈ RingHom.ker φ.toRingHom ↔ φ c = 0 from Iff.rfl).mp
    rw [hkerφ]
    exact (show Ideal.span {c} ≤ _ from le_sup_left) (Ideal.subset_span (Set.mem_singleton _))
  have hφa : φ ∘ pairConeA k A B (coneDifference θ) = ψ ∘ pairLeft k (rootPairQ θ) := by
    funext i
    simp only [φ,Function.comp_apply,AlgHom.comp_apply,pairConeToRoot_left]
  have hDlower : min (2*A) B ≤ A*u+B*v := by
    by_contra hnot
    have hlow : A*u+B*v < min (2*A) B := by omega
    have hi : LinearIndependent K (fun o : Option (Fin (n+1)) => o.elim 1 (φ ∘ pairConeA k A B (coneDifference θ))) := hφa ▸ hind
    exact hc0 (pairCone_low_affine_degree_injective k A B hB (coneDifference θ) φ
      (by simp [φ]) hi c (A*u+B*v) (hlow.trans_le (min_le_left _ _))
      (hlow.trans_le (min_le_right _ _)) hc hφc)
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
open scoped BigOperators Classical

lemma affine_pair_projection_bounded {n d : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (a : Fin d → MvPolynomial (Fin n) K) (x : MvPolynomial (Fin n) K)
    (j : Fin 2 → Fin d)
    (hind : AlgebraicIndependent K (Fin.cases (Ideal.Quotient.mk I x)
      (fun _ : Fin 1 => Ideal.Quotient.mk I (a (j 1)))))
    (hdim : affineDimension I = 2) (E D : ℕ) (hD : 0 < D)
    (hdeg : affineDegree I ≤ E) (hadeg : ∀ i, (a i).totalDegree ≤ D) (hxdeg : x.totalDegree ≤ D) :
    ∃ p : MvPolynomial (Option (Fin 2)) K, Irreducible p ∧ p.totalDegree ≤ E*D^2 ∧
      (∀ q, Ideal.Quotient.mk I (MvPolynomial.aeval (fun o => o.elim x (a ∘ j)) q) = 0 ↔ p ∣ q) := by
  have htr : Algebra.trdeg K (MvPolynomial (Fin n) K ⧸ I) = (1+1 : ℕ) := by
    rw [←hilbert_natDegree_eq_trdeg I (coordinateHilbert I) (coordinateHilbert_eventually I)]
    change (affineDimension I : Cardinal) = _
    rw [hdim]
  obtain ⟨p,hp,hkp⟩ := pair_principal_projection_of_extra
    (fun i : Fin 2 => Ideal.Quotient.mk I (a (j i))) (Ideal.Quotient.mk I x)
    (fun _ : Fin 1 => (1:Fin 2)) 0 hind htr
  have hj : (fun i : Fin 2 => Ideal.Quotient.mk I (a (j i))) ∘
      (Fin.cases (0 : Fin 2) (fun _ : Fin 1 => (1:Fin 2))) =
      fun i => Ideal.Quotient.mk I (a (j i)) := by
    funext i
    fin_cases i <;> rfl
  rw [hj] at hkp
  have hker (q) : Ideal.Quotient.mk I (MvPolynomial.aeval (fun o => o.elim x (a ∘ j)) q) = 0 ↔ p ∣ q := by
    rw [←hkp]
    change (Ideal.Quotient.mkₐ K I) (MvPolynomial.aeval _ q) = 0 ↔ _
    rw [MvPolynomial.comp_aeval_apply]
    have he : (fun o : Option (Fin 2) => (Ideal.Quotient.mkₐ K I) (o.elim x (a ∘ j))) =
        (fun o => o.elim (Ideal.Quotient.mk I x) (fun i => Ideal.Quotient.mk I (a (j i)))) := by
      funext o
      cases o <;> rfl
    rw [he]
  refine ⟨p,hp,?_,hker⟩
  have hb := affine_polynomial_projection_degree_bound (finSuccEquiv 2) I hdim
    (fun o => o.elim x (a ∘ j)) D hD (by intro o; cases o with
      | none => exact hxdeg
      | some i => exact hadeg (j i)) p hp.ne_zero hker
  have hb' : (p.totalDegree:ℚ) ≤ (E:ℚ)*(D:ℚ)^2 :=
    hb.trans (mul_le_mul_of_nonneg_right hdeg (by positivity))
  exact_mod_cast hb'

theorem norm_ambient_hilbert_uniform_affine_pair {n d : ℕ} {K : Type*} [Field K]
    {k : ℕ} (hk : 0 < k) (A B : ℕ) (hA : 0 < A) (hB : 0 < B)
    (E D : ℕ) (hD : 0 < D) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
        (a b : Fin d → MvPolynomial (Fin n) K) (x : MvPolynomial (Fin n) K)
        (θ : Fin d → K), Function.Injective θ →
      (∀ i, Ideal.Quotient.mk I (a i) ≠ 0) →
      (∀ i, Ideal.Quotient.mk I (a i)^k * Ideal.Quotient.mk I (b i) =
        Ideal.Quotient.mk I x - algebraMap K (MvPolynomial (Fin n) K ⧸ I) (θ i)) →
      ∀ (j : Fin 2 → Fin d), Function.Injective j →
      AlgebraicIndependent K (Fin.cases (Ideal.Quotient.mk I x)
        (fun _ : Fin 1 => Ideal.Quotient.mk I (a (j 1)))) →
      LinearIndependent K (fun o : Option (Fin 2) => o.elim 1 (fun i => Ideal.Quotient.mk I (a (j i)))) →
      affineDimension I = 2 → affineDegree I ≤ E →
      (∀ i, (a i).totalDegree ≤ D) → x.totalDegree ≤ D →
      ∀ (w : Fin n → ℕ), (∀ i, w i ≠ 0) →
        (∀ i, a i ∈ weightedSpace w A) → (∀ i, b i ∈ weightedSpace w B) →
      ∀ T : ℕ, (k*A+B)*(E*D^2) ≤ T →
        ((min (2*A) B:ℕ):ℝ)*((k*A+B : ℕ):ℝ) /
          (((2:ℕ).factorial:ℝ)*(A:ℝ)^2*(B:ℝ)^2)*(T:ℝ)^2 -
          C*((T:ℝ)+1)^1 ≤
          (Module.finrank K ((weightedSpace w T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℝ) := by
  obtain ⟨C,hC,hunif⟩ := rootPair_actual_hilbert_uniform_affine
    (n := 1) (K := K) hk A B hA hB (E*D^2)
  refine ⟨C,hC,fun I _ a b x θ hθ ha hab j hj hind hlind hdim hdeg hadeg hxdeg w hw haw hbw T hT => ?_⟩
  obtain ⟨p,hp,hpD,hkp⟩ := affine_pair_projection_bounded I a x j hind
    hdim E D hD hdeg hadeg hxdeg
  let S := MvPolynomial (Fin n) K ⧸ I
  let L := FractionRing S
  let e : S →ₐ[K] L := IsScalarTower.toAlgHom K S L
  have he : Function.Injective e := IsFractionRing.injective S L
  let aj : Fin 2 → S := fun i => Ideal.Quotient.mk I (a (j i))
  let bj : Fin 2 → S := fun i => Ideal.Quotient.mk I (b (j i))
  let xj : S := Ideal.Quotient.mk I x
  have habj : ∀ i, aj i ^ k * bj i = xj - algebraMap K S ((θ ∘ j) i) := fun i => hab (j i)
  let ψ : RootPair k (θ ∘ j) →ₐ[K] L := e.comp (rootPairEvaluation k (θ ∘ j) aj bj xj habj)
  have hψa (i) : ψ (pairLeft k (rootPairQ (θ ∘ j)) i) = e (Ideal.Quotient.mk I (a (j i))) := by
    simp only [ψ,AlgHom.comp_apply,rootPairEvaluation_left,aj]
  have hψb (i) : ψ (pairRight k (rootPairQ (θ ∘ j)) i) = e (Ideal.Quotient.mk I (b (j i))) := by
    simp only [ψ,AlgHom.comp_apply,rootPairEvaluation_right,bj]
  have hpa (i) : ψ (pairLeft k (rootPairQ (θ ∘ j)) i) ≠ 0 := by
    rw [hψa,map_ne_zero_iff e he]
    exact ha (j i)
  have hproj (q) : MvPolynomial.aeval (fun o => o.elim xj aj) q = 0 ↔ p ∣ q := by
    rw [←hkp]
    have hh := MvPolynomial.comp_aeval_apply
      (f := fun o : Option (Fin 2) => o.elim x (a ∘ j)) (Ideal.Quotient.mkₐ K I) q
    have hv : (fun o : Option (Fin 2) => (Ideal.Quotient.mkₐ K I) (o.elim x (a ∘ j))) =
        (fun o => o.elim xj aj) := by funext o; cases o <;> rfl
    rw [hv] at hh
    exact Iff.of_eq (congrArg (fun y => y = 0) hh.symm)
  have hker := rootPairEvaluation_comp_kernel k (θ ∘ j) aj bj xj habj e he p hproj
  have hindL : LinearIndependent K (fun o : Option (Fin 2) => o.elim 1 (ψ ∘ pairLeft k (rootPairQ (θ ∘ j)))) := by
    have hh := hlind.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr he)
    have heq : (e.toLinearMap ∘ (fun o : Option (Fin 2) => o.elim 1 (fun i => Ideal.Quotient.mk I (a (j i))))) =
        (fun o : Option (Fin 2) => o.elim 1 (ψ ∘ pairLeft k (rootPairQ (θ ∘ j)))) := by
      funext o
      cases o with
      | none => exact map_one e
      | some i => exact (hψa i).symm
    rw [heq] at hh
    exact hh
  obtain ⟨r,s,hmin,_,hH⟩ := hunif L (θ ∘ j) (hθ.comp hj) ψ hpa hindL p hp.ne_zero hpD hker
  have hR := rootPair_actual_hilbert_le I e he k A B hB (θ ∘ j) ψ
    (a ∘ j) (b ∘ j) w hw (fun i => haw (j i)) (fun i => hbw (j i)) hψa hψb T
  have hH' := (abs_le.mp (hH T hT)).1
  have hcoef : ((min (2*A) B:ℕ):ℝ)*((k*A+B : ℕ):ℝ) /
      (((2:ℕ).factorial:ℝ)*(A:ℝ)^2*(B:ℝ)^2)*(T:ℝ)^2 ≤
    ((A*r+B*s : ℕ):ℝ)*((k*A+B : ℕ):ℝ) /
      (((2:ℕ).factorial:ℝ)*(A:ℝ)^2*(B:ℝ)^2)*(T:ℝ)^2 := by
    gcongr
  have hR' : (Module.finrank K ((homogeneousSpace (pairConeScale k A B (coneDifference (θ ∘ j))) T).map
      (ψ.comp (pairConeToRoot k A B (θ ∘ j))).toLinearMap) : ℝ) ≤
      (Module.finrank K ((weightedSpace w T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℝ) := by exact_mod_cast hR
  norm_num only [Nat.reduceAdd,pow_one] at hH'
  linarith

end QuarticPowerFree

end OAI

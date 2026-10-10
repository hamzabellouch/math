import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.TaylorCoefficients

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.AdicFunctor
variable {R S : Type*} [CommRing R] [CommRing S]

lemma map_map_equiv (I : Ideal R) (J : Ideal S) (e : R ≃+* S)
    (h : I ≤ J.comap e.toRingHom) (h' : J ≤ I.comap e.symm.toRingHom) (x : AdicCompletion I R) :
    map J I e.symm.toRingHom h' (map I J e.toRingHom h x) = x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [eval_map,eval_map]
  generalize AdicCompletion.evalₐ I n x = y
  induction y using Quotient.inductionOn' with
  | _ r => change Ideal.Quotient.mk _ (e.symm (e r)) = _; rw [e.symm_apply_apply]; rfl

noncomputable def equiv (I : Ideal R) (J : Ideal S) (e : R ≃+* S)
    (h : I ≤ J.comap e.toRingHom) (h' : J ≤ I.comap e.symm.toRingHom) :
    AdicCompletion I R ≃+* AdicCompletion J S :=
  { map I J e.toRingHom h with
    invFun := map J I e.symm.toRingHom h'
    left_inv := map_map_equiv I J e h h'
    right_inv := map_map_equiv J I e.symm h' h }

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.AdicFunctor

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.PolynomialPointCompletion
variable {K α : Type*} [Field K] [Finite α]
open MvPolynomial

noncomputable def shift (a : α → K) : MvPolynomial α K ≃ₐ[K] MvPolynomial α K :=
  AlgEquiv.ofAlgHom (aeval fun i ↦ X i + C (a i)) (aeval fun i ↦ X i - C (a i))
    (by ext i; simp) (by ext i; simp)

omit [Finite α] in
lemma vars_ker [Finite α] : idealOfVars α K = RingHom.ker (constantCoeff : MvPolynomial α K →+* K) := by
  apply le_antisymm
  · rw [idealOfVars,Ideal.span_le]
    rintro _ ⟨i,rfl⟩
    simp
  · intro p hp
    rw [← pow_one (idealOfVars α K),mem_pow_idealOfVars_iff]
    intro e he
    have he0 : e ≠ 0 := by
      intro h; subst e
      exact (mem_support_iff.mp he) hp
    exact Nat.one_le_iff_ne_zero.mpr (by simpa [Finsupp.degree_eq_zero_iff] using he0)

omit [Finite α] in
lemma constant_shift [Finite α] (a : α → K) (p : MvPolynomial α K) :
    constantCoeff (shift a p) = aeval a p := by
  have h : (constantCoeff : MvPolynomial α K →+* K).comp (shift a).toRingHom =
      (aeval a).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro k; simp [shift]
    · intro i; simp [shift]
  exact RingHom.congr_fun h p

noncomputable def completionEquiv (a : α → K) :
    AdicCompletion (RingHom.ker (aeval a : MvPolynomial α K →ₐ[K] K).toRingHom) (MvPolynomial α K) ≃+*
      AdicCompletion (idealOfVars α K) (MvPolynomial α K) :=
  AdicFunctor.equiv _ _ (shift a).toRingEquiv
    (by intro p hp; rw [vars_ker]; exact (constant_shift a p).trans hp)
    (by
      intro p hp
      change aeval a ((shift a).symm p) = 0
      rw [← constant_shift,AlgEquiv.apply_symm_apply]
      rw [vars_ker] at hp
      exact hp)

theorem isDomain_completion (a : α → K) :
    IsDomain (AdicCompletion (RingHom.ker (aeval a : MvPolynomial α K →ₐ[K] K).toRingHom) (MvPolynomial α K)) := by
  have : IsDomain (MvPowerSeries α K) := NoZeroDivisors.to_isDomain _
  let e := (completionEquiv a).trans (MvPowerSeries.toAdicCompletionAlgEquiv α K).symm.toRingEquiv
  exact Function.Injective.isDomain e e.injective

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.PolynomialPointCompletion

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.CompletionScalar
open scoped TensorProduct
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

noncomputable def algebraMapCompletion (I : Ideal R) :
    AdicCompletion I R →ₐ[R] AdicCompletion (I.map (algebraMap R S)) S :=
  { AdicFunctor.map I (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map with
    commutes' := fun r ↦ AdicFunctor.map_of I (I.map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map r }

noncomputable def tensorHom (I : Ideal R) :
    AdicCompletion I R ⊗[R] S →ₐ[R] AdicCompletion (I.map (algebraMap R S)) S :=
  Algebra.TensorProduct.lift (algebraMapCompletion I)
    (IsScalarTower.toAlgHom R S _) (fun _ _ ↦ Commute.all _ _)

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

lemma tensorHom_eq [IsNoetherianRing R] [Module.Finite R S] (I : Ideal R) :
    (tensorHom (S := S) I).toLinearMap = (tensorEquiv I).toLinearMap := by
  apply TensorProduct.ext'
  intro r s
  change AdicFunctor.map I (I.map (algebraMap R S)) (algebraMap R S)
      Ideal.le_comap_map r * AdicCompletion.of (I.map (algebraMap R S)) S s =
    tensorEquiv I (r ⊗ₜ[R] s)
  exact (tensorEquiv_tmul I r s).symm

noncomputable def tensorAlgEquiv [IsNoetherianRing R] [Module.Finite R S] (I : Ideal R) :
    AdicCompletion I R ⊗[R] S ≃ₐ[R] AdicCompletion (I.map (algebraMap R S)) S :=
  AlgEquiv.ofBijective (tensorHom I) (by
    change Function.Bijective (tensorHom I).toLinearMap
    rw [tensorHom_eq]
    exact (tensorEquiv I).bijective)

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.CompletionScalar

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.CompletionCRT
open Function
variable {R ι : Type*} [CommRing R] [Fintype ι]

lemma pow_iInf (I : ι → Ideal R) (hI : Pairwise (IsCoprime on I)) (n : ℕ) :
    (⨅ i, I i)^n = ⨅ i, I i ^ n := by
  classical
  have h (J : ι → Ideal R) (hJ : Pairwise (IsCoprime on J)) :
      ∏ i, J i = ⨅ i, J i := by
    simpa using Ideal.prod_eq_iInf_of_pairwise_isCoprime
      (s := Finset.univ) (J := J) (fun i _ j _ hij ↦ hJ hij)
  rw [← h I hI,← h (fun i ↦ I i^n) (fun i j hij ↦ (hI hij).pow)]
  exact (Finset.prod_pow _ _ _).symm

noncomputable def level (I : ι → Ideal R) (hI : Pairwise (IsCoprime on I)) (n : ℕ) :
    R ⧸ (⨅ i, I i)^n ≃+* ∀ i, R ⧸ I i^n :=
  (Ideal.quotEquivOfEq (pow_iInf I hI n)).trans
    (Ideal.quotientInfRingEquivPiQuotient (fun i ↦ I i^n)
      (fun _ _ hij ↦ (hI hij).pow))

@[simp] lemma level_mk (I : ι → Ideal R) (hI : Pairwise (IsCoprime on I))
    (n : ℕ) (r : R) (i : ι) :
    level I hI n (Ideal.Quotient.mk _ r) i = Ideal.Quotient.mk (I i^n) r := rfl

lemma level_factor (I : ι → Ideal R) (hI : Pairwise (IsCoprime on I))
    {m n : ℕ} (h : m ≤ n) (x : R ⧸ (⨅ i, I i)^n) (i : ι) :
    level I hI m (Ideal.Quotient.factorPow (⨅ i, I i) h x) i =
      Ideal.Quotient.factorPow (I i) h (level I hI n x i) := by
  induction x using Quotient.inductionOn' with
  | _ r => rfl

noncomputable def forward (I : ι → Ideal R) :
    AdicCompletion (⨅ i, I i) R →+* ∀ i, AdicCompletion (I i) R :=
  RingHom.pi (fun i ↦ AdicFunctor.map (⨅ i, I i) (I i) (RingHom.id R)
    (by simpa using (iInf_le I i)))

lemma eval_to (I : ι → Ideal R) (hI : Pairwise (IsCoprime on I))
    (n : ℕ) (x : AdicCompletion (⨅ i, I i) R) (i : ι) :
    AdicCompletion.evalₐ (I i) n (forward I x i) =
      level I hI n (AdicCompletion.evalₐ (⨅ i, I i) n x) i := by
  change AdicCompletion.evalₐ (I i) n (AdicFunctor.map _ _ _ _ x) = _
  rw [AdicFunctor.eval_map]
  generalize AdicCompletion.evalₐ (⨅ i, I i) n x = y
  induction y using Quotient.inductionOn' with
  | _ r => rfl

noncomputable def inverseFamily (I : ι → Ideal R)
    (hI : Pairwise (IsCoprime on I)) (n : ℕ) :
    (∀ i, AdicCompletion (I i) R) →+* R ⧸ (⨅ i, I i)^n :=
  (level I hI n).symm.toRingHom.comp
    (RingHom.pi fun i ↦ (AdicCompletion.evalₐ (I i) n).toRingHom.comp (Pi.evalRingHom _ i))

lemma inverseFamily_compatible (I : ι → Ideal R) (hI : Pairwise (IsCoprime on I))
    {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow (⨅ i, I i) h).comp (inverseFamily I hI n) =
      inverseFamily I hI m := by
  ext x
  apply (level I hI m).injective
  funext i
  change level I hI m (Ideal.Quotient.factorPow (⨅ i, I i) h
    ((level I hI n).symm (fun j ↦ AdicCompletion.evalₐ (I j) n (x j)))) i =
    level I hI m ((level I hI m).symm (fun j ↦ AdicCompletion.evalₐ (I j) m (x j))) i
  rw [level_factor,RingEquiv.apply_symm_apply,RingEquiv.apply_symm_apply]
  exact AdicCofinal.factor_eval (I i) h (x i)

noncomputable def inverse (I : ι → Ideal R) (hI : Pairwise (IsCoprime on I)) :
    (∀ i, AdicCompletion (I i) R) →+* AdicCompletion (⨅ i, I i) R :=
  AdicCompletion.liftRingHom _ (inverseFamily I hI) (inverseFamily_compatible I hI)

lemma eval_inverse (I : ι → Ideal R) (hI : Pairwise (IsCoprime on I))
    (n : ℕ) (x : ∀ i, AdicCompletion (I i) R) :
    AdicCompletion.evalₐ (⨅ i, I i) n (inverse I hI x) =
      (level I hI n).symm (fun i ↦ AdicCompletion.evalₐ (I i) n (x i)) :=
  AdicCompletion.evalₐ_liftRingHom _ _ (inverseFamily_compatible I hI) n x

noncomputable def equiv (I : ι → Ideal R) (hI : Pairwise (IsCoprime on I)) :
    AdicCompletion (⨅ i, I i) R ≃+* ∀ i, AdicCompletion (I i) R :=
  { forward I with
    invFun := inverse I hI
    left_inv := fun x ↦ by
      apply AdicCompletion.ext_evalₐ
      intro n
      rw [eval_inverse]
      apply (level I hI n).injective
      rw [RingEquiv.apply_symm_apply]
      funext i
      exact eval_to I hI n x i
    right_inv := fun x ↦ by
      funext i
      apply AdicCompletion.ext_evalₐ
      intro n
      change AdicCompletion.evalₐ (I i) n (forward I (inverse I hI x) i) = _
      rw [eval_to I hI,eval_inverse,RingEquiv.apply_symm_apply] }

theorem reduced_factor (I : ι → Ideal R) (hI : Pairwise (IsCoprime on I))
    [IsReduced (AdicCompletion (⨅ i, I i) R)] (i : ι) :
    IsReduced (AdicCompletion (I i) R) := by
  classical
  have : IsReduced (∀ i, AdicCompletion (I i) R) :=
    isReduced_of_injective (equiv I hI).symm (equiv I hI).symm.injective
  constructor
  intro x hx
  obtain ⟨n,hn⟩ := hx
  have hn1 : x^(n+1) = 0 := by rw [pow_succ,hn,zero_mul]
  let y : ∀ j, AdicCompletion (I j) R := fun j ↦ if h : j = i then h ▸ x else 0
  have hy : IsNilpotent y := ⟨n+1,by
    funext j
    by_cases h : j = i
    · subst j
      simpa [y] using hn1
    · simp [y,h]⟩
  have hz := congrFun hy.eq_zero i
  simpa [y] using hz

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.CompletionCRT

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.PowerCofinal
variable {R : Type*} [CommRing R]

def family (I J : Ideal R) (c : ℕ)
    (hc : ∀ n, I ^ (c*n) ≤ J ^ n) (n : ℕ) :
    AdicCompletion I R →+* R ⧸ J ^ n :=
  (Ideal.Quotient.factor (hc n)).comp (AdicCompletion.evalₐ I (c*n)).toRingHom

lemma compatible (I J : Ideal R) (c : ℕ)
    (hc : ∀ n, I ^ (c*n) ≤ J ^ n) {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow J h).comp (family I J c hc n) = family I J c hc m := by
  ext x
  have hx := AdicCofinal.factor_eval I (Nat.mul_le_mul_left c h) x
  have hy := congrArg (Ideal.Quotient.factor (hc m)) hx
  simpa only [family,RingHom.comp_apply,AlgHom.toRingHom_eq_coe,RingHom.coe_coe,
    Ideal.Quotient.factorPow,Ideal.Quotient.factor_comp_apply] using hy

noncomputable def map (I J : Ideal R) (c : ℕ)
    (hc : ∀ n, I ^ (c*n) ≤ J ^ n) : AdicCompletion I R →+* AdicCompletion J R :=
  AdicCompletion.liftRingHom J (family I J c hc) (compatible I J c hc)

@[simp] lemma eval_map (I J : Ideal R) (c : ℕ)
    (hc : ∀ n, I ^ (c*n) ≤ J ^ n) (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (map I J c hc x) =
      Ideal.Quotient.factor (hc n) (AdicCompletion.evalₐ I (c*n) x) :=
  AdicCompletion.evalₐ_liftRingHom J _ (compatible I J c hc) n x

lemma map_map (I J : Ideal R) (c d : ℕ) (hc0 : 0 < c) (hd0 : 0 < d)
    (hc : ∀ n, I ^ (c*n) ≤ J ^ n) (hd : ∀ n, J ^ (d*n) ≤ I ^ n)
    (x : AdicCompletion I R) : map J I d hd (map I J c hc x) = x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  simp only [eval_map]
  have hn : n ≤ c*(d*n) := (Nat.le_mul_of_pos_left n hd0).trans
    (Nat.le_mul_of_pos_left (d*n) hc0)
  have he := AdicCofinal.factor_eval I hn x
  simpa only [Ideal.Quotient.factorPow,Ideal.Quotient.factor_comp_apply] using he

noncomputable def equiv (I J : Ideal R) (c d : ℕ) (hc0 : 0 < c) (hd0 : 0 < d)
    (hc : ∀ n, I ^ (c*n) ≤ J ^ n) (hd : ∀ n, J ^ (d*n) ≤ I ^ n) :
    AdicCompletion I R ≃+* AdicCompletion J R :=
  { map I J c hc with
    invFun := map J I d hd
    left_inv := map_map I J c d hc0 hd0 hc hd
    right_inv := map_map J I d c hd0 hc0 hd hc }

noncomputable def radicalEquiv [IsNoetherianRing R] (I : Ideal R) :
    AdicCompletion I R ≃+* AdicCompletion I.radical R := by
  let hc0 := Ideal.exists_pow_le_of_le_radical_of_fg (le_refl I.radical)
    (IsNoetherian.noetherian I.radical)
  let c := hc0.choose
  have hc := hc0.choose_spec
  refine equiv I I.radical 1 (c+1) (by omega) (by omega)
    (fun n ↦ by simpa using (pow_le_pow_left' Ideal.le_radical n)) ?_
  intro n
  rw [pow_mul]
  exact pow_le_pow_left' ((Ideal.pow_le_pow_right (by omega : c ≤ c+1)).trans hc) n

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.PowerCofinal

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.SemilocalCompletion
variable {R : Type*} [CommRing R] [IsNoetherianRing R]
variable (I : Ideal R) [IsArtinianRing (R ⧸ I)]

noncomputable def primes (p : PrimeSpectrum (R ⧸ I)) : Ideal R :=
  p.asIdeal.comap (Ideal.Quotient.mk I)

instance primesMaximal (p : PrimeSpectrum (R ⧸ I)) : (primes I p).IsMaximal :=
  Ideal.comap_isMaximal_of_surjective _ (Ideal.Quotient.mk_surjective)

omit [IsNoetherianRing R] in
lemma primes_pairwise [IsNoetherianRing R] :
    Pairwise (fun p q ↦ IsCoprime (primes I p) (primes I q)) := by
  intro p q hpq
  apply Ideal.isCoprime_of_isMaximal
  intro h
  apply hpq
  apply PrimeSpectrum.ext
  exact Ideal.comap_injective_of_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective h

omit [IsNoetherianRing R] [IsArtinianRing (R ⧸ I)] in
lemma iInf_primes [IsNoetherianRing R] [IsArtinianRing (R ⧸ I)] :
    (⨅ p, primes I p) = I.radical := by
  unfold primes
  rw [← Ideal.comap_iInf,← PrimeSpectrum.nilradical_eq_iInf]
  change (Ideal.radical (⊥ : Ideal (R ⧸ I))).comap _ = _
  rw [Ideal.comap_radical,← RingHom.ker_eq_comap_bot,Ideal.mk_ker]

theorem reduced_at_maximal [IsReduced (AdicCompletion I R)]
    (p : Ideal R) [p.IsMaximal] (hIp : I ≤ p) : IsReduced (AdicCompletion p R) := by
  classical
  let : Fintype (PrimeSpectrum (R ⧸ I)) := Fintype.ofFinite _
  have : IsReduced (AdicCompletion I.radical R) :=
    isReduced_of_injective (PowerCofinal.radicalEquiv I).symm
      (PowerCofinal.radicalEquiv I).symm.injective
  have : IsReduced (AdicCompletion (⨅ q,primes I q) R) := by
    rw [iInf_primes]
    infer_instance
  have hp : (p.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hIp)
  let q : PrimeSpectrum (R ⧸ I) := ⟨p.map (Ideal.Quotient.mk I),hp⟩
  have hq : primes I q = p := by
    change (p.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = p
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    rw [← RingHom.ker_eq_comap_bot,Ideal.mk_ker,sup_eq_left.mpr hIp]
  rw [← hq]
  exact CompletionCRT.reduced_factor (primes I) (primes_pairwise I) q

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.SemilocalCompletion

end

end OAI

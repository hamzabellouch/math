import OAI.NumberTheory.PowerFree.RootPairHilbert

namespace OAI

universe u

namespace QuarticPowerFree

section
open scoped BigOperators Classical

def pairSplitFirst {h : ℕ} (p : Fin (h+1) → ℕ × ℕ) : Fin (h+2) → ℕ × ℕ :=
  Fin.cons ((p 0).1,0) (Fin.cons (0,(p 0).2) (fun i => p i.succ))

theorem pairSplitFirst_injective {h : ℕ} : Function.Injective (pairSplitFirst (h := h)) := by
  intro p q he
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · have h0 := congrArg (fun r => (r 0).1) he
    have h1 := congrArg (fun r => (r 1).2) he
    exact Prod.ext h0 h1
  · exact congrFun he j.succ.succ

theorem pairSplitFirst_weight {h : ℕ} (A B : ℕ) (p : Fin (h+1) → ℕ × ℕ) :
    ∑ i, (A*(pairSplitFirst p i).1+B*(pairSplitFirst p i).2) =
      ∑ i, (A*(p i).1+B*(p i).2) := by
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp only [pairSplitFirst,Fin.cons_zero,Fin.cons_succ,mul_zero,add_zero,zero_add]
  omega

theorem ambientPairTuples_card_full {h A B k T : ℕ} (hA : 0 < A) (hB : 0 < B) :
    (ambientPairTuples h A B k T).card =
      (normalPairTuples A B (Fin.cons 0 (Fin.cons 1 (fun _ : Fin h => k)))
        (Fin.cons 1 (Fin.cons 0 (fun _ : Fin h => 1))) T).card := by
  classical
  apply Finset.card_bij (fun p _ => pairSplitFirst p)
  · intro p hp
    obtain ⟨hn,hw⟩ := (mem_ambientPairTuples hA hB p).mp hp
    apply (mem_normalPairTuples hA hB _ _ _ _).mpr
    refine ⟨?_,(pairSplitFirst_weight A B p).symm ▸ hw⟩
    intro i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => ?_) j) i
    · simp [pairSplitFirst]
    · simp [pairSplitFirst]
    · simpa only [Fin.cons_succ,pairSplitFirst,Nat.lt_one_iff] using hn l
  · intro p _ q _ he
    exact pairSplitFirst_injective he
  · intro q hq
    obtain ⟨hn,hw⟩ := (mem_normalPairTuples hA hB _ _ _ _).mp hq
    have h0 : (q 0).2 = 0 := by
      have hh := hn 0
      simp only [Fin.cons_zero,Nat.not_lt_zero,false_or] at hh
      omega
    have h1 : (q 1).1 = 0 := by
      have hh := hn 1
      change (q 1).1 < 1 ∨ (q 1).2 < 0 at hh
      omega
    let p : Fin (h+1) → ℕ × ℕ := Fin.cons ((q 0).1,(q 1).2) (fun i => q i.succ.succ)
    have he : pairSplitFirst p = q := by
      funext i
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => ?_) j) i
      · exact Prod.ext rfl h0.symm
      · exact Prod.ext h1.symm rfl
      · rfl
    refine ⟨p,(mem_ambientPairTuples hA hB p).mpr ⟨?_,?_⟩,he⟩
    · intro i
      simpa only [p,Fin.cons_succ,Nat.lt_one_iff] using hn i.succ.succ
    · rw [←pairSplitFirst_weight A B p,he]
      exact hw

theorem ambientPairTuples_hilbert_error {h A B k : ℕ} (hA : 0 < A) (hB : 0 < B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ,
      |((ambientPairTuples h A B k T).card : ℝ) -
        ((k*A+B : ℕ):ℝ)^h / (((h+2).factorial:ℝ)*(A:ℝ)^(h+1)*(B:ℝ)^(h+1))*(T:ℝ)^(h+2)| ≤
        C*((T:ℝ)+1)^(h+1) := by
  obtain ⟨C,hC,hh⟩ := normalPairTuples_hilbert_error hA hB
    (Fin.cons 0 (Fin.cons 1 (fun _ : Fin h => k)))
    (Fin.cons 1 (Fin.cons 0 (fun _ : Fin h => 1)))
  refine ⟨C,hC,fun T => ?_⟩
  rw [ambientPairTuples_card_full hA hB]
  have hp : (∏ i : Fin (h+2),
      (((((Fin.cons (α := fun _ => ℕ) 0 (Fin.cons 1 (fun _ : Fin h => k))) i):ℕ):ℝ)*A+
        ((((Fin.cons (α := fun _ => ℕ) 1 (Fin.cons 0 (fun _ : Fin h => 1))) i):ℕ):ℝ)*B)) =
        (A:ℝ)*B*((k*A+B:ℕ):ℝ)^h := by
    rw [Fin.prod_univ_succ,Fin.prod_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,Nat.cast_zero,Nat.cast_one,zero_mul,one_mul,
      zero_add,add_zero,Finset.prod_const,Finset.card_univ,Fintype.card_fin,Nat.cast_add,Nat.cast_mul]
    ring
  have ha : (A:ℝ) ≠ 0 := by positivity
  have hb : (B:ℝ) ≠ 0 := by positivity
  have hc : (A:ℝ)*B*((k*A+B:ℕ):ℝ)^h /
      (((h+2).factorial:ℝ)*(A:ℝ)^(h+2)*(B:ℝ)^(h+2)) =
      ((k*A+B:ℕ):ℝ)^h/(((h+2).factorial:ℝ)*(A:ℝ)^(h+1)*(B:ℝ)^(h+1)) := by
    rw [show h+2 = (h+1)+1 by omega,pow_succ,pow_succ]
    field_simp
    ring
  simpa only [hp,hc,show h+2-1 = h+1 by omega] using hh T

end
section
open MvPolynomial

theorem norm_full_projection_independent {d : ℕ} {K A : Type*}
    [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    (k : ℕ) (a b : Fin d → A) (x : A) (θ : Fin d → K)
    (ha : ∀ i, a i ≠ 0) (hab : ∀ i, a i^k*b i = x-algebraMap K A (θ i))
    (hgen : Algebra.adjoin K (Set.range a ∪ Set.range b) = ⊤)
    (hx : Transcendental K x) (htr : Algebra.trdeg K A = (d+1:ℕ)) :
    AlgebraicIndependent K (fun o : Option (Fin d) => o.elim x a) := by
  let := pair_projection_isAlgebraic k a b x θ ha hab hgen
  obtain ⟨m,j,hj,hji,hm⟩ := left_coordinates_transcendence_selection a x hx
  have hmd : m = d := by rw [htr] at hm; exact_mod_cast (Nat.add_right_cancel (by exact_mod_cast hm.symm))
  subst m
  let e : Fin d ≃ Fin d := Equiv.ofBijective j ⟨hji,Finite.surjective_of_injective hji⟩
  let g : Option (Fin d) → Fin (d+1) := fun o => o.elim 0 (fun i => (e.symm i).succ)
  have hg : Function.Injective g := by
    intro o p he
    cases o <;> cases p
    · rfl
    · exact (Fin.succ_ne_zero _ he.symm).elim
    · exact (Fin.succ_ne_zero _ he).elim
    · exact congrArg some (e.symm.injective (Fin.succ_injective _ he))
  have heq : Fin.cases x (a ∘ j) ∘ g = fun o : Option (Fin d) => o.elim x a := by
    funext o
    cases o with
    | none => rfl
    | some i =>
      change a (e (e.symm i)) = a i
      rw [e.apply_symm_apply]
  exact heq ▸ hj.comp g hg

theorem rootPair_evaluation_injective {d : ℕ} {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (k : ℕ) (θ : Fin d → K) (a b : Fin d → L) (x : L)
    (hab : ∀ i, a i^k*b i = x-algebraMap K L (θ i))
    (hi : AlgebraicIndependent K (fun o : Option (Fin d) => o.elim x a)) :
    Function.Injective (rootPairEvaluation k θ a b x hab) := by
  let q := rootPairQ θ
  let ψ := rootPairEvaluation k θ a b x hab
  let φ := ψ.toRingHom.comp (positiveToPair k q)
  have hφ : Function.Injective φ := by
    have he (p) : φ ((optionEquivRight K (Fin d)) p) = aeval (fun o => o.elim x a) p :=
      rootPairEvaluation_projection k θ a b x hab p
    intro p r hpr
    let E := optionEquivRight K (Fin d)
    have hp := he (E.symm p)
    have hr := he (E.symm r)
    rw [E.apply_symm_apply] at hp hr
    have hinj := hi
    exact E.symm.injective (hinj (hp.symm.trans (hpr.trans hr)))
  have ha (i) : ψ.toRingHom (pairCoordinate k q i) ≠ 0 := by
    have hn : (X i : MvPolynomial (Fin d) (Polynomial K)) ≠ 0 := X_ne_zero i
    have hh : φ (X i) ≠ 0 := (map_ne_zero_iff φ hφ).mpr hn
    simpa only [φ,RingHom.comp_apply,positiveToPair_X] using hh
  have haφ (i) : φ (X i) ≠ 0 := by simpa only [φ,RingHom.comp_apply,positiveToPair_X] using ha i
  obtain ⟨ℓ,hℓ,hker⟩ := positiveLaurent_kernel φ haφ
  rw [(RingHom.ker_eq_bot_iff_eq_zero φ).mpr (fun p hp => hφ (hp.trans (map_zero φ).symm)),Ideal.map_bot] at hker
  have hℓinj : Function.Injective ℓ := (RingHom.injective_iff_ker_eq_bot ℓ).mpr hker
  have he := pair_laurent_evaluation k q ψ.toRingHom ℓ ha hℓ
  change Function.Injective ψ.toRingHom
  rw [←he]
  exact hℓinj.comp (pairToLaurent_injective k q (fun i => Polynomial.X_sub_C_ne_zero (θ i)))

theorem pairCone_full_finrank {n : ℕ} {K L : Type*} [Field K] [Field L] [Algebra K L]
    (k A B : ℕ) (hA : 0 < A) (hB : 0 < B) (θ : Fin (n+1) → K)
    (ψ : RootPair k θ →ₐ[K] L) (hψ : Function.Injective ψ) (T : ℕ) :
    Module.finrank K ((homogeneousSpace (pairConeScale k A B (coneDifference θ)) T).map
      (ψ.comp (pairConeToRoot k A B θ)).toLinearMap) =
      (ambientPairTuples n A B k T).card := by
  let : (Ideal.span (Set.range (pairRelation k (pairConeQ k A B (coneDifference θ))))).IsPrime :=
    pair_ideal_isPrime k _ (pairConeQ_ne_zero k A B hB (coneDifference θ))
  let f := (ψ.comp (pairConeToRoot k A B θ)).toLinearMap.domRestrict
    (homogeneousSpace (pairConeScale k A B (coneDifference θ)) T)
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro c hc
    apply Subtype.ext
    have hz : pairConeToRoot k A B θ c.val = 0 := hψ (hc.trans (map_zero ψ).symm)
    have hmem : c.val ∈ Ideal.span {pairCoeffMap k (pairConeQ k A B (coneDifference θ)) (X 2)-1} := by
      rw [←pairConeToRoot_kernel k A B θ]
      exact hz
    exact homogeneous_dehomogenization_zero (pairConeScale k A B (coneDifference θ))
      (pairCone_t_prime k A B hB (coneDifference θ)).ne_zero
      (pairCone_t_homogeneous k A B (coneDifference θ)) c.property
      (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  have he := LinearMap.finrank_range_of_inj hf
  rw [LinearMap.range_domRestrict] at he
  exact he.trans (pairCone_finrank k A B hA hB (coneDifference θ) T)

theorem norm_full_hilbert_uniform {N n : ℕ} {K : Type u} [Field K]
    (k A B : ℕ) (hA : 0 < A) (hB : 0 < B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (I : Ideal (MvPolynomial (Fin N) K)) [I.IsPrime]
        (a b : Fin (n+1) → MvPolynomial (Fin N) K) (x : MvPolynomial (Fin N) K)
        (θ : Fin (n+1) → K),
      (∀ i, Ideal.Quotient.mk I (a i) ≠ 0) →
      (∀ i, Ideal.Quotient.mk I (a i)^k * Ideal.Quotient.mk I (b i) =
        Ideal.Quotient.mk I x - algebraMap K (MvPolynomial (Fin N) K ⧸ I) (θ i)) →
      Algebra.adjoin K (Set.range (fun i => Ideal.Quotient.mk I (a i)) ∪
        Set.range (fun i => Ideal.Quotient.mk I (b i))) = ⊤ →
      Transcendental K (Ideal.Quotient.mk I x) → affineDimension I = n+2 →
      ∀ (w : Fin N → ℕ), (∀ i, w i ≠ 0) →
        (∀ i, a i ∈ weightedSpace w A) → (∀ i, b i ∈ weightedSpace w B) →
      ∀ T : ℕ,
        ((k*A+B : ℕ):ℝ)^n / (((n+2).factorial:ℝ)*(A:ℝ)^(n+1)*(B:ℝ)^(n+1))*(T:ℝ)^(n+2) -
          C*((T:ℝ)+1)^(n+1) ≤
          (Module.finrank K ((weightedSpace w T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℝ) := by
  obtain ⟨C,hC,hH⟩ := ambientPairTuples_hilbert_error (h := n) (k := k) hA hB
  refine ⟨C,hC,fun I _ a b x θ ha hab hgen hx hdim w hw haw hbw T => ?_⟩
  let S := MvPolynomial (Fin N) K ⧸ I
  let L := FractionRing S
  let e : S →ₐ[K] L := IsScalarTower.toAlgHom K S L
  have he : Function.Injective e := IsFractionRing.injective S L
  let aj : Fin (n+1) → S := fun i => Ideal.Quotient.mk I (a i)
  let bj : Fin (n+1) → S := fun i => Ideal.Quotient.mk I (b i)
  let xj : S := Ideal.Quotient.mk I x
  have htr : Algebra.trdeg K S = (n+2:ℕ) := by
    rw [←hilbert_natDegree_eq_trdeg I (coordinateHilbert I) (coordinateHilbert_eventually I)]
    change (affineDimension I : Cardinal) = _
    rw [hdim]
  have hi := norm_full_projection_independent k aj bj xj θ ha hab hgen hx htr
  have hil : AlgebraicIndependent K (fun o : Option (Fin (n+1)) => o.elim (e xj) (e ∘ aj)) := by
    have hh := hi.map' he
    convert hh using 1
    funext o
    cases o <;> rfl
  have habL (i) : (e (aj i))^k*e (bj i) = e xj-algebraMap K L (θ i) := by
    have hh : aj i^k*bj i = xj-algebraMap K S (θ i) := hab i
    simpa only [map_mul,map_pow,map_sub,AlgHom.commutes] using congrArg e hh
  let ψ : RootPair k θ →ₐ[K] L := rootPairEvaluation k θ (e ∘ aj) (e ∘ bj) (e xj) habL
  have hinj : Function.Injective ψ := rootPair_evaluation_injective k θ (e ∘ aj) (e ∘ bj) (e xj) habL hil
  have hR := rootPair_actual_hilbert_le I e he k A B hB θ ψ a b w hw haw hbw
    (fun i => rootPairEvaluation_left k θ (e ∘ aj) (e ∘ bj) (e xj) habL i)
    (fun i => rootPairEvaluation_right k θ (e ∘ aj) (e ∘ bj) (e xj) habL i) T
  rw [pairCone_full_finrank k A B hA hB θ ψ hinj T] at hR
  have hR' : ((ambientPairTuples n A B k T).card:ℝ) ≤
      (Module.finrank K ((weightedSpace w T).map (Ideal.Quotient.mkₐ K I).toLinearMap):ℝ) := by exact_mod_cast hR
  have hh := (abs_le.mp (hH T)).1
  linarith

end

theorem uniform_real_hilbert_floor (h M : ℕ) (L α C : ℝ)
    (hL : 0 < L) (hα : 0 ≤ α) (hC : 0 ≤ C) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (H : ℕ → ℝ) (G : ℝ → ℝ),
      (∀ T, 0 ≤ G T) →
      (∀ T, 1 ≤ T → H ⌊L*T⌋₊ ≤ G T) →
      (∀ N, M ≤ N → α*(N:ℝ)^(h+1)-C*((N:ℝ)+1)^h ≤ H N) →
      ∀ T, 1 ≤ T → α*L^(h+1)*T^(h+1)-c*T^h ≤ G T := by
  let c := α*(h+1)*L^h + C*(L+1)^h + α*(M:ℝ)^(h+1)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨c,hc,fun H G hG hi hl T hT => ?_⟩
  let N := ⌊L*T⌋₊
  have hT0 : 0 ≤ T := by linarith
  have hLT : 0 ≤ L*T := mul_nonneg hL.le hT0
  have hN : (N:ℝ) ≤ L*T := Nat.floor_le hLT
  have hN1 : L*T < (N:ℝ)+1 := Nat.lt_floor_add_one _
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hTh : 1 ≤ T^h := one_le_pow₀ hT
  have hpowtarget : α*L^(h+1)*T^(h+1) = α*(L*T)^(h+1) := by rw [mul_pow]; ring
  rw [hpowtarget]
  by_cases hMN : M ≤ N
  · have hh := (hl N hMN).trans (hi T hT)
    have hab : |L*T-(N:ℝ)| ≤ 1 := by rw [abs_of_nonneg (sub_nonneg.mpr hN)]; linarith
    have hdiff := abs_pow_sub_pow_le (a := L*T) (b := (N:ℝ)) (n := h+1)
    rw [abs_of_nonneg hLT,abs_of_nonneg hN0,max_eq_left hN,Nat.add_sub_cancel] at hdiff
    have hdiff' : (L*T)^(h+1)-(N:ℝ)^(h+1) ≤ (h+1:ℕ)*(L*T)^h := by
      refine (le_abs_self _).trans (hdiff.trans ?_)
      calc |L*T-(N:ℝ)| * (h+1:ℕ)*(L*T)^h ≤ 1*(h+1:ℕ)*(L*T)^h := by gcongr
           _ = (h+1:ℕ)*(L*T)^h := by ring
    have hd := mul_le_mul_of_nonneg_left hdiff' hα
    have hNp : (N:ℝ)+1 ≤ (L+1)*T := by nlinarith
    have he : C*((N:ℝ)+1)^h ≤ C*(L+1)^h*T^h := by
      rw [mul_assoc,←mul_pow]
      gcongr
    have hsmall : 0 ≤ α*(M:ℝ)^(h+1)*T^h := by positivity
    simp only [mul_pow] at hd ⊢
    push_cast at hd
    dsimp only [c]
    nlinarith only [hh,hd,he,hsmall]
  · have hNM : N+1 ≤ M := by omega
    have hNM' : (N:ℝ)+1 ≤ M := by exact_mod_cast hNM
    have hM : L*T ≤ M := by linarith
    have hp : (L*T)^(h+1) ≤ (M:ℝ)^(h+1) := pow_le_pow_left₀ hLT hM _
    have hpα := mul_le_mul_of_nonneg_left hp hα
    have hscale : α*(M:ℝ)^(h+1) ≤ α*(M:ℝ)^(h+1)*T^h :=
      le_mul_of_one_le_right (by positivity) hTh
    have hother : 0 ≤ (α*(h+1)*L^h+C*(L+1)^h)*T^h := by positivity
    dsimp only [c]
    linarith [hG T]

open MvPolynomial

theorem norm_full_real_hilbert_uniform {N n : ℕ} {K : Type u} [Field K]
    (k A B : ℕ) (hA : 0 < A) (hB : 0 < B) (L : ℝ) (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (I : Ideal (MvPolynomial (Fin N) K)) [I.IsPrime]
        (a b : Fin (n+1) → MvPolynomial (Fin N) K) (x : MvPolynomial (Fin N) K)
        (θ : Fin (n+1) → K),
      (∀ i, Ideal.Quotient.mk I (a i) ≠ 0) →
      (∀ i, Ideal.Quotient.mk I (a i)^k * Ideal.Quotient.mk I (b i) =
        Ideal.Quotient.mk I x - algebraMap K (MvPolynomial (Fin N) K ⧸ I) (θ i)) →
      Algebra.adjoin K (Set.range (fun i => Ideal.Quotient.mk I (a i)) ∪
        Set.range (fun i => Ideal.Quotient.mk I (b i))) = ⊤ →
      Transcendental K (Ideal.Quotient.mk I x) → affineDimension I = n+2 →
      ∀ (w : Fin N → ℕ), (∀ i, w i ≠ 0) →
        (∀ i, a i ∈ weightedSpace w A) → (∀ i, b i ∈ weightedSpace w B) →
      ∀ (ω : Fin N → ℝ), (∀ i, 0 < ω i) → (∀ i, (w i:ℝ) = L*ω i) →
      ∀ T : ℝ, 1 ≤ T →
        ((k*A+B : ℕ):ℝ)^n*L^(n+2) / (((n+2).factorial:ℝ)*(A:ℝ)^(n+1)*(B:ℝ)^(n+1))*T^(n+2) -
          C*T^(n+1) ≤ weightedHilbert I ω T := by
  let α : ℝ := ((k*A+B : ℕ):ℝ)^n /
    (((n+2).factorial:ℝ)*(A:ℝ)^(n+1)*(B:ℝ)^(n+1))
  have hα : 0 ≤ α := by dsimp [α]; positivity
  obtain ⟨C,hC,hh⟩ := norm_full_hilbert_uniform (N := N) (n := n) (K := K) k A B hA hB
  obtain ⟨c,hc,hr⟩ := uniform_real_hilbert_floor (n+1) 0 L α C hL hα hC
  refine ⟨c,hc,fun I _ a b x θ ha hab hgen hx hdim w hw haw hbw ω hω hscale T hT => ?_⟩
  have hb := hr (fun N => (Module.finrank K ((weightedSpace w N).map
        (Ideal.Quotient.mkₐ K I).toLinearMap):ℝ))
    (fun t => (weightedHilbert I ω t:ℝ))
    (fun t => Nat.cast_nonneg _)
    (fun t ht => by
      exact_mod_cast Submodule.finrank_mono
        (weightedSpace_map_le_weightedFunctions I w ω hω L hL hscale t (by linarith)))
    (fun t _ => hh I a b x θ ha hab hgen hx hdim w hw haw hbw t) T hT
  dsimp only [α] at hb
  convert hb using 1
  ring

end QuarticPowerFree

end OAI

import OAI.NumberTheory.PowerFree.PairProjections

namespace OAI

namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators

theorem polynomial_projection_hilbert_le {n m : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K))
    (J : Ideal (MvPolynomial (Fin m) K)) (z : Fin m → MvPolynomial (Fin n) K)
    (D : ℕ) (hz : ∀ i, (z i).totalDegree ≤ D)
    (hker : ∀ p, Ideal.Quotient.mk I (MvPolynomial.aeval z p) = 0 ↔ p ∈ J) (T : ℕ) :
    Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K J).toLinearMap) ≤
      Module.finrank K ((totalSpace (D*T)).map (Ideal.Quotient.mkₐ K I).toLinearMap) := by
  classical
  let := totalSpace_finite (n := n) (K := K) (D*T)
  let f₀ := (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval z)
  let f := Ideal.Quotient.liftₐ J f₀ (fun p hp => (hker p).mpr hp)
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro y hy
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective y
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hker p).mp hy)
  let g := (f.toLinearMap.domRestrict
    ((totalSpace T).map (Ideal.Quotient.mkₐ K J).toLinearMap)).codRestrict
      ((totalSpace (D*T)).map (Ideal.Quotient.mkₐ K I).toLinearMap) (by
        rintro ⟨y,p,hp,rfl⟩
        exact ⟨MvPolynomial.aeval z p,totalSpace_aeval z D hz p T hp,rfl⟩)
  apply LinearMap.finrank_le_finrank_of_injective (f := g)
  intro y z he
  exact Subtype.ext (hf (congrArg Subtype.val he))

theorem polynomial_projection_equation_degree_bound {n h : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (P : Polynomial ℚ)
    (hP : P.natDegree ≤ h)
    (hT : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
        P.eval (T : ℚ)) (z : Fin (h+1) → MvPolynomial (Fin n) K)
    (D : ℕ) (hD : 0 < D) (hz : ∀ i, (z i).totalDegree ≤ D)
    (q : MvPolynomial (Fin (h+1)) K) (hq : q ≠ 0)
    (hker : ∀ p, Ideal.Quotient.mk I (MvPolynomial.aeval z p) = 0 ↔ q ∣ p) :
    (q.totalDegree : ℚ) ≤ (h.factorial : ℚ) * P.coeff h * (D:ℚ)^h := by
  let Q := P.comp (Polynomial.C (D:ℚ)*Polynomial.X)
  have hQT : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace (D*T)).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
        Q.eval (T:ℚ) := by
    obtain ⟨T₀,hT₀⟩ := Filter.eventually_atTop.mp hT
    apply Filter.eventually_atTop.mpr
    refine ⟨T₀,fun T hTT => ?_⟩
    have hT' : T₀ ≤ D*T := hTT.trans (by simpa using Nat.mul_le_mul_right T hD)
    simpa [Q,Polynomial.eval_comp] using hT₀ (D*T) hT'
  have hQ : Q.natDegree ≤ h := by
    have hh := Polynomial.natDegree_comp_le (p := P) (q := Polynomial.C (D:ℚ)*Polynomial.X)
    have hND : (Polynomial.C (D:ℚ)*Polynomial.X).natDegree ≤ 1 := by
      exact le_trans Polynomial.natDegree_mul_le (by simp)
    exact (hh.trans ((Nat.mul_le_mul_left _ hND).trans_eq (Nat.mul_one _))).trans hP
  have hh : ∀ᶠ T : ℕ in Filter.atTop,
      (hypersurfaceHilbertPolynomial h q.totalDegree).eval (T:ℚ) ≤ Q.eval (T:ℚ) := by
    filter_upwards [hQT,Filter.eventually_ge_atTop q.totalDegree] with T hT hqT
    rw [←hT,←hypersurface_hilbert_polynomial q hq T hqT]
    exact_mod_cast polynomial_projection_hilbert_le I (Ideal.span {q}) z D hz
      (fun p => (hker p).trans Ideal.mem_span_singleton.symm) T
  have hc := coeff_le_of_eventually_nat_eval_le
    (hypersurfaceHilbertPolynomial h q.totalDegree) Q h
    (hypersurfaceHilbertPolynomial_degree _ _) hQ hh
  rw [hypersurfaceHilbertPolynomial_coeff,Polynomial.comp_C_mul_X_coeff] at hc
  have hf : (0:ℚ) < h.factorial := by exact_mod_cast Nat.factorial_pos h
  exact (div_le_iff₀ hf).mp hc |>.trans_eq (by ring)

end
section
open MvPolynomial

theorem polynomial_projection_equation_degree_bound_equiv {n h : ℕ}
    {σ K : Type*} [Field K] (e : Fin (h+1) ≃ σ)
    (I : Ideal (MvPolynomial (Fin n) K)) (P : Polynomial ℚ)
    (hP : P.natDegree ≤ h)
    (hT : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
        P.eval (T : ℚ)) (z : σ → MvPolynomial (Fin n) K)
    (D : ℕ) (hD : 0 < D) (hz : ∀ i, (z i).totalDegree ≤ D)
    (q : MvPolynomial σ K) (hq : q ≠ 0)
    (hker : ∀ p, Ideal.Quotient.mk I (MvPolynomial.aeval z p) = 0 ↔ q ∣ p) :
    (q.totalDegree : ℚ) ≤ (h.factorial : ℚ) * P.coeff h * (D:ℚ)^h := by
  let E := MvPolynomial.renameEquiv K e
  let q₀ := E.symm q
  have hq₀ : q₀ ≠ 0 := by
    intro hz
    apply hq
    have hh := congrArg E hz
    simpa only [q₀,E.apply_symm_apply,map_zero] using hh
  have he (p : MvPolynomial (Fin (h+1)) K) :
      MvPolynomial.aeval (z ∘ e) p = MvPolynomial.aeval z (E p) := by
    simp only [E,MvPolynomial.renameEquiv_apply,MvPolynomial.aeval_rename,Function.comp_def]
  have hk₀ (p) : Ideal.Quotient.mk I (MvPolynomial.aeval (z ∘ e) p) = 0 ↔ q₀ ∣ p := by
    rw [he,hker]
    have hh := map_dvd_iff E (a := q₀) (b := p)
    rwa [show E q₀ = q from E.apply_symm_apply q] at hh
  have hh := polynomial_projection_equation_degree_bound I P hP hT (z ∘ e) D hD
    (fun i => hz (e i)) q₀ hq₀ hk₀
  have hdeg : q₀.totalDegree = q.totalDegree := MvPolynomial.totalDegree_renameEquiv e.symm q
  rwa [hdeg] at hh

theorem affine_polynomial_projection_degree_bound {n h : ℕ} {σ K : Type*}
    [Field K] (e : Fin (h+1) ≃ σ)
    (I : Ideal (MvPolynomial (Fin n) K)) (hdim : affineDimension I = h)
    (z : σ → MvPolynomial (Fin n) K) (D : ℕ) (hD : 0 < D)
    (hz : ∀ i, (z i).totalDegree ≤ D)
    (q : MvPolynomial σ K) (hq : q ≠ 0)
    (hker : ∀ p, Ideal.Quotient.mk I (MvPolynomial.aeval z p) = 0 ↔ q ∣ p) :
    (q.totalDegree:ℚ) ≤ affineDegree I * (D:ℚ)^h := by
  have hh := polynomial_projection_equation_degree_bound_equiv e I (coordinateHilbert I)
    hdim.le (coordinateHilbert_eventually I) z D hD hz q hq hker
  simpa only [affineDegree,hdim] using hh

end

theorem left_coordinates_transcendence_selection {d : ℕ} {K A : Type*}
    [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    (a : Fin d → A) (x : A) (hx : Transcendental K x)
    [Algebra.IsAlgebraic (Algebra.adjoin K (insert x (Set.range a))) A] :
    ∃ m : ℕ, ∃ j : Fin m → Fin d,
      AlgebraicIndependent K (Fin.cases x (a ∘ j)) ∧ Function.Injective j ∧
      Algebra.trdeg K A = (m+1 : ℕ) := by
  classical
  have hx' : AlgebraicIndepOn K id {x} := by
    change AlgebraicIndependent K (fun z : ({x} : Set A) => z.val)
    rw [algebraicIndependent_singleton_iff (⟨x,rfl⟩ : ({x} : Set A))]
    exact hx
  obtain ⟨t,hxt,htt,htb⟩ := exists_isTranscendenceBasis_between
    (R := K) (A := A) {x} (insert x (Set.range a)) (by simp) hx'
  have htfin : t.Finite := ((Set.finite_range a).insert x).subset htt
  let : Fintype t := htfin.fintype
  let xt : t := ⟨x,hxt (Set.mem_singleton x)⟩
  have hcard : 0 < Fintype.card t := Fintype.card_pos_iff.mpr ⟨xt⟩
  let m := Fintype.card t - 1
  have hm : m+1 = Fintype.card t := by omega
  let e₀ : Fin (m+1) ≃ t := (finCongr hm).trans (Fintype.equivFin t).symm
  let e : Fin (m+1) ≃ t := (Equiv.swap 0 (e₀.symm xt)).trans e₀
  have he0 : e 0 = xt := by simp [e]
  have heA (i : Fin m) : (e i.succ).val ∈ Set.range a := by
    have hh := htt (e i.succ).property
    rcases hh with hh | hh
    · have heq : e i.succ = xt := Subtype.ext hh
      have : i.succ = 0 := e.injective (heq.trans he0.symm)
      exact (Fin.succ_ne_zero i this).elim
    · exact hh
  choose j hj using heA
  have heval : (fun i : Fin (m+1) => (e i).val) = Fin.cases x (a ∘ j) := by
    funext i
    refine Fin.cases ?_ (fun l => ?_) i
    · exact congrArg Subtype.val he0
    · exact (hj l).symm
  have hi : AlgebraicIndependent K (Fin.cases x (a ∘ j)) := by
    simpa only [Function.comp_def,heval] using htb.1.comp e e.injective
  refine ⟨m,j,hi,?_,?_⟩
  · intro i l hil
    apply Fin.succ_injective
    apply hi.injective
    simp only [Fin.cases_succ,Function.comp_def,hil]
  · rw [←htb.cardinalMk_eq_trdeg,Cardinal.mk_fintype,←hm]

theorem pair_right_isAlgebraic {d : ℕ} {K A : Type*}
    [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    (k : ℕ) (a b : Fin d → A) (x : A) (θ : Fin d → K)
    (ha : ∀ i, a i ≠ 0) (hab : ∀ i, a i ^ k * b i = x - algebraMap K A (θ i))
    (i : Fin d) : IsAlgebraic (Algebra.adjoin K (insert x (Set.range a))) (b i) := by
  let S := Algebra.adjoin K (insert x (Set.range a))
  let ai : S := ⟨a i,Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨i,rfl⟩)⟩
  let xi : S := ⟨x,Algebra.subset_adjoin (Set.mem_insert _ _)⟩
  let p : Polynomial S := Polynomial.C (ai^k) * Polynomial.X -
    Polynomial.C (xi - algebraMap K S (θ i))
  refine ⟨p,?_,?_⟩
  · intro hp
    have hh := congrArg (fun q : Polynomial S => q.coeff 1) hp
    have hh' : ai^k = 0 := by
      simpa only [p,Polynomial.coeff_sub,Polynomial.coeff_C_mul_X,
        Polynomial.coeff_C,ite_eq_right (by decide : (1:ℕ) ≠ 0),
        ite_eq_left rfl,ite_true,sub_zero,Polynomial.coeff_zero] using hh
    have hai : ai ≠ 0 := fun h => ha i (congrArg Subtype.val h)
    exact pow_ne_zero k hai hh'
  · change Polynomial.aeval (b i) p = 0
    simp only [p,map_sub,map_mul,Polynomial.aeval_C,Polynomial.aeval_X]
    change a i ^ k * b i - (x - algebraMap K A (θ i)) = 0
    exact sub_eq_zero.mpr (hab i)

theorem pair_projection_isAlgebraic {d : ℕ} {K A : Type*}
    [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    (k : ℕ) (a b : Fin d → A) (x : A) (θ : Fin d → K)
    (ha : ∀ i, a i ≠ 0) (hab : ∀ i, a i ^ k * b i = x - algebraMap K A (θ i))
    (hgen : Algebra.adjoin K (Set.range a ∪ Set.range b) = ⊤) :
    Algebra.IsAlgebraic (Algebra.adjoin K (insert x (Set.range a))) A := by
  constructor
  intro z
  have hz : IsAlgebraic (Algebra.adjoin K (Set.range a ∪ Set.range b)) z := by
    rw [hgen]
    exact isAlgebraic_algebraMap (R := (⊤ : Subalgebra K A)) ⟨z,trivial⟩
  apply hz.adjoin_of_forall_isAlgebraic
  rintro y ⟨hy,hyn⟩
  rcases hy with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · exact (hyn (Set.mem_insert_of_mem _ ⟨i,rfl⟩)).elim
  · exact pair_right_isAlgebraic k a b x θ ha hab i

open MvPolynomial

theorem principal_evaluation_kernel_reindex {σ τ K A : Type*}
    [Field K] [CommRing A] [Algebra K A] (e : σ ≃ τ)
    (x : σ → A) (y : τ → A) (hxy : ∀ i, y (e i) = x i)
    (q : MvPolynomial σ K)
    (hq : ∀ p, MvPolynomial.aeval x p = 0 ↔ q ∣ p) :
    ∀ p, MvPolynomial.aeval y p = 0 ↔ MvPolynomial.renameEquiv K e q ∣ p := by
  intro p
  let p₀ := (MvPolynomial.renameEquiv K e).symm p
  have he : MvPolynomial.aeval x p₀ = MvPolynomial.aeval y p := by
    have hh : (MvPolynomial.aeval y).comp (MvPolynomial.renameEquiv K e).toAlgHom =
        MvPolynomial.aeval x := by
      apply MvPolynomial.algHom_ext
      intro i
      simpa using hxy i
    have hv := AlgHom.congr_fun hh p₀
    simpa only [AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,
      p₀,AlgEquiv.apply_symm_apply] using hv.symm
  rw [←he,hq]
  exact (map_dvd_iff (MvPolynomial.renameEquiv K e)).symm.trans (by
    rw [show MvPolynomial.renameEquiv K e p₀ = p from AlgEquiv.apply_symm_apply _ _])

def pairProjectionIndex (m : ℕ) : Fin (m+2) ≃ Option (Fin (m+1)) :=
  (Equiv.swap 0 1).trans (finSuccEquiv (m+1))

@[simp] theorem pairProjectionIndex_zero (m : ℕ) : pairProjectionIndex m 0 = some 0 := by
  simp [pairProjectionIndex]

@[simp] theorem pairProjectionIndex_one (m : ℕ) : pairProjectionIndex m 1 = none := by
  simp [pairProjectionIndex]

@[simp] theorem pairProjectionIndex_succ_succ (m : ℕ) (i : Fin m) :
    pairProjectionIndex m i.succ.succ = some i.succ := by
  have hi0 : i.succ.succ ≠ (0 : Fin (m+2)) := Fin.succ_ne_zero _
  have hi1 : i.succ.succ ≠ (1 : Fin (m+2)) := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_succ,Fin.val_one] at this
    omega
  simp [pairProjectionIndex,Equiv.swap_apply_of_ne_of_ne hi0 hi1]

theorem finite_basis_extra_dependent {h : ℕ} {K A : Type*}
    [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    (x : A) (a : Fin (h+1) → A) (htr : Algebra.trdeg K A = (h+1 : ℕ)) :
    ¬ AlgebraicIndependent K (Fin.cases x a) := by
  intro hI
  have hh := hI.lift_cardinalMk_le_trdeg
  simp only [Cardinal.mk_fintype,Fintype.card_fin,Cardinal.lift_natCast,htr] at hh
  have : h+2 ≤ h+1 := by exact_mod_cast hh
  omega

theorem pairProjectionIndex_evaluation {d h : ℕ} {A : Type*}
    (a : Fin d → A) (x : A) (j : Fin h → Fin d) (i : Fin d) (r : Fin (h+2)) :
    (fun o => o.elim x (a ∘ Fin.cases i j)) (pairProjectionIndex h r) =
      Fin.cases (a i) (Fin.cases x (a ∘ j)) r := by
  refine Fin.cases ?_ (fun r' => ?_) r
  · simp only [pairProjectionIndex_zero,Option.elim_some,Function.comp_apply,Fin.cases_zero]
  · refine Fin.cases ?_ (fun r'' => ?_) r'
    · change (fun o => o.elim x (a ∘ Fin.cases i j)) (pairProjectionIndex h 1) = x
      simp only [pairProjectionIndex_one,Option.elim_none]
    · simp only [pairProjectionIndex_succ_succ,Option.elim_some,Function.comp_apply,Fin.cases_succ]

theorem pair_principal_projection_of_extra {d h : ℕ} {K A : Type*}
    [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    (a : Fin d → A) (x : A) (j : Fin h → Fin d) (i : Fin d)
    (hj : AlgebraicIndependent K (Fin.cases x (a ∘ j)))
    (htr : Algebra.trdeg K A = (h+1 : ℕ)) :
    ∃ p : MvPolynomial (Option (Fin (h+1))) K, Irreducible p ∧
      (∀ q, MvPolynomial.aeval (fun o => o.elim x (a ∘ Fin.cases i j)) q = 0 ↔ p ∣ q) := by
  have hdep := finite_basis_extra_dependent (K := K) (h := h) (a i) (Fin.cases x (a ∘ j)) htr
  generalize hy : (Fin.cases x (a ∘ j) : Fin (h+1) → A) = y at hj hdep
  obtain ⟨q,hq,_,hkq⟩ := exists_principal_relation_of_dependent (K := K) (h := h+1) (a i) y hj hdep
  refine ⟨MvPolynomial.renameEquiv K (pairProjectionIndex h) q, ?_, ?_⟩
  · exact (MulEquiv.irreducible_iff (MvPolynomial.renameEquiv K (pairProjectionIndex h)).toMulEquiv).mpr hq
  · apply principal_evaluation_kernel_reindex (pairProjectionIndex h) _ _ _ q hkq
    intro r
    rw [←hy]
    exact pairProjectionIndex_evaluation a x j i r

theorem pair_principal_projection_of_basis {d h : ℕ} {K A : Type*}
    [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    (a : Fin d → A) (x : A) (j : Fin h → Fin d)
    (hj : AlgebraicIndependent K (Fin.cases x (a ∘ j)))
    (hjinj : Function.Injective j) (htr : Algebra.trdeg K A = (h+1 : ℕ))
    (hhd : h+1 ≤ d) :
    ∃ j : Fin (h+1) → Fin d, Function.Injective j ∧
      ∃ p : MvPolynomial (Option (Fin (h+1))) K, Irreducible p ∧
        (∀ q, MvPolynomial.aeval (fun o => o.elim x (a ∘ j)) q = 0 ↔ p ∣ q) := by
  classical
  have hex : ∃ i : Fin d, i ∉ Set.range j := by
    by_contra hh
    push Not at hh
    have hsur : Function.Surjective j := hh
    have hc := Fintype.card_le_of_surjective _ hsur
    simp only [Fintype.card_fin] at hc
    omega
  obtain ⟨i,hi⟩ := hex
  let js : Fin (h+1) → Fin d := Fin.cases i j
  have hjs : Function.Injective js := by
    intro r s hrs
    induction r using Fin.cases with
    | zero =>
      induction s using Fin.cases with
      | zero => rfl
      | succ s => exact (hi ⟨s,hrs.symm⟩).elim
    | succ r =>
      induction s using Fin.cases with
      | zero => exact (hi ⟨r,hrs⟩).elim
      | succ s => exact congrArg Fin.succ (hjinj hrs)
  obtain ⟨p,hp,hkp⟩ := pair_principal_projection_of_extra a x j i hj htr
  exact ⟨js,hjs,p,hp,hkp⟩

theorem pair_principal_projection_selection {d : ℕ} {K A : Type*}
    [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    (k : ℕ) (a b : Fin d → A) (x : A) (θ : Fin d → K)
    (ha : ∀ i, a i ≠ 0) (hab : ∀ i, a i ^ k * b i = x - algebraMap K A (θ i))
    (hgen : Algebra.adjoin K (Set.range a ∪ Set.range b) = ⊤)
    (hx : Transcendental K x) (hdim : Algebra.trdeg K A ≤ d) :
    ∃ h : ℕ, ∃ j : Fin (h+1) → Fin d, Function.Injective j ∧
      Algebra.trdeg K A = (h+1 : ℕ) ∧
      ∃ p : MvPolynomial (Option (Fin (h+1))) K, Irreducible p ∧
        (∀ q, MvPolynomial.aeval (fun o => o.elim x (a ∘ j)) q = 0 ↔ p ∣ q) := by
  classical
  let := pair_projection_isAlgebraic k a b x θ ha hab hgen
  obtain ⟨h,j,hj,hjinj,htr⟩ := left_coordinates_transcendence_selection a x hx
  have hhd : h+1 ≤ d := by exact_mod_cast (htr ▸ hdim)
  obtain ⟨js,hjs,p,hp,hkp⟩ := pair_principal_projection_of_basis a x j hj hjinj htr hhd
  exact ⟨h, js, hjs, htr, p, hp, hkp⟩

end QuarticPowerFree

end OAI

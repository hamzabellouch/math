import OAI.NumberTheory.PowerFree.Sieve

namespace OAI

namespace QuarticPowerFree
open MvPolynomial Finsupp MonomialOrder
open scoped MonomialOrder

variable {σ K : Type*} [Field K]

def IdealNormal (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K))
    (d : σ →₀ ℕ) : Prop :=
  ∀ p ∈ I, p ≠ 0 → ¬ m.degree p ≤ d

theorem ideal_normal_form (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K))
    (p : MvPolynomial σ K) :
    ∃ r : MvPolynomial σ K, p-r ∈ I ∧
      (∀ d ∈ r.support, IdealNormal m I d) ∧ m.degree r ≼[m] m.degree p := by
  classical
  let b : {q : MvPolynomial σ K // q ∈ I ∧ q ≠ 0} → MvPolynomial σ K := Subtype.val
  have hb : ∀ i, IsUnit (m.leadingCoeff (b i)) := by
    intro i
    apply isUnit_iff_ne_zero.mpr
    exact m.leadingCoeff_ne_zero_iff.mpr i.property.2
  obtain ⟨g, r, hpr, hdeg, hr⟩ := m.div hb p
  have hg : Finsupp.linearCombination _ b g ∈ I := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    apply Ideal.sum_mem
    intro i _
    exact Ideal.mul_mem_left _ _ i.property.1
  refine ⟨r, ?_, ?_, ?_⟩
  · rw [hpr, add_sub_cancel_right]; exact hg
  · intro d hd q hq hq0
    exact hr d hd ⟨q, hq, hq0⟩
  · have hlin : m.degree (Finsupp.linearCombination _ b g) ≼[m] m.degree p := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
      apply m.degree_sum_le.trans
      apply Finset.sup_le
      intro i _
      simpa [smul_eq_mul, mul_comm] using hdeg i
    have heq : r = p - Finsupp.linearCombination _ b g := by rw [hpr]; ring
    rw [heq]
    exact (m.degree_sub_le).trans (max_le le_rfl hlin)

theorem ideal_normal_injective (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K))
    (p : MvPolynomial σ K) (hp : ∀ d ∈ p.support, IdealNormal m I d)
    (hI : p ∈ I) : p = 0 := by
  by_contra hp0
  exact hp _ (m.degree_mem_support hp0) p hI hp0 le_rfl

theorem ideal_normal_quotient_bijective (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ K)) :
    Function.Bijective
      (((Ideal.Quotient.mkₐ K I).toLinearMap).comp
        (restrictSupport K {d : σ →₀ ℕ | IdealNormal m I d}).subtype) := by
  classical
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro p hp
    apply Subtype.ext
    exact ideal_normal_injective m I p.val (fun d hd => p.property hd)
      (Ideal.Quotient.eq_zero_iff_mem.mp hp)
  · intro y
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨r, hr, hn, _⟩ := ideal_normal_form m I p
    refine ⟨⟨r, fun d hd => hn d hd⟩, ?_⟩
    change (Ideal.Quotient.mk I) r = (Ideal.Quotient.mk I) p
    apply Ideal.Quotient.eq.mpr
    simpa only [neg_sub] using I.neg_mem hr

noncomputable def idealNormalEquiv (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ K)) :
    restrictSupport K {d : σ →₀ ℕ | IdealNormal m I d} ≃ₗ[K]
      MvPolynomial σ K ⧸ I :=
  LinearEquiv.ofBijective
    (((Ideal.Quotient.mkₐ K I).toLinearMap).comp
      (restrictSupport K {d : σ →₀ ℕ | IdealNormal m I d}).subtype)
    (ideal_normal_quotient_bijective m I)

noncomputable def idealNormalBasis (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ K)) :
    Module.Basis {d : σ →₀ ℕ // IdealNormal m I d} K (MvPolynomial σ K ⧸ I) :=
  (basisRestrictSupport K {d : σ →₀ ℕ | IdealNormal m I d}).map (idealNormalEquiv m I)

theorem ideal_normal_finite_obstructions [Finite σ] (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ K)) :
    ∃ s : Finset (σ →₀ ℕ),
      (∀ d ∈ s, ∃ p ∈ I, p ≠ 0 ∧ m.degree p = d) ∧
      ∀ d, IdealNormal m I d ↔ ∀ a ∈ s, ¬ a ≤ d := by
  classical
  let D : Set (σ →₀ ℕ) := {d | ∃ p ∈ I, p ≠ 0 ∧ m.degree p = d}
  have hf : {a | Minimal (· ∈ D) a}.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain _)
  refine ⟨hf.toFinset, ?_, ?_⟩
  · intro d hd
    exact (hf.mem_toFinset.mp hd).1
  · intro d
    constructor
    · intro hn a ha had
      obtain ⟨p, hp, hp0, he⟩ := (hf.mem_toFinset.mp ha).1
      exact hn p hp hp0 (he ▸ had)
    · intro hn p hp hp0 hpd
      have hpD : m.degree p ∈ D := ⟨p, hp, hp0, rfl⟩
      obtain ⟨a, hap, ha⟩ := (show D.IsPWO from Set.isPWO_of_wellQuasiOrderedLE D).exists_le_minimal hpD
      exact hn a (hf.mem_toFinset.mpr ha) (hap.trans hpd)

noncomputable def totalSpace (T : ℕ) : Submodule K (MvPolynomial σ K) :=
  restrictSupport K {d | d.degree ≤ T}

@[simp] theorem mem_totalSpace {T : ℕ} {p : MvPolynomial σ K} :
    p ∈ totalSpace T ↔ p.totalDegree ≤ T := by
  simp only [totalSpace, mem_restrictSupport_iff, totalDegree, Finset.sup_le_iff]
  rfl

noncomputable def normalTotalSpace (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K))
    (T : ℕ) : Submodule K (MvPolynomial σ K) :=
  restrictSupport K {d | IdealNormal m I d ∧ d.degree ≤ T}

theorem normalTotalSpace_le (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K))
    (T : ℕ) : normalTotalSpace m I T ≤ totalSpace T := by
  intro p hp d hd
  exact (hp hd).2

theorem totalSpace_image_normal [LinearOrder σ] [WellFoundedGT σ]
    (I : Ideal (MvPolynomial σ K)) (T : ℕ) :
    (totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap =
      (normalTotalSpace degLex I T).map (Ideal.Quotient.mkₐ K I).toLinearMap := by
  apply le_antisymm
  · rintro y ⟨p, hp, rfl⟩
    obtain ⟨r, hr, hn, hd⟩ := ideal_normal_form degLex I p
    refine ⟨r, ?_, ?_⟩
    · intro d hdr
      refine ⟨hn d hdr, ?_⟩
      exact (le_totalDegree hdr).trans
        ((degLex_totalDegree_monotone hd).trans (mem_totalSpace.mp hp))
    · apply Ideal.Quotient.eq.mpr
      simpa only [neg_sub] using I.neg_mem hr
  · exact Submodule.map_mono (normalTotalSpace_le _ _ _)

theorem coordinate_hilbert_count [LinearOrder σ] [WellFoundedGT σ]
    (I : Ideal (MvPolynomial σ K)) (T : ℕ) :
    Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) =
      Nat.card {d : σ →₀ ℕ // IdealNormal degLex I d ∧ d.degree ≤ T} := by
  rw [totalSpace_image_normal]
  let M := normalTotalSpace degLex I T
  let f := (Ideal.Quotient.mkₐ K I).toLinearMap.domRestrict M
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro p hp
    apply Subtype.ext
    exact ideal_normal_injective degLex I p.val (fun d hd => (p.property hd).1)
      (Ideal.Quotient.eq_zero_iff_mem.mp hp)
  have heq : LinearMap.range f = M.map (Ideal.Quotient.mkₐ K I).toLinearMap :=
    LinearMap.range_domRestrict _ _
  rw [← heq, LinearMap.finrank_range_of_inj hf]
  exact Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)

open scoped BigOperators

noncomputable def simplexTuple (h N : ℕ) : Finset (Fin h → ℕ) :=
  (Finset.range (N+1)).biUnion (Finset.Nat.antidiagonalTuple h)

@[simp] theorem mem_simplexTuple {h N : ℕ} (x : Fin h → ℕ) :
    x ∈ simplexTuple h N ↔ ∑ i, x i ≤ N := by
  classical
  simp only [simplexTuple, Finset.mem_biUnion, Finset.mem_range,
    Finset.Nat.mem_antidiagonalTuple]
  constructor
  · rintro ⟨n, hn, he⟩; omega
  · intro hx; exact ⟨_, by omega, rfl⟩

private theorem card_antidiagonalTuple (h N : ℕ) :
    (Finset.Nat.antidiagonalTuple h N).card = h.multichoose N := by
  classical
  have hc := Finset.card_finsuppAntidiag_nat_eq_multichoose
    (s := (Finset.univ : Finset (Fin h))) N
  rw [Finset.card_univ, Fintype.card_fin] at hc
  rw [← hc]
  apply Finset.card_bij (fun x _ => Finsupp.equivFunOnFinite.symm x)
  · intro x hx
    rw [Finset.mem_finsuppAntidiag']
    exact ⟨by simpa [Finsupp.sum_fintype] using Finset.Nat.mem_antidiagonalTuple.mp hx,
      Finset.subset_univ _⟩
  · intro x _ y _ he
    exact Finsupp.equivFunOnFinite.symm.injective he
  · intro x hx
    refine ⟨Finsupp.equivFunOnFinite x, ?_, by simp⟩
    rw [Finset.Nat.mem_antidiagonalTuple]
    simpa [Finsupp.sum_fintype] using (Finset.mem_finsuppAntidiag'.mp hx).1

theorem card_simplexTuple (h N : ℕ) :
    (simplexTuple h N).card = (N+h).choose h := by
  classical
  rw [simplexTuple, Finset.card_biUnion]
  · simp_rw [card_antidiagonalTuple]
    exact Nat.sum_range_multichoose N h
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x hi hj
    exact hij ((Finset.Nat.mem_antidiagonalTuple.mp hi).symm.trans
      (Finset.Nat.mem_antidiagonalTuple.mp hj))

noncomputable def simplexExponents (n T : ℕ) : Finset (Fin n →₀ ℕ) :=
  (simplexTuple n T).map Finsupp.equivFunOnFinite.symm.toEmbedding

@[simp] theorem mem_simplexExponents {n T : ℕ} (d : Fin n →₀ ℕ) :
    d ∈ simplexExponents n T ↔ d.degree ≤ T := by
  classical
  simp only [simplexExponents, Finset.mem_map_equiv, mem_simplexTuple]
  change (∑ i, d i) ≤ T ↔ (d.sum fun _ e => e) ≤ T
  rw [Finsupp.sum_fintype]
  intro i; rfl

@[simp] theorem card_simplexExponents (n T : ℕ) :
    (simplexExponents n T).card = (T+n).choose n := by
  rw [simplexExponents, Finset.card_map, card_simplexTuple]

noncomputable def normalExponents {n : ℕ} (s : Finset (Fin n →₀ ℕ)) (T : ℕ) :
    Finset (Fin n →₀ ℕ) := by
  classical
  exact (simplexExponents n T).filter (fun d => ∀ a ∈ s, ¬ a ≤ d)

@[simp] theorem mem_normalExponents {n : ℕ} (s : Finset (Fin n →₀ ℕ)) (T : ℕ)
    (d : Fin n →₀ ℕ) :
    d ∈ normalExponents s T ↔ d.degree ≤ T ∧ ∀ a ∈ s, ¬ a ≤ d := by
  classical
  simp [normalExponents]

@[simp] theorem normalExponents_empty (n T : ℕ) :
    normalExponents (∅ : Finset (Fin n →₀ ℕ)) T = simplexExponents n T := by
  classical
  ext; simp

noncomputable def colonMonomials {n : ℕ} (a : Fin n →₀ ℕ)
    (s : Finset (Fin n →₀ ℕ)) : Finset (Fin n →₀ ℕ) := by
  classical
  exact s.image (fun b => b-a)

theorem colonMonomials_card_le {n : ℕ} (a : Fin n →₀ ℕ)
    (s : Finset (Fin n →₀ ℕ)) : (colonMonomials a s).card ≤ s.card := by
  classical
  exact Finset.card_image_le

theorem finsupp_tsub_le_iff {n : ℕ} (a b d : Fin n →₀ ℕ) :
    b-a ≤ d ↔ b ≤ a+d := by
  simp only [Finsupp.le_def, Finsupp.tsub_apply, Finsupp.add_apply]
  constructor
  · intro h i; have := h i; omega
  · intro h i; have := h i; omega

theorem normalExponents_card_insert {n : ℕ} (a : Fin n →₀ ℕ)
    (s : Finset (Fin n →₀ ℕ)) (T : ℕ) (ha : a.degree ≤ T) :
    (normalExponents (insert a s) T).card +
      (normalExponents (colonMonomials a s) (T-a.degree)).card =
        (normalExponents s T).card := by
  classical
  have hs : normalExponents (insert a s) T =
      (normalExponents s T).filter (fun d => ¬ a ≤ d) := by
    ext d; simp [and_left_comm, and_comm]
  have hc : ((normalExponents s T).filter (a ≤ ·)).card =
      (normalExponents (colonMonomials a s) (T-a.degree)).card := by
    symm
    apply Finset.card_bij (fun d _ => a+d)
    · intro d hd
      obtain ⟨hdT, hdS⟩ := (mem_normalExponents _ _ d).mp hd
      apply Finset.mem_filter.mpr
      refine ⟨(mem_normalExponents _ _ _).mpr ⟨?_, ?_⟩, le_add_right le_rfl⟩
      · rw [map_add]; omega
      · intro b hb hbad
        exact hdS (b-a) (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
          ((finsupp_tsub_le_iff a b d).mpr hbad)
    · intro d _ e _ h; exact add_left_cancel h
    · intro d hd
      obtain ⟨hdS, had⟩ := Finset.mem_filter.mp hd
      obtain ⟨hdT, hdN⟩ := (mem_normalExponents _ _ d).mp hdS
      refine ⟨d-a, (mem_normalExponents _ _ _).mpr ⟨?_, ?_⟩,
        add_tsub_cancel_of_le had⟩
      · have he := congrArg Finsupp.degree (add_tsub_cancel_of_le had)
        simp only [map_add] at he
        omega
      · intro b hb hbd
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
        apply hdN c hc
        have h := (finsupp_tsub_le_iff a c (d-a)).mp hbd
        simpa only [add_tsub_cancel_of_le had] using h
  rw [hs, ← hc, add_comm]
  exact Finset.card_filter_add_card_filter_not _

theorem normalExponents_eventually_polynomial {n : ℕ} (s : Finset (Fin n →₀ ℕ)) :
    ∃ P : Polynomial ℚ, P.natDegree ≤ n ∧ ∃ T₀ : ℕ, ∀ T ≥ T₀,
      ((normalExponents s T).card : ℚ) = P.eval (T : ℚ) := by
  classical
  suffices H : ∀ N, ∀ s : Finset (Fin n →₀ ℕ), s.card = N →
      ∃ P : Polynomial ℚ, P.natDegree ≤ n ∧ ∃ T₀ : ℕ, ∀ T ≥ T₀,
        ((normalExponents s T).card : ℚ) = P.eval (T : ℚ) by
    exact H s.card s rfl
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro s hs
    by_cases he : s = ∅
    · subst s
      refine ⟨Polynomial.preHilbertPoly ℚ n 0,
        (Polynomial.natDegree_preHilbertPoly _ _ _).le, 0, ?_⟩
      intro T _
      rw [normalExponents_empty, card_simplexExponents,
        Polynomial.preHilbertPoly_eq_choose_add_sub _ _ (Nat.zero_le _)]
      simp
    · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr he
      let s' := s.erase a
      have ht : s'.card < N := by rw [← hs]; exact Finset.card_erase_lt_of_mem ha
      obtain ⟨P, hP, TP, hPT⟩ := ih s'.card ht s' rfl
      obtain ⟨Q, hQ, TQ, hQT⟩ := ih (colonMonomials a s').card
        ((colonMonomials_card_le _ _).trans_lt ht) _ rfl
      refine ⟨P - Q.comp (Polynomial.X - Polynomial.C (a.degree : ℚ)), ?_,
        max TP (TQ+a.degree), ?_⟩
      · apply (Polynomial.natDegree_sub_le _ _).trans
        apply max_le hP
        rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_sub_C, mul_one]
        exact hQ
      · intro T hT
        have hTP : TP ≤ T := (le_max_left _ _).trans hT
        have hTQ : TQ+a.degree ≤ T := (le_max_right _ _).trans hT
        have haT : a.degree ≤ T := by omega
        have hh := normalExponents_card_insert a s' T haT
        rw [show insert a s' = s from Finset.insert_erase ha] at hh
        have hhQ : ((normalExponents s T).card : ℚ) +
            ((normalExponents (colonMonomials a s') (T-a.degree)).card : ℚ) =
              ((normalExponents s' T).card : ℚ) := by exact_mod_cast hh
        rw [hPT T hTP, hQT (T-a.degree) (by omega)] at hhQ
        rw [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C]
        rw [Nat.cast_sub haT] at hhQ
        linarith

theorem coordinate_hilbert_eventually_polynomial {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) :
    ∃ P : Polynomial ℚ, P.natDegree ≤ n ∧ ∃ T₀ : ℕ, ∀ T ≥ T₀,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
        P.eval (T : ℚ) := by
  classical
  obtain ⟨s, _, hs⟩ := ideal_normal_finite_obstructions degLex I
  have hc (T : ℕ) :
      Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) =
        (normalExponents s T).card := by
    rw [coordinate_hilbert_count, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro d
    simp only [mem_normalExponents, hs, and_comm]
  obtain ⟨P, hP, T₀, hT⟩ := normalExponents_eventually_polynomial s
  refine ⟨P, hP, T₀, ?_⟩
  intro T h
  rw [hc]
  exact hT T h

theorem idealNormal_span_singleton (m : MonomialOrder σ)
    (p : MvPolynomial σ K) (hp : p ≠ 0) (d : σ →₀ ℕ) :
    IdealNormal m (Ideal.span {p}) d ↔ ¬ m.degree p ≤ d := by
  constructor
  · intro h
    exact h p (Ideal.subset_span (Set.mem_singleton p)) hp
  · intro h q hq hq0 hqd
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hq
    have hr : r ≠ 0 := by intro he; simp [he] at hq0
    rw [m.degree_mul hp hr] at hqd
    exact h ((_root_.le_add_right le_rfl).trans hqd)

theorem hypersurface_hilbert_count {n : ℕ} (p : MvPolynomial (Fin n) K)
    (hp : p ≠ 0) (T : ℕ) (hT : p.totalDegree ≤ T) :
    Module.finrank K ((totalSpace T).map
      (Ideal.Quotient.mkₐ K (Ideal.span {p})).toLinearMap) +
        (T-p.totalDegree+n).choose n = (T+n).choose n := by
  classical
  have hc : Module.finrank K ((totalSpace T).map
      (Ideal.Quotient.mkₐ K (Ideal.span {p})).toLinearMap) =
      (normalExponents {degLex.degree p} T).card := by
    rw [coordinate_hilbert_count, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro d
    simp only [mem_normalExponents, idealNormal_span_singleton degLex p hp,
      Finset.mem_singleton, forall_eq, and_comm]
  rw [hc]
  have hh := normalExponents_card_insert (degLex.degree p) ∅ T
    (by simpa only [degree_degLexDegree] using hT)
  simpa [colonMonomials, degree_degLexDegree] using hh

theorem binomial_difference_sum (n e T : ℕ) (he : e ≤ T) :
    (T-e+(n+1)).choose (n+1) +
      ∑ j ∈ Finset.range e, (T-j+n).choose n =
        (T+(n+1)).choose (n+1) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Finset.sum_range_succ]
    have hi := ih (by omega)
    have hE : T-e+n = (T-(e+1)+(n+1)) := by omega
    have hE' : T-e+(n+1) = (T-e+n)+1 := by omega
    have hb := Nat.choose_succ_succ (T-e+n) n
    change (T-e+n+1).choose (n+1) = (T-e+n).choose n + (T-e+n).choose (n+1) at hb
    rw [← hE'] at hb
    rw [← hE]
    omega

noncomputable def hypersurfaceHilbertPolynomial (n e : ℕ) : Polynomial ℚ :=
  ∑ j ∈ Finset.range e, Polynomial.preHilbertPoly ℚ n j

theorem hypersurfaceHilbertPolynomial_coeff (n e : ℕ) :
    (hypersurfaceHilbertPolynomial n e).coeff n = (e : ℚ)/(n.factorial : ℚ) := by
  simp [hypersurfaceHilbertPolynomial, Polynomial.coeff_preHilbertPoly_self, div_eq_mul_inv]

theorem hypersurfaceHilbertPolynomial_degree (n e : ℕ) :
    (hypersurfaceHilbertPolynomial n e).natDegree ≤ n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_preHilbertPoly _ _ _).le

theorem hypersurface_hilbert_polynomial {n : ℕ} (p : MvPolynomial (Fin (n+1)) K)
    (hp : p ≠ 0) (T : ℕ) (hT : p.totalDegree ≤ T) :
    (Module.finrank K ((totalSpace T).map
      (Ideal.Quotient.mkₐ K (Ideal.span {p})).toLinearMap) : ℚ) =
        (hypersurfaceHilbertPolynomial n p.totalDegree).eval (T : ℚ) := by
  have hh := hypersurface_hilbert_count p hp T hT
  have hb := binomial_difference_sum n p.totalDegree T hT
  have he : Module.finrank K ((totalSpace T).map
      (Ideal.Quotient.mkₐ K (Ideal.span {p})).toLinearMap) =
        ∑ j ∈ Finset.range p.totalDegree, (T-j+n).choose n := by omega
  rw [he, Nat.cast_sum]
  simp only [hypersurfaceHilbertPolynomial, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Polynomial.preHilbertPoly_eq_choose_add_sub _ _
    (Nat.le_add_right_of_le ((Finset.mem_range.mp hj).le.trans hT)),
    Nat.sub_add_comm ((Finset.mem_range.mp hj).le.trans hT)]

end QuarticPowerFree

end OAI

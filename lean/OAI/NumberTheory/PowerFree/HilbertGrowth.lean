import OAI.NumberTheory.PowerFree.NormalMonomials

namespace OAI

namespace QuarticPowerFree

section
open Polynomial Filter
open scoped Topology

theorem leadingCoeff_nonneg_of_eventually_nat_eval_nonneg (P : Polynomial ℚ)
    (hP : ∀ᶠ T : ℕ in atTop, 0 ≤ P.eval (T : ℚ)) : 0 ≤ P.leadingCoeff := by
  by_cases hd : P.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero hd] at hP ⊢
    simpa only [eval_C, leadingCoeff_C, eventually_const] using hP
  · by_contra hl
    have ht := (P.tendsto_atBot_of_leadingCoeff_nonpos
      (natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hd)) (le_of_not_ge hl)).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun T : ℕ => (T : ℚ)) atTop atTop)
    have hn := ht.eventually_lt_atBot 0
    obtain ⟨T, hT, hT'⟩ := (hP.and hn).exists
    exact (not_lt_of_ge hT) hT'

theorem coeff_le_of_eventually_nat_eval_le (P Q : Polynomial ℚ) (h : ℕ)
    (hP : P.natDegree ≤ h) (hQ : Q.natDegree ≤ h)
    (hle : ∀ᶠ T : ℕ in atTop, P.eval (T : ℚ) ≤ Q.eval (T : ℚ)) :
    P.coeff h ≤ Q.coeff h := by
  have hn : 0 ≤ (Q-P).leadingCoeff :=
    leadingCoeff_nonneg_of_eventually_nat_eval_nonneg (Q-P)
      (hle.mono (fun T hT => by simpa only [eval_sub, sub_nonneg] using hT))
  have hd : (Q-P).natDegree ≤ h := (natDegree_sub_le _ _).trans (max_le hQ hP)
  have hc : 0 ≤ (Q-P).coeff h := by
    rcases hd.eq_or_lt with he | he
    · simpa only [← he, coeff_natDegree] using hn
    · rw [coeff_eq_zero_of_natDegree_lt he]
  simpa only [coeff_sub, sub_nonneg] using hc

theorem natDegree_le_of_eventually_nat_eval_bounds (P Q : Polynomial ℚ)
    (hP : ∀ᶠ T : ℕ in atTop, 0 ≤ P.eval (T : ℚ))
    (hle : ∀ᶠ T : ℕ in atTop, P.eval (T : ℚ) ≤ Q.eval (T : ℚ)) :
    P.natDegree ≤ Q.natDegree := by
  by_contra hh
  have hdeg : Q.natDegree < P.natDegree := lt_of_not_ge hh
  have hP0 : P ≠ 0 := by intro he; simp [he] at hdeg
  have hl : 0 < P.leadingCoeff := lt_of_le_of_ne
    (leadingCoeff_nonneg_of_eventually_nat_eval_nonneg P hP)
    (Ne.symm (leadingCoeff_ne_zero.mpr hP0))
  have hm := leadingCoeff_nonneg_of_eventually_nat_eval_nonneg (Q-P)
    (hle.mono (fun T hT => by simpa only [eval_sub, sub_nonneg] using hT))
  rw [leadingCoeff_sub_of_degree_lt' (degree_lt_degree hdeg)] at hm
  linarith

end

open MvPolynomial Finsupp MonomialOrder
open scoped MonomialOrder BigOperators

def FreeNormalFace {n : ℕ} (s : Finset (Fin n →₀ ℕ)) (J : Finset (Fin n)) : Prop :=
  ∀ a ∈ s, ¬ a.support ⊆ J

theorem normal_of_free_face {n : ℕ} {s : Finset (Fin n →₀ ℕ)}
    {J : Finset (Fin n)} (hJ : FreeNormalFace s J)
    (d : Fin n →₀ ℕ) (hd : d.support ⊆ J) : ∀ a ∈ s, ¬ a ≤ d := by
  intro a ha had
  apply hJ a ha
  intro i hi
  apply hd
  apply Finsupp.mem_support_iff.mpr
  have hai : a i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have hh := had i
  omega

theorem large_coordinates_free {n : ℕ} (s : Finset (Fin n →₀ ℕ))
    (B : ℕ) (hB : ∀ a ∈ s, a.degree < B)
    (d : Fin n →₀ ℕ) (hd : ∀ a ∈ s, ¬ a ≤ d) :
    FreeNormalFace s (Finset.univ.filter (fun i => B ≤ d i)) := by
  classical
  intro a ha hsub
  apply hd a ha
  intro i
  by_cases hi : i ∈ a.support
  · have hh : B ≤ d i := (Finset.mem_filter.mp (hsub hi)).2
    exact ((Finsupp.le_degree i a).trans (hB a ha).le).trans hh
  · simpa only [Finsupp.notMem_support_iff.mp hi] using Nat.zero_le (d i)

theorem free_face_algebraicIndependent {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K))
    (s : Finset (Fin n →₀ ℕ))
    (hs : ∀ d, IdealNormal degLex I d ↔ ∀ a ∈ s, ¬ a ≤ d)
    (J : Finset (Fin n)) (hJ : FreeNormalFace s J) :
    AlgebraicIndependent K (fun j : J => Ideal.Quotient.mk I (X j.val)) := by
  classical
  let f := (Ideal.Quotient.mkₐ K I).comp (rename (fun j : J => j.val))
  have he : MvPolynomial.aeval (fun j : J => Ideal.Quotient.mk I (X j.val)) = f := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [f]
  rw [algebraicIndependent_iff_injective_aeval, he]
  intro p q hpq
  apply sub_eq_zero.mp
  apply (rename_injective (fun j : J => j.val) Subtype.val_injective)
  rw [map_zero]
  apply ideal_normal_injective degLex I
  · intro d hd
    apply (hs d).mpr
    apply normal_of_free_face hJ
    intro i hi
    have hv := support_subset_vars_of_mem_support hd hi
    have hr := vars_rename (fun j : J => j.val) (p-q) hv
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hr
    exact j.property
  · apply Ideal.Quotient.eq_zero_iff_mem.mp
    change f (p-q) = 0
    rw [map_sub, hpq, sub_self]

noncomputable def partialCoordinateBox {n : ℕ} (B T : ℕ) (J : Finset (Fin n)) :
    Finset (Fin n → ℕ) := by
  classical
  exact Fintype.piFinset (fun i => Finset.range (if i ∈ J then T+1 else B))

theorem card_partialCoordinateBox_le {n : ℕ} (B T h : ℕ) (hB : 1 ≤ B)
    (J : Finset (Fin n)) (hJ : J.card ≤ h) :
    (partialCoordinateBox B T J).card ≤ B^n * (T+1)^h := by
  classical
  rw [partialCoordinateBox, Fintype.card_piFinset]
  simp only [Finset.card_range]
  rw [Finset.prod_ite]
  have he : (Finset.univ.filter (fun i : Fin n => i ∈ J)) = J := by ext; simp
  rw [he]
  simp only [Finset.prod_const]
  have hc : (Finset.univ.filter (fun i : Fin n => i ∉ J)).card ≤ n := by
    exact (Finset.card_filter_le _ _).trans (by simp)
  calc
    (T+1)^J.card * B^(Finset.univ.filter (fun i : Fin n => i ∉ J)).card ≤
        (T+1)^h * B^n := Nat.mul_le_mul
          (Nat.pow_le_pow_right (by omega) hJ) (Nat.pow_le_pow_right hB hc)
    _ = B^n * (T+1)^h := Nat.mul_comm _ _

theorem normalExponents_card_growth {n : ℕ} (s : Finset (Fin n →₀ ℕ))
    (h : ℕ) (hh : ∀ J, FreeNormalFace s J → J.card ≤ h) (T : ℕ) :
    (normalExponents s T).card ≤
      (2^n * (s.sup Finsupp.degree + 1)^n) * (T+1)^h := by
  classical
  let B := s.sup Finsupp.degree + 1
  let faces := (Finset.univ : Finset (Fin n)).powerset.filter (fun J => J.card ≤ h)
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hBs : ∀ a ∈ s, a.degree < B := by
    intro a ha
    exact Nat.lt_succ_of_le (Finset.le_sup (f := Finsupp.degree) ha)
  have hc : (normalExponents s T).image (fun d : Fin n →₀ ℕ => (d : Fin n → ℕ)) ⊆
      faces.biUnion (partialCoordinateBox B T) := by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
    have ha' := mem_normalExponents s T a |>.mp ha
    let J := Finset.univ.filter (fun i => B ≤ a i)
    refine Finset.mem_biUnion.mpr ⟨J, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
        hh J (large_coordinates_free s B hBs a ha'.2)⟩
    · rw [partialCoordinateBox, Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_range]
      by_cases hi : i ∈ J
      · rw [ite_eq_left hi]
        exact Nat.lt_succ_of_le ((Finsupp.le_degree i a).trans ha'.1)
      · rw [ite_eq_right hi]
        have hh : ¬ B ≤ a i := by simpa [J] using hi
        omega
  have hf : faces.card ≤ 2^n := by
    exact (Finset.card_filter_le _ _).trans (by simp)
  calc
    (normalExponents s T).card =
      ((normalExponents s T).image (fun d : Fin n →₀ ℕ => (d : Fin n → ℕ))).card :=
        (Finset.card_image_of_injective _ (fun p q h => Finsupp.ext (fun i => congrFun h i))).symm
    _ ≤ (faces.biUnion (partialCoordinateBox B T)).card := Finset.card_le_card hc
    _ ≤ ∑ J ∈ faces, (partialCoordinateBox B T J).card := Finset.card_biUnion_le
    _ ≤ faces.card * (B^n * (T+1)^h) := by
      simpa only [nsmul_eq_mul, Nat.cast_id] using Finset.sum_le_card_nsmul faces
        (fun J => (partialCoordinateBox B T J).card) (B^n * (T+1)^h)
        (fun J hJ => card_partialCoordinateBox_le B T h hB J (Finset.mem_filter.mp hJ).2)
    _ ≤ 2^n * (B^n * (T+1)^h) := Nat.mul_le_mul_right _ hf
    _ = (2^n * (s.sup Finsupp.degree+1)^n) * (T+1)^h := by rw [Nat.mul_assoc]

theorem totalSpace_finite {n : ℕ} {K : Type*} [Field K] (T : ℕ) :
    Module.Finite K (totalSpace (σ := Fin n) (K := K) T) := by
  classical
  let e : {d : Fin n →₀ ℕ // d.degree ≤ T} ≃ {d // d ∈ simplexExponents n T} :=
    Equiv.subtypeEquivRight (fun d => (mem_simplexExponents d).symm)
  let : Finite {d : Fin n →₀ ℕ | d.degree ≤ T} :=
    Finite.of_equiv {d // d ∈ simplexExponents n T} e.symm
  exact Module.Finite.of_basis (basisRestrictSupport K {d : Fin n →₀ ℕ | d.degree ≤ T})

theorem totalSpace_finrank {n : ℕ} {K : Type*} [Field K] (T : ℕ) :
    Module.finrank K (totalSpace (σ := Fin n) (K := K) T) = (T+n).choose n := by
  change Module.finrank K (restrictSupport K {d : Fin n →₀ ℕ | d.degree ≤ T}) = _
  rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)]
  rw [← card_simplexExponents n T, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun d => (mem_simplexExponents d).symm)

theorem independent_coordinates_hilbert_lower {n h : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (j : Fin h → Fin n)
    (hj : AlgebraicIndependent K (fun a => Ideal.Quotient.mk I (X (j a)))) (T : ℕ) :
    (T+h).choose h ≤
      Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) := by
  classical
  let := totalSpace_finite (n := n) (K := K) T
  let f := (Ideal.Quotient.mkₐ K I).comp (rename j)
  have hf : Function.Injective f := by
    rw [algebraicIndependent_iff_injective_aeval] at hj
    have he : MvPolynomial.aeval (fun a => Ideal.Quotient.mk I (X (j a))) = f := by
      apply algHom_ext
      intro a
      simp [f]
    rwa [he] at hj
  let g : totalSpace (σ := Fin h) (K := K) T →ₗ[K]
      (totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap :=
    (f.toLinearMap.domRestrict (totalSpace T)).codRestrict _ (by
      intro p
      exact ⟨rename j p.val,
        mem_totalSpace.mpr ((totalDegree_rename_le j p.val).trans (mem_totalSpace.mp p.property)),
        rfl⟩)
  have hg : Function.Injective g := by
    intro p q he
    exact Subtype.ext (hf (congrArg Subtype.val he))
  rw [← totalSpace_finrank (K := K) (n := h) T]
  exact LinearMap.finrank_le_finrank_of_injective hg

theorem empty_free_face_of_proper {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (hI : I ≠ ⊤)
    (s : Finset (Fin n →₀ ℕ))
    (hs : ∀ d ∈ s, ∃ p ∈ I, p ≠ 0 ∧ degLex.degree p = d) :
    FreeNormalFace s ∅ := by
  classical
  intro a ha hh
  have ha0 : a = 0 := Finsupp.support_eq_empty.mp (Finset.subset_empty.mp hh)
  obtain ⟨p, hp, hp0, hd⟩ := hs a ha
  have he := (degLex.degree_eq_zero_iff (f := p)).mp (hd.trans ha0)
  have hu : IsUnit (degLex.leadingCoeff p) := isUnit_iff_ne_zero.mpr
    (degLex.leadingCoeff_ne_zero_iff.mpr hp0)
  exact hI (I.eq_top_of_isUnit_mem hp (he ▸ hu.map C))

theorem coordinate_hilbert_degree_independent {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (hI : I ≠ ⊤) :
    ∃ P : Polynomial ℚ, ∃ j : Fin P.natDegree → Fin n,
      Function.Injective j ∧
      AlgebraicIndependent K (fun a => Ideal.Quotient.mk I (X (j a))) ∧
      (P.natDegree.factorial : ℚ)⁻¹ ≤ P.coeff P.natDegree ∧
      ∃ T₀ : ℕ, ∀ T ≥ T₀,
        (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
          P.eval (T : ℚ) := by
  classical
  obtain ⟨s, hsI, hs⟩ := ideal_normal_finite_obstructions degLex I
  let faces := (Finset.univ : Finset (Fin n)).powerset.filter (FreeNormalFace s)
  have hne : faces.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨?_, empty_free_face_of_proper I hI s hsI⟩⟩
    exact Finset.mem_powerset.mpr (Finset.empty_subset _)
  obtain ⟨J, hJ, hmax⟩ := Finset.exists_max_image faces Finset.card hne
  have hfree : FreeNormalFace s J := (Finset.mem_filter.mp hJ).2
  have hmax' (J' : Finset (Fin n)) (hJ' : FreeNormalFace s J') : J'.card ≤ J.card :=
    hmax J' (Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hJ'⟩)
  let j : Fin J.card → Fin n := fun a => ((Finset.equivFin J).symm a).val
  have hj : Function.Injective j := Subtype.val_injective.comp (Finset.equivFin J).symm.injective
  have hind : AlgebraicIndependent K (fun a => Ideal.Quotient.mk I (X (j a))) :=
    (free_face_algebraicIndependent I s hs J hfree).comp _ (Finset.equivFin J).symm.injective
  obtain ⟨P, _, T₀, hT⟩ := coordinate_hilbert_eventually_polynomial I
  have hcount (T : ℕ) :
      Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) =
        (normalExponents s T).card := by
    rw [coordinate_hilbert_count, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro d
    simp only [mem_normalExponents, hs, and_comm]
  let c := 2^n * (s.sup Finsupp.degree+1)^n
  let Q : Polynomial ℚ := Polynomial.C (c : ℚ) *
    (Polynomial.X + Polynomial.C 1)^J.card
  have hPnonneg : ∀ᶠ T : ℕ in Filter.atTop, 0 ≤ P.eval (T : ℚ) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨T₀, fun T h => ?_⟩
    rw [← hT T h]
    positivity
  have hPQ : ∀ᶠ T : ℕ in Filter.atTop, P.eval (T : ℚ) ≤ Q.eval (T : ℚ) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨T₀, fun T h => ?_⟩
    rw [← hT T h, hcount]
    simp only [Q, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_X]
    exact_mod_cast normalExponents_card_growth s J.card hmax' T
  have hupper : P.natDegree ≤ J.card := by
    apply (natDegree_le_of_eventually_nat_eval_bounds P Q hPnonneg hPQ).trans
    apply Polynomial.natDegree_mul_le.trans
    simp only [Polynomial.natDegree_C, zero_add]
    exact Polynomial.natDegree_pow_le.trans (by simp only [Polynomial.natDegree_X_add_C, mul_one]; exact le_rfl)
  have hlower : ∀ᶠ T : ℕ in Filter.atTop,
      (Polynomial.preHilbertPoly ℚ J.card 0).eval (T : ℚ) ≤ P.eval (T : ℚ) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨T₀, fun T h => ?_⟩
    rw [← hT T h, Polynomial.preHilbertPoly_eq_choose_add_sub _ _ (Nat.zero_le _)]
    simp only [Nat.sub_zero]
    exact_mod_cast independent_coordinates_hilbert_lower I j hind T
  have hbase : ∀ᶠ T : ℕ in Filter.atTop,
      0 ≤ (Polynomial.preHilbertPoly ℚ J.card 0).eval (T : ℚ) := by
    apply Filter.Eventually.of_forall
    intro T
    rw [Polynomial.preHilbertPoly_eq_choose_add_sub _ _ (Nat.zero_le _)]
    positivity
  have hdegree : P.natDegree = J.card := by
    apply Nat.le_antisymm hupper
    simpa only [Polynomial.natDegree_preHilbertPoly] using
      natDegree_le_of_eventually_nat_eval_bounds _ P hbase hlower
  have hcoeff : (J.card.factorial : ℚ)⁻¹ ≤ P.coeff J.card := by
    have hh := coeff_le_of_eventually_nat_eval_le
      (Polynomial.preHilbertPoly ℚ J.card 0) P J.card
      (by rw [Polynomial.natDegree_preHilbertPoly]) hupper hlower
    simpa only [Polynomial.coeff_preHilbertPoly_self] using hh
  refine ⟨P, ?_⟩
  rw [hdegree]
  exact ⟨j, hj, hind, hcoeff, T₀, hT⟩

theorem projection_hilbert_le {n m : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K))
    (J : Ideal (MvPolynomial (Fin m) K)) (j : Fin m → Fin n)
    (hker : ∀ p, Ideal.Quotient.mk I (rename j p) = 0 ↔ p ∈ J) (T : ℕ) :
    Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K J).toLinearMap) ≤
      Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) := by
  classical
  let := totalSpace_finite (n := n) (K := K) T
  let f₀ := (Ideal.Quotient.mkₐ K I).comp (rename j)
  let f := Ideal.Quotient.liftₐ J f₀ (fun p hp => (hker p).mpr hp)
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro y hy
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact (hker p).mp hy
  let g := (f.toLinearMap.domRestrict
    ((totalSpace T).map (Ideal.Quotient.mkₐ K J).toLinearMap)).codRestrict
      ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) (by
        rintro ⟨y, p, hp, rfl⟩
        exact ⟨rename j p,
          mem_totalSpace.mpr ((totalDegree_rename_le j p).trans (mem_totalSpace.mp hp)), rfl⟩)
  apply LinearMap.finrank_le_finrank_of_injective (f := g)
  intro y z he
  exact Subtype.ext (hf (congrArg Subtype.val he))

theorem not_independent_over_hilbert_degree {n h : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (P : Polynomial ℚ)
    (hP : P.natDegree ≤ h)
    (hT : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
        P.eval (T : ℚ)) (j : Fin (h+1) → Fin n) :
    ¬ AlgebraicIndependent K (fun a => Ideal.Quotient.mk I (X (j a))) := by
  intro hj
  have hlower : ∀ᶠ T : ℕ in Filter.atTop,
      (Polynomial.preHilbertPoly ℚ (h+1) 0).eval (T : ℚ) ≤ P.eval (T : ℚ) := by
    apply hT.mono
    intro T h
    rw [← h, Polynomial.preHilbertPoly_eq_choose_add_sub _ _ (Nat.zero_le _)]
    simp only [Nat.sub_zero]
    exact_mod_cast independent_coordinates_hilbert_lower I j hj T
  have hbase : ∀ᶠ T : ℕ in Filter.atTop,
      0 ≤ (Polynomial.preHilbertPoly ℚ (h+1) 0).eval (T : ℚ) := by
    apply Filter.Eventually.of_forall
    intro T
    rw [Polynomial.preHilbertPoly_eq_choose_add_sub _ _ (Nat.zero_le _)]
    positivity
  have hh := natDegree_le_of_eventually_nat_eval_bounds _ P hbase hlower
  rw [Polynomial.natDegree_preHilbertPoly] at hh
  omega

theorem projection_equation_degree_bound {n h : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (P : Polynomial ℚ)
    (hP : P.natDegree ≤ h)
    (hT : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
        P.eval (T : ℚ)) (j : Fin (h+1) → Fin n)
    (q : MvPolynomial (Fin (h+1)) K) (hq : q ≠ 0)
    (hker : ∀ p, Ideal.Quotient.mk I (rename j p) = 0 ↔ q ∣ p) :
    (q.totalDegree : ℚ) ≤ (h.factorial : ℚ) * P.coeff h := by
  have hh : ∀ᶠ T : ℕ in Filter.atTop,
      (hypersurfaceHilbertPolynomial h q.totalDegree).eval (T : ℚ) ≤ P.eval (T : ℚ) := by
    filter_upwards [hT, Filter.eventually_ge_atTop q.totalDegree] with T hT hqT
    rw [← hT, ← hypersurface_hilbert_polynomial q hq T hqT]
    exact_mod_cast projection_hilbert_le I (Ideal.span {q}) j
      (fun p => (hker p).trans Ideal.mem_span_singleton.symm) T
  have hcoeff := coeff_le_of_eventually_nat_eval_le
    (hypersurfaceHilbertPolynomial h q.totalDegree) P h
    (hypersurfaceHilbertPolynomial_degree _ _) hP hh
  rw [hypersurfaceHilbertPolynomial_coeff] at hcoeff
  have hf : (0 : ℚ) < h.factorial := by exact_mod_cast Nat.factorial_pos h
  exact (div_le_iff₀ hf).mp hcoeff |>.trans_eq (mul_comm _ _)

open Polynomial

theorem exists_irreducible_in_kernel {R S : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [CommRing S] [IsDomain S]
    (f : R →+* S) (p : R) (hp : p ≠ 0) (hfp : f p = 0) :
    ∃ g : R, Irreducible g ∧ f g = 0 := by
  induction p using WfDvdMonoid.induction_on_irreducible with
  | zero => exact (hp rfl).elim
  | unit u hu => exact (hu.map f).ne_zero hfp |>.elim
  | mul a i ha hi ih =>
    rw [map_mul, mul_eq_zero] at hfp
    rcases hfp with h | h
    · exact ⟨i, hi, h⟩
    · exact ih ha h

theorem principal_coordinate_kernel {R F L : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [Field F] [Field L]
    [Algebra R F] [IsFractionRing R F] [Algebra F L] [Algebra R L]
    [IsScalarTower R F L]
    (x : L) (p : Polynomial R) (hp : p ≠ 0) (hpx : Polynomial.aeval x p = 0) :
    ∃ g : Polynomial R, Irreducible g ∧ g.IsPrimitive ∧ g.natDegree ≠ 0 ∧
      (∀ q : Polynomial R, Polynomial.aeval x q = 0 ↔ g ∣ q) := by
  obtain ⟨g, hg, hxg⟩ := exists_irreducible_in_kernel (Polynomial.aeval x).toRingHom p hp hpx
  change Polynomial.aeval x g = 0 at hxg
  have hinj : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R F L]
    change Function.Injective ((algebraMap F L) ∘ (algebraMap R F))
    exact (RingHom.injective (algebraMap F L)).comp (IsFractionRing.injective R F)
  have hn : g.natDegree ≠ 0 := by
    intro h
    have he := eq_C_of_natDegree_eq_zero h
    have hh := hxg
    rw [he, Polynomial.aeval_C] at hh
    have hz : g.coeff 0 = 0 := hinj (hh.trans (map_zero _).symm)
    exact hg.ne_zero (he.trans (by rw [hz, Polynomial.C_0]))
  have hprim := hg.isPrimitive hn
  have hi : Irreducible (g.map (algebraMap R F)) :=
    hprim.irreducible_iff_irreducible_map_fraction_map.mp hg
  have hx : Polynomial.aeval x (g.map (algebraMap R F)) = 0 := by
    simpa only [Polynomial.aeval_map_algebraMap] using hxg
  have ha : IsAlgebraic F x := ⟨g.map (algebraMap R F), hi.ne_zero, hx⟩
  have hass := (minpoly.irreducible ha.isIntegral).associated_of_dvd hi (minpoly.dvd F x hx)
  refine ⟨g, hg, hprim, hn, ?_⟩
  intro q
  constructor
  · intro hq
    apply (hprim.dvd_iff_fraction_map_dvd_fraction_map F).mpr
    apply hass.dvd_iff_dvd_left.mp
    exact minpoly.dvd F x (by simpa only [Polynomial.aeval_map_algebraMap] using hq)
  · rintro ⟨r, rfl⟩
    simp only [map_mul, hxg, zero_mul]

open MvPolynomial in

theorem principal_projection_relation {h : ℕ} {K L : Type*} [Field K] [Field L]
    [Algebra K L] (y : Fin h → L) (hy : AlgebraicIndependent K y) (x : L)
    (p : MvPolynomial (Fin (h+1)) K) (hp : p ≠ 0)
    (hpx : MvPolynomial.aeval (Fin.cases x y) p = 0) :
    ∃ q : MvPolynomial (Fin (h+1)) K, Irreducible q ∧ q.degreeOf 0 ≠ 0 ∧
      (∀ r, MvPolynomial.aeval (Fin.cases x y) r = 0 ↔ q ∣ r) := by
  let R := MvPolynomial (Fin h) K
  let F := FractionRing R
  let f : R →ₐ[K] L := MvPolynomial.aeval y
  have hf : Function.Injective f := algebraicIndependent_iff_injective_aeval.mp hy
  let : Algebra R L := f.toRingHom.toAlgebra
  let : Algebra F L := (IsFractionRing.lift (K := F) hf).toAlgebra
  have hcomp : algebraMap R L = (algebraMap F L).comp (algebraMap R F) := by
    apply RingHom.ext
    intro a
    exact (IsFractionRing.lift_algebraMap (K := F) (g := f.toRingHom) hf a).symm
  let : IsScalarTower R F L := IsScalarTower.of_algebraMap_eq' hcomp
  let E := finSuccEquiv K h
  have heval (r : MvPolynomial (Fin (h+1)) K) :
      Polynomial.aeval x (E r) = MvPolynomial.aeval (Fin.cases x y) r := by
    have he : (Polynomial.aeval x).toRingHom.comp E.toRingHom =
        (MvPolynomial.aeval (Fin.cases x y)).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c
        change Polynomial.aeval x ((finSuccEquiv K h) (MvPolynomial.C c)) = _
        rw [finSuccEquiv_apply, eval₂Hom_C, RingHom.comp_apply, Polynomial.aeval_C]
        change MvPolynomial.aeval y (MvPolynomial.C c) =
          MvPolynomial.aeval (Fin.cases x y) (MvPolynomial.C c)
        simp only [MvPolynomial.aeval_C]
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · change Polynomial.aeval x ((finSuccEquiv K h) (MvPolynomial.X 0)) = _
          rw [finSuccEquiv_X_zero, Polynomial.aeval_X]
          change x = MvPolynomial.aeval (Fin.cases x y) (MvPolynomial.X (0 : Fin (h+1)))
          simp only [MvPolynomial.aeval_X, Fin.cases_zero]
        · change Polynomial.aeval x ((finSuccEquiv K h) (MvPolynomial.X j.succ)) = _
          rw [finSuccEquiv_X_succ, Polynomial.aeval_C]
          change MvPolynomial.aeval y (MvPolynomial.X j) =
            MvPolynomial.aeval (Fin.cases x y) (MvPolynomial.X j.succ)
          simp only [MvPolynomial.aeval_X, Fin.cases_succ]
    exact congrArg (fun g : MvPolynomial (Fin (h+1)) K →+* L => g r) he
  have hep : E p ≠ 0 := by
    intro hh
    exact hp (E.injective (hh.trans (map_zero E).symm))
  obtain ⟨g, hg, _, hgn, hgker⟩ := principal_coordinate_kernel (F := F) x (E p) hep
    ((heval p).trans hpx)
  refine ⟨E.symm g, ?_, ?_, ?_⟩
  · exact (MulEquiv.irreducible_iff E.symm).mpr hg
  · simpa only [← natDegree_finSuccEquiv, E, AlgEquiv.apply_symm_apply] using hgn
  · intro r
    rw [← heval r, hgker]
    constructor
    · rintro ⟨s, hs⟩
      refine ⟨E.symm s, ?_⟩
      apply E.injective
      simpa only [map_mul, AlgEquiv.apply_symm_apply] using hs
    · rintro ⟨s, rfl⟩
      exact ⟨E s, by simp only [map_mul, AlgEquiv.apply_symm_apply]⟩

theorem quotient_aeval_rename {n m : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (j : Fin m → Fin n) :
    MvPolynomial.aeval (fun a => Ideal.Quotient.mk I (MvPolynomial.X (j a))) =
      (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.rename j) := by
  ext a
  simp

theorem exists_principal_relation_of_dependent {h : ℕ} {K A : Type*}
    [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    (x : A) (y : Fin h → A) (hy : AlgebraicIndependent K y)
    (hxy : ¬ AlgebraicIndependent K (Fin.cases x y)) :
    ∃ q : MvPolynomial (Fin (h+1)) K, Irreducible q ∧ q.degreeOf 0 ≠ 0 ∧
      (∀ r, MvPolynomial.aeval (Fin.cases x y) r = 0 ↔ q ∣ r) := by
  let L := FractionRing A
  let e : A →ₐ[K] L := IsScalarTower.toAlgHom K A L
  have he : Function.Injective e := IsFractionRing.injective A L
  have hcase : Fin.cases (e x) (fun a => e (y a)) =
      fun a : Fin (h+1) => e (Fin.cases x y a) := by
    funext a
    exact Fin.cases rfl (fun _ => rfl) a
  have hei (r : MvPolynomial (Fin (h+1)) K) :
      MvPolynomial.aeval (Fin.cases (e x) (fun a => e (y a))) r =
        e (MvPolynomial.aeval (Fin.cases x y) r) := by
    rw [hcase, ← MvPolynomial.comp_aeval_apply]
  have hyL : AlgebraicIndependent K (fun a => e (y a)) := hy.map' he
  rw [algebraicIndependent_iff] at hxy
  push Not at hxy
  obtain ⟨p, hpx, hp⟩ := hxy
  obtain ⟨q, hq, hqdeg, hqker⟩ := principal_projection_relation
    (fun a => e (y a)) hyL (e x) p hp (by rw [hei, hpx, map_zero])
  refine ⟨q, hq, hqdeg, fun r => ?_⟩
  rw [← hqker, hei, map_eq_zero_iff e he]

theorem prime_projection_relation {n h : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (j : Fin h → Fin n)
    (hj : AlgebraicIndependent K (fun a => Ideal.Quotient.mk I (MvPolynomial.X (j a))))
    (i : Fin n)
    (hdep : ¬ AlgebraicIndependent K
      (fun a => Ideal.Quotient.mk I (MvPolynomial.X (Fin.cases i j a)))) :
    ∃ q : MvPolynomial (Fin (h+1)) K, Irreducible q ∧ q.degreeOf 0 ≠ 0 ∧
      (∀ r, Ideal.Quotient.mk I (MvPolynomial.rename (Fin.cases i j) r) = 0 ↔ q ∣ r) := by
  have hcase : Fin.cases (Ideal.Quotient.mk I (MvPolynomial.X i))
      (fun a => Ideal.Quotient.mk I (MvPolynomial.X (j a))) =
        fun a : Fin (h+1) => Ideal.Quotient.mk I (MvPolynomial.X (Fin.cases i j a)) := by
    funext a
    exact Fin.cases rfl (fun _ => rfl) a
  have hd : ¬ AlgebraicIndependent K
      (Fin.cases (Ideal.Quotient.mk I (MvPolynomial.X i))
        (fun a => Ideal.Quotient.mk I (MvPolynomial.X (j a)))) := by
    rwa [hcase]
  obtain ⟨q, hq, hqdeg, hqker⟩ := exists_principal_relation_of_dependent
    (Ideal.Quotient.mk I (MvPolynomial.X i))
    (fun a => Ideal.Quotient.mk I (MvPolynomial.X (j a))) hj hd
  refine ⟨q, hq, hqdeg, fun r => ?_⟩
  rw [← hqker, hcase, quotient_aeval_rename]
  rfl

theorem prime_projection_map {n h : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (z : Fin (h+1) → Fin n)
    (hz : AlgebraicIndependent K
      (fun a : Fin h => Ideal.Quotient.mk I (MvPolynomial.X (z a.succ))))
    (hdep : ¬ AlgebraicIndependent K
      (fun a => Ideal.Quotient.mk I (MvPolynomial.X (z a)))) :
    ∃ q : MvPolynomial (Fin (h+1)) K, Irreducible q ∧ q.degreeOf 0 ≠ 0 ∧
      (∀ r, Ideal.Quotient.mk I (MvPolynomial.rename z r) = 0 ↔ q ∣ r) := by
  have he (a : Fin (h+1)) : Fin.cases (z 0) (fun b : Fin h => z b.succ) a = z a :=
    Fin.cases rfl (fun _ => rfl) a
  have hd : ¬ AlgebraicIndependent K
      (fun a => Ideal.Quotient.mk I (MvPolynomial.X
        (Fin.cases (z 0) (fun b : Fin h => z b.succ) a))) := by
    simpa only [he] using hdep
  obtain ⟨q, hq, hqd, hker⟩ := prime_projection_relation I (fun a => z a.succ) hz (z 0) hd
  refine ⟨q, hq, hqd, fun r => ?_⟩
  have hr : MvPolynomial.rename z r =
      MvPolynomial.rename (fun a => Fin.cases (z 0) (fun b : Fin h => z b.succ) a) r :=
    congrArg (fun v : Fin (h+1) → Fin n => MvPolynomial.rename v r) (funext he).symm
  rw [hr]
  exact hker r

theorem bounded_projection_relation {n h : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (P : Polynomial ℚ) (hP : P.natDegree ≤ h)
    (hT : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
        P.eval (T : ℚ)) (z : Fin (h+1) → Fin n)
    (hz : AlgebraicIndependent K
      (fun a : Fin h => Ideal.Quotient.mk I (MvPolynomial.X (z a.succ)))) :
    ∃ q : MvPolynomial (Fin (h+1)) K, Irreducible q ∧ q.degreeOf 0 ≠ 0 ∧
      (q.totalDegree : ℚ) ≤ (h.factorial : ℚ) * P.coeff h ∧
      (∀ r, Ideal.Quotient.mk I (MvPolynomial.rename z r) = 0 ↔ q ∣ r) := by
  have hd := not_independent_over_hilbert_degree I P hP hT z
  obtain ⟨q, hq, hqdeg, hker⟩ := prime_projection_map I z hz hd
  exact ⟨q, hq, hqdeg,
    projection_equation_degree_bound I P hP hT z q hq.ne_zero hker, hker⟩

end QuarticPowerFree

end OAI

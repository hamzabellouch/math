import OAI.NumberTheory.PowerFree.DeformedRoots

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

section

open MvPolynomial MonomialOrder
open scoped MonomialOrder

theorem separate_powers_normal_form {n : ℕ} {K : Type*} [Field K]
    (D : ℕ) (q : Fin n → MvPolynomial (Fin n) K)
    (hq : ∀ i, (q i).totalDegree ≤ D) (p : MvPolynomial (Fin n) K) :
    ∃ (g : Fin n →₀ MvPolynomial (Fin n) K) (r : MvPolynomial (Fin n) K),
      p = Finsupp.linearCombination _ (fun i => X i ^ (D + 1) - q i) g + r ∧
      ∀ m ∈ r.support, ∀ i, m i ≤ D := by
  classical
  have hlt : ∀ i, degLex.degree (q i) ≺[degLex]
      degLex.degree (X i ^ (D + 1) : MvPolynomial (Fin n) K) := by
    intro i
    apply lt_of_not_ge
    intro h
    have ht := MvPolynomial.degLex_totalDegree_monotone h
    simp only [MvPolynomial.totalDegree_X_pow] at ht
    exact Nat.not_succ_le_self D (ht.trans (hq i))
  have hdeg : ∀ i, degLex.degree (X i ^ (D + 1) - q i) =
      Finsupp.single i (D + 1) := by
    intro i
    rw [degLex.degree_sub_of_lt (hlt i), X_pow_eq_monomial,
      degLex.degree_monomial, ite_eq_right one_ne_zero]
  have hun : ∀ i, IsUnit (degLex.leadingCoeff (X i ^ (D + 1) - q i)) := by
    intro i
    rw [degLex.leadingCoeff_sub_of_lt (hlt i), X_pow_eq_monomial,
      degLex.leadingCoeff_monomial]
    exact isUnit_one
  obtain ⟨g, r, he, _, hr⟩ := MonomialOrder.div hun p
  refine ⟨g, r, he, ?_⟩
  intro m hm i
  have hh := hr m hm i
  rw [hdeg i] at hh
  have : ¬ (D + 1 ≤ m i) := by
    intro h
    apply hh
    exact Finsupp.single_le_iff.mpr h
  omega

theorem card_separate_powers_roots {n : ℕ} {K ι : Type*} [Field K] [Fintype ι]
    (D : ℕ) (q : Fin n → MvPolynomial (Fin n) K)
    (hq : ∀ i, (q i).totalDegree ≤ D) (z : ι → Fin n → K)
    (hz : Function.Injective z)
    (hroot : ∀ a i, z a i ^ (D + 1) = eval (z a) (q i)) :
    Fintype.card ι ≤ (D + 1) ^ n := by
  classical
  let ex : (Fin n → Fin (D + 1)) → (Fin n →₀ ℕ) := fun m =>
    Finsupp.equivFunOnFinite.symm (fun i => (m i).val)
  let b : (Fin n → Fin (D + 1)) → (ι → K) := fun m a =>
    eval (z a) (monomial (ex m) 1)
  let E : MvPolynomial (Fin n) K →ₗ[K] (ι → K) :=
    { toFun := fun p a => eval (z a) p
      map_add' := by intro p r; ext a; simp
      map_smul' := by intro c p; ext a; simp [smul_eq_C_mul] }
  have hspan : Submodule.span K (Set.range b) = ⊤ := by
    apply top_unique
    intro v _
    obtain ⟨p, hp⟩ := exists_mv_interpolate z hz v
    obtain ⟨g, r, he, hr⟩ := separate_powers_normal_form D q hq p
    have her : E r = v := by
      funext a
      have h := congrArg (eval (z a)) he
      simp only [map_add, Finsupp.linearCombination_apply, Finsupp.sum,
        smul_eq_mul, map_sum, map_mul, map_sub, map_pow, eval_X, hroot,
        sub_self, mul_zero, Finset.sum_const_zero, zero_add, hp] at h
      exact h.symm
    rw [← her, r.as_sum, map_sum]
    apply Submodule.sum_mem
    intro m hm
    let m' : Fin n → Fin (D + 1) := fun i => ⟨m i, Nat.lt_succ_of_le (hr m hm i)⟩
    have hex : ex m' = m := by ext i; rfl
    have hb : E (monomial m (r.coeff m)) = r.coeff m • b m' := by
      funext a
      simp only [E, LinearMap.coe_mk, AddHom.coe_mk, b, hex, Pi.smul_apply,
        smul_eq_mul, eval_monomial, one_mul]
    rw [hb]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m', rfl⟩)
  have h := finrank_le_of_span_eq_top hspan
  simpa only [Module.finrank_pi, Fintype.card_fun, Fintype.card_fin] using h

end

section
open MvPolynomial

theorem card_nonsingular_polynomial_roots {n : ℕ} {K ι : Type*} [Field K]
    [Fintype ι] (D : ℕ) (f : Fin n → MvPolynomial (Fin n) K)
    (hf : ∀ i, (f i).totalDegree ≤ D) (a : ι → Fin n → K)
    (hinj : Function.Injective a) (ha : ∀ b i, eval (a b) (f i) = 0)
    (hJ : ∀ b, (Matrix.of (fun i j => eval (a b) (pderiv j (f i)))).det ≠ 0) :
    Fintype.card ι ≤ (D + 1) ^ n := by
  classical
  choose y hy hyr using fun b => exists_deformed_powerSeries_root f (a b) (ha b) (hJ b) D
  let L := FractionRing (PowerSeries K)
  let inc : PowerSeries K →+* L := algebraMap _ _
  let c : K →+* L := inc.comp PowerSeries.C
  let T : L := inc PowerSeries.X
  let z : ι → Fin n → L := fun b i => inc (y b i)
  have hinc : Function.Injective inc := IsFractionRing.injective _ _
  have ht : T ≠ 0 := by
    exact fun h => PowerSeries.X_ne_zero (hinc (h.trans inc.map_zero.symm))
  have hz : Function.Injective z := by
    intro b b' h
    apply hinj
    funext i
    have hyy := hinc (congrFun h i)
    have hcc := congrArg PowerSeries.constantCoeff hyy
    simpa only [hy] using hcc
  let q : Fin n → MvPolynomial (Fin n) L := fun i => (-T⁻¹) • map c (f i)
  have hq : ∀ i, (q i).totalDegree ≤ D := by
    intro i
    apply (totalDegree_smul_le _ _).trans
    have hmap : (map c (f i)).totalDegree ≤ (f i).totalDegree :=
      Finset.sup_mono (support_map_subset c (f i))
    exact hmap.trans (hf i)
  apply card_separate_powers_roots D q hq z hz
  intro b i
  have h := congrArg inc (hyr b i)
  simp only [map_add, map_mul, map_pow, map_zero, eval₂_comp_left] at h
  change eval₂ c (z b) (f i) + T * z b i ^ (D + 1) = 0 at h
  change z b i ^ (D + 1) = eval (z b) ((-T⁻¹) • map c (f i))
  rw [smul_eq_C_mul, map_mul, eval_C, ← eval₂_eq_eval_map]
  apply mul_left_cancel₀ ht
  rw [← mul_assoc, mul_neg, mul_inv_cancel₀ ht, neg_one_mul]
  exact eq_neg_of_add_eq_zero_right h

theorem totalDegree_linear_substitute_le {σ τ K : Type*} [CommSemiring K]
    (F : σ → MvPolynomial τ K) (hF : ∀ i, (F i).totalDegree ≤ 1)
    (p : MvPolynomial σ K) :
    (eval₂ C F p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum, eval₂_sum]
  apply totalDegree_finsetSum_le
  intro m hm
  rw [eval₂_monomial]
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  apply (totalDegree_finsetProd _ _).trans
  calc
    (∑ i ∈ m.support, (F i ^ m i).totalDegree) ≤
        ∑ i ∈ m.support, m i := by
      apply Finset.sum_le_sum
      intro i _
      exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (m i) (hF i))
    _ ≤ p.totalDegree := le_totalDegree hm

noncomputable def partialEval {ι κ K : Type*} [CommSemiring K] (x : ι → K) :
    MvPolynomial (ι ⊕ κ) K →+* MvPolynomial κ K :=
  eval₂Hom C (Sum.elim (fun i => C (x i)) X)

@[simp] theorem eval_partialEval {ι κ K : Type*} [CommSemiring K]
    (x : ι → K) (y : κ → K) (p : MvPolynomial (ι ⊕ κ) K) :
    eval y (partialEval x p) = eval (Sum.elim x y) p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [partialEval]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p a hp =>
    simp only [map_mul, hp]
    congr 1
    cases a <;> simp [partialEval]

theorem totalDegree_partialEval_le {ι κ K : Type*} [CommSemiring K]
    (x : ι → K) (p : MvPolynomial (ι ⊕ κ) K) :
    (partialEval x p).totalDegree ≤ p.totalDegree := by
  apply totalDegree_linear_substitute_le
  intro a
  cases a with
  | inl i => simp
  | inr j =>
    simpa [X] using
      totalDegree_monomial_le (Finsupp.single j 1) (1 : K)

theorem pderiv_partialEval {ι κ K : Type*} [CommSemiring K]
    (x : ι → K) (p : MvPolynomial (ι ⊕ κ) K) (j : κ) :
    pderiv j (partialEval x p) = partialEval x (pderiv (Sum.inr j) p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => simp [partialEval]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p a hp =>
    simp only [map_mul, pderiv_mul, hp, map_add]
    cases a with
    | inl i => simp [partialEval]
    | inr i =>
      simp only [partialEval, eval₂Hom_X', Sum.elim_inr, pderiv_X,
        Pi.single_apply, Sum.inr.injEq]
      split_ifs <;> simp

theorem card_smooth_patch {r m : ℕ} {K ι : Type*} [Field K] [Fintype K]
    [Fintype ι] (D : ℕ) (G : Fin m → MvPolynomial (Fin r ⊕ Fin m) K)
    (hG : ∀ j, (G j).totalDegree ≤ D) (z : ι → (Fin r ⊕ Fin m) → K)
    (hinj : Function.Injective z) (hz : ∀ b j, eval (z b) (G j) = 0)
    (hminor : ∀ b, (Matrix.of (fun i j => eval (z b) (pderiv (Sum.inr j) (G i)))).det ≠ 0) :
    Fintype.card ι ≤ Fintype.card K ^ r * (D + 1) ^ m := by
  classical
  let free : ι → Fin r → K := fun b i => z b (Sum.inl i)
  have hfiber (x : Fin r → K) : Fintype.card {b // free b = x} ≤ (D + 1) ^ m := by
    let a : {b // free b = x} → Fin m → K := fun b j => z b.val (Sum.inr j)
    have heq (b : {b // free b = x}) : Sum.elim x (a b) = z b.val := by
      funext j
      cases j with
      | inl i => exact (congrFun b.property i).symm
      | inr j => rfl
    apply card_nonsingular_polynomial_roots D (fun j => partialEval x (G j))
      (fun j => (totalDegree_partialEval_le x (G j)).trans (hG j)) a
    · intro b b' h
      apply Subtype.ext
      apply hinj
      rw [← heq b, ← heq b', h]
    · intro b j
      rw [eval_partialEval, heq]
      exact hz b.val j
    · intro b
      simpa only [pderiv_partialEval, eval_partialEval, heq] using hminor b.val
  calc
    Fintype.card ι = ∑ x : Fin r → K, Fintype.card {b // free b = x} := by
      rw [← Fintype.card_sigma]
      exact (Fintype.card_congr (Equiv.sigmaFiberEquiv free)).symm
    _ ≤ ∑ _x : Fin r → K, (D + 1) ^ m := Finset.sum_le_sum (fun x _ => hfiber x)
    _ = Fintype.card K ^ r * (D + 1) ^ m := by simp

end

open scoped BigOperators

theorem card_regular_residue_tuples {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (good : ∀ i, Finset (α i)) (A M h N b : ℕ)
    (hA : 1 ≤ A) (hM : 1 ≤ M)
    (hall : ∀ i, Fintype.card (α i) ≤ M^N)
    (hgood : ∀ i, (good i).card ≤ A*M^h) :
    let R := Finset.univ.filter fun x : ∀ i, α i =>
      (Finset.univ.filter fun i => x i ∉ good i).card ≤ b
    R.card ≤ 2^Fintype.card ι * A^Fintype.card ι *
      M^(h*Fintype.card ι+N*b) := by
  classical
  let U : Finset (Finset ι) := Finset.univ.powerset.filter fun u => u.card ≤ b
  let C : Finset ι → Finset (∀ i, α i) := fun u =>
    Fintype.piFinset fun i => if i ∈ u then Finset.univ else good i
  have hbase : 1 ≤ A*M^h := by simpa using Nat.mul_le_mul hA (one_le_pow₀ hM (n := h))
  have hC (u : Finset ι) (hu : u ∈ U) :
      (C u).card ≤ A^Fintype.card ι*M^(h*Fintype.card ι+N*b) := by
    have hub : u.card ≤ b := (Finset.mem_filter.mp hu).2
    calc
      (C u).card = ∏ i, (if i ∈ u then Fintype.card (α i) else (good i).card) := by
        simp only [C,Fintype.card_piFinset]
        apply Finset.prod_congr rfl
        intro i _
        split_ifs <;> simp
      _ ≤ ∏ i, (A*M^h) * (if i ∈ u then M^N else 1) := by
        apply Finset.prod_le_prod
        intro i _
        by_cases hi : i ∈ u
        · simp only [hi,ite_true]
          exact (hall i).trans (by simpa using Nat.mul_le_mul_right (M^N) hbase)
        · simpa only [hi,ite_false,mul_one] using hgood i
      _ = (A*M^h)^Fintype.card ι * (M^N)^u.card := by
        rw [Finset.prod_mul_distrib]
        simp
      _ ≤ (A*M^h)^Fintype.card ι * (M^N)^b := by
        gcongr
      _ = A^Fintype.card ι*M^(h*Fintype.card ι+N*b) := by
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_assoc, ← pow_add]
  have hsub : (Finset.univ.filter fun x : ∀ i, α i =>
      (Finset.univ.filter fun i => x i ∉ good i).card ≤ b) ⊆ U.biUnion C := by
    intro x hx
    let u := Finset.univ.filter fun i => x i ∉ good i
    refine Finset.mem_biUnion.mpr ⟨u, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
        (Finset.mem_filter.mp hx).2⟩
    · apply Fintype.mem_piFinset.mpr
      intro i
      by_cases hi : i ∈ u
      · simp only [hi,ite_true,Finset.mem_univ]
      · have hg : x i ∈ good i := by simpa [u] using hi
        simpa only [hi,ite_false] using hg
  calc
    _ ≤ (U.biUnion C).card := Finset.card_le_card hsub
    _ ≤ ∑ u ∈ U, (C u).card := Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ U, A^Fintype.card ι*M^(h*Fintype.card ι+N*b) :=
      Finset.sum_le_sum hC
    _ = U.card * (A^Fintype.card ι*M^(h*Fintype.card ι+N*b)) := by simp
    _ ≤ 2^Fintype.card ι * (A^Fintype.card ι*M^(h*Fintype.card ι+N*b)) := by
      apply Nat.mul_le_mul_right
      exact (Finset.card_filter_le _ _).trans (by simp)
    _ = _ := by ring

end QuarticPowerFree

end OAI

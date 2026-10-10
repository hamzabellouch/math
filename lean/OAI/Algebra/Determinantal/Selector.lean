import OAI.Algebra.Determinantal.BorderPolars

namespace OAI

namespace PermanentBorder.Selector
open MvPolynomial
variable {n R : Type*} [Fintype n] [DecidableEq n] [CommSemiring R]

noncomputable def allOnes (V : Type*) [Fintype V] : V →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => 1)

@[simp] theorem allOnes_apply {V : Type*} [Fintype V] (i : V) : allOnes V i = 1 := rfl

noncomputable def edgeExponent (e : n × n) : (n ⊕ n) →₀ ℕ :=
  Finsupp.single (.inl e.1) 1 + Finsupp.single (.inr e.2) 1

noncomputable def occupancy (S : Finset (n × n)) : (n ⊕ n) →₀ ℕ :=
  ∑ e ∈ S, edgeExponent e

omit [Fintype n] in
 theorem occupancy_left (S : Finset (n × n)) (i : n) :
    occupancy S (.inl i) = (S.filter (fun e => e.1 = i)).card := by
  classical
  rw [Finset.card_filter]
  simp only [occupancy, Finsupp.finsetSum_apply, edgeExponent, Finsupp.add_apply,
    Finsupp.single_apply, Sum.inl.injEq, Sum.inr_ne_inl,
    ite_false, add_zero]

omit [Fintype n] in
 theorem occupancy_right (S : Finset (n × n)) (j : n) :
    occupancy S (.inr j) = (S.filter (fun e => e.2 = j)).card := by
  classical
  rw [Finset.card_filter]
  simp only [occupancy, Finsupp.finsetSum_apply, edgeExponent, Finsupp.add_apply,
    Finsupp.single_apply, Sum.inr.injEq, Sum.inl_ne_inr,
    ite_false, zero_add]

noncomputable def permGraph (σ : Equiv.Perm n) : Finset (n × n) :=
  Finset.univ.image (fun j => (σ j,j))

@[simp] theorem mem_permGraph (σ : Equiv.Perm n) (i j : n) :
    (i,j) ∈ permGraph σ ↔ σ j = i := by
  simp [permGraph, eq_comm]

 theorem permGraph_injective : Function.Injective (permGraph (n := n)) := by
  intro σ τ h
  ext j
  have hmem : (σ j,j) ∈ permGraph σ := by simp
  rw [h] at hmem
  exact (mem_permGraph τ _ _).mp hmem |>.symm

 theorem occupancy_permGraph (σ : Equiv.Perm n) :
    occupancy (permGraph σ) = allOnes (n ⊕ n) := by
  classical
  ext v
  cases v with
  | inl i =>
    rw [occupancy_left, allOnes_apply]
    apply Finset.card_eq_one.mpr
    refine ⟨(i,σ.symm i), ?_⟩
    ext ⟨r,c⟩
    simp only [Finset.mem_filter, mem_permGraph, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨h₁,h₂⟩
      exact ⟨h₂, σ.injective ((h₁.trans h₂).trans (σ.apply_symm_apply i).symm)⟩
    · rintro ⟨rfl,rfl⟩
      simp
  | inr j =>
    rw [occupancy_right, allOnes_apply]
    apply Finset.card_eq_one.mpr
    refine ⟨(σ j,j), ?_⟩
    ext ⟨r,c⟩
    simp only [Finset.mem_filter, mem_permGraph, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨h₁,rfl⟩
      exact ⟨h₁.symm,rfl⟩
    · rintro ⟨rfl,rfl⟩
      exact ⟨rfl,rfl⟩

 theorem unique_column {S : Finset (n × n)}
    (h : occupancy S = allOnes (n ⊕ n)) (j : n) :
    ∃! i, (i,j) ∈ S := by
  have hc : (S.filter (fun e => e.2 = j)).card = 1 := by
    rw [← occupancy_right, h, allOnes_apply]
  obtain ⟨⟨r,c⟩, hset⟩ := Finset.card_eq_one.mp hc
  have hm : (r,c) ∈ S.filter (fun e => e.2 = j) := by simp [hset]
  obtain ⟨hr, rfl⟩ := Finset.mem_filter.mp hm
  refine ⟨r, hr, ?_⟩
  intro i hi
  have hmem : (i,c) ∈ S.filter (fun e => e.2 = c) := by simp [hi]
  rw [hset] at hmem
  exact congrArg Prod.fst (Finset.mem_singleton.mp hmem)

 theorem unique_row {S : Finset (n × n)}
    (h : occupancy S = allOnes (n ⊕ n)) (i : n) :
    ∃! j, (i,j) ∈ S := by
  have hc : (S.filter (fun e => e.1 = i)).card = 1 := by
    rw [← occupancy_left, h, allOnes_apply]
  obtain ⟨⟨r,c⟩, hset⟩ := Finset.card_eq_one.mp hc
  have hm : (r,c) ∈ S.filter (fun e => e.1 = i) := by simp [hset]
  obtain ⟨hmem0, rfl⟩ := Finset.mem_filter.mp hm
  refine ⟨c, hmem0, ?_⟩
  intro j hj
  have hmem : (r,j) ∈ S.filter (fun e => e.1 = r) := by simp [hj]
  rw [hset] at hmem
  exact congrArg Prod.snd (Finset.mem_singleton.mp hmem)

 theorem occupancy_eq_iff {S : Finset (n × n)} :
    occupancy S = allOnes (n ⊕ n) ↔ ∃ σ : Equiv.Perm n, S = permGraph σ := by
  classical
  constructor
  · intro h
    choose f hf hfu using unique_column h
    have hinj : Function.Injective f := by
      intro i j hij
      obtain ⟨c,hc,hcu⟩ := unique_row h (f i)
      exact (hcu i (hf i)).trans (hcu j (hij ▸ hf j)).symm
    have hsurj : Function.Surjective f := Finite.surjective_of_injective hinj
    let σ : Equiv.Perm n := Equiv.ofBijective f ⟨hinj,hsurj⟩
    refine ⟨σ, ?_⟩
    ext ⟨r,c⟩
    rw [mem_permGraph]
    change (r,c) ∈ S ↔ f c = r
    constructor
    · intro hr
      exact (hfu c r hr).symm
    · rintro rfl
      exact hf c
  · rintro ⟨σ,rfl⟩
    exact occupancy_permGraph σ

noncomputable def edgeProduct (M : Matrix n n R) : MvPolynomial (n ⊕ n) R :=
  ∏ e : n × n, (1 + monomial (edgeExponent e) (M e.1 e.2))

omit [DecidableEq n] in
 theorem edgeProduct_expansion (M : Matrix n n R) :
    edgeProduct M = ∑ S : Finset (n × n),
      monomial (occupancy S) (∏ e ∈ S, M e.1 e.2) := by
  classical
  simp only [edgeProduct, add_comm (1 : MvPolynomial (n ⊕ n) R)]
  rw [Finset.prod_add_one]
  simp only [← monomial_sum_prod, occupancy, Finset.powerset_univ]

 theorem edgeProduct_permanent (M : Matrix n n R) :
    (edgeProduct M).coeff (allOnes (n ⊕ n)) = M.permanent := by
  classical
  rw [edgeProduct_expansion, coeff_sum]
  simp only [coeff_monomial]
  let good := Finset.univ.filter (fun S : Finset (n × n) => occupancy S = allOnes (n ⊕ n))
  have hgood : good = Finset.univ.image (permGraph (n := n)) := by
    ext S
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, occupancy_eq_iff]
    exact ⟨fun ⟨σ,h⟩ => ⟨σ,h.symm⟩, fun ⟨σ,h⟩ => ⟨σ,h.symm⟩⟩
  calc
    (∑ S : Finset (n × n), if occupancy S = allOnes (n ⊕ n) then ∏ e ∈ S, M e.1 e.2 else 0) =
        ∑ S ∈ good, ∏ e ∈ S, M e.1 e.2 := by rw [Finset.sum_filter]
    _ = ∑ σ : Equiv.Perm n, ∏ e ∈ permGraph σ, M e.1 e.2 := by
      rw [hgood, Finset.sum_image]
      exact fun σ _ τ _ h => permGraph_injective h
    _ = M.permanent := by
      unfold Matrix.permanent
      apply Finset.sum_congr rfl
      intro σ _
      unfold permGraph
      rw [Finset.prod_image]
      intro i _ j _ hij
      exact congrArg Prod.snd hij
end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {I J R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]

 theorem coeff_separate_univariate (p : I → Polynomial R) (d : I →₀ ℕ) :
    (∏ i, Polynomial.eval₂ C (X i) (p i) : MvPolynomial I R).coeff d =
      ∏ i, (p i).coeff (d i) := by
  classical
  have hexp (i : I) : Polynomial.eval₂ C (X i) (p i) =
      ∑ k ∈ (p i).support, C ((p i).coeff k) * X i ^ k := by
    conv_lhs => rw [Polynomial.as_sum_support (p i)]
    simp only [Polynomial.eval₂_finsetSum, Polynomial.eval₂_monomial]
  simp_rw [hexp]
  rw [Finset.prod_univ_sum, coeff_sum]
  simp_rw [Finset.prod_mul_distrib, ← map_prod, coeff_C_mul, coeff_prod_X_pow]
  have heq (k : I → ℕ) : d = Finsupp.indicator Finset.univ (fun i _ => k i) ↔ k = d := by
    simp only [Finsupp.ext_iff, Finsupp.indicator_of_mem (Finset.mem_univ _),
      _root_.funext_iff, eq_comm]
  simp_rw [heq]
  rw [Finset.sum_eq_single (fun i => d i)]
  · simp
  · intro k _ hk
    simp [hk]
  · intro hd
    have hnot : ¬ ∀ i, d i ∈ (p i).support := by
      simpa only [Fintype.mem_piFinset] using hd
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    simp only [Polynomial.mem_support_iff, not_not] at hi
    simp only [ite_true, mul_one]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact hi

 theorem coeff_one_edge_factors (s : Finset J) (a : J → R) :
    (∏ j ∈ s, (1 + Polynomial.C (a j) * Polynomial.X)).coeff 1 = ∑ j ∈ s, a j := by
  classical
  have hzero (t : Finset J) :
      (∏ j ∈ t, (1 + Polynomial.C (a j) * Polynomial.X)).coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_prod]
    simp [Polynomial.coeff_add, Polynomial.mul_coeff_zero, Polynomial.coeff_one, Polynomial.coeff_X]
  induction s using Finset.induction_on with
  | empty => norm_num [Polynomial.coeff_one]
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, add_mul, one_mul,
      Polynomial.coeff_add, mul_assoc, mul_comm Polynomial.X,
      ← mul_assoc, Polynomial.coeff_mul_X, Polynomial.coeff_C_mul, hzero, ih, mul_one]
    exact add_comm _ _

 theorem coeff_row_edge_product [Fintype J] (a : I → J → R) :
    (∏ i, ∏ j, (1 + C (a i j) * X i) : MvPolynomial I R).coeff
        (Finsupp.equivFunOnFinite.symm (fun _ => 1)) =
      ∏ i, ∑ j, a i j := by
  classical
  let p : I → Polynomial R := fun i => ∏ j, (1 + Polynomial.C (a i j) * Polynomial.X)
  have hp (i : I) : Polynomial.eval₂ C (X i) (p i) = ∏ j, (1 + C (a i j) * X i) := by
    simp only [p, Polynomial.eval₂_finsetProd, Polynomial.eval₂_add, Polynomial.eval₂_one,
      Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
  rw [← show (∏ i, Polynomial.eval₂ C (X i) (p i)) =
      (∏ i, ∏ j, (1 + C (a i j) * X i)) from Finset.prod_congr rfl (fun i _ => hp i),
      coeff_separate_univariate]
  apply Finset.prod_congr rfl
  intro i _
  exact coeff_one_edge_factors Finset.univ (a i)
end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {A B R : Type*} [CommSemiring R]
 theorem sumRingEquiv_monomial (d : A →₀ ℕ) (e : B →₀ ℕ) (r : R) :
    sumRingEquiv R A B (monomial (d.sumElim e) r) = monomial d (monomial e r) := by
  simp [sumRingEquiv, monomial]
 theorem coeff_nested (p : MvPolynomial (A ⊕ B) R) (d : A →₀ ℕ) (e : B →₀ ℕ) :
    p.coeff (d.sumElim e) = ((sumRingEquiv R A B p).coeff d).coeff e := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add, hp, hq]
  | monomial f r =>
    obtain ⟨⟨a, b⟩, rfl⟩ := Finsupp.sumFinsuppAddEquivProdFinsupp.symm.surjective f
    have hab : Finsupp.sumFinsuppAddEquivProdFinsupp.symm (a, b) = a.sumElim b := by
      ext x; cases x <;> rfl
    rw [hab, sumRingEquiv_monomial]
    simp only [coeff_monomial]
    have habde : a.sumElim b = d.sumElim e ↔ a = d ∧ b = e := by
      constructor
      · intro h; constructor
        · ext x; exact congrArg (fun f => f (Sum.inl x)) h
        · ext x; exact congrArg (fun f => f (Sum.inr x)) h
      · rintro ⟨rfl, rfl⟩; rfl
    simp only [habde]
    by_cases ha : a = d <;> by_cases hb : b = e <;> simp [ha, hb]
end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]
omit [DecidableEq I] in
 theorem edgeProduct_nested (M : Matrix I I R) :
    sumRingEquiv R I I (edgeProduct M) =
      ∏ i, ∏ j, (1 + C (C (M i j)*X j)*X i) := by
  classical
  have hm (i j : I) : monomial (edgeExponent (i,j)) (M i j) =
      C (M i j)*X (.inl i)*X (.inr j) := by
    rw [C_mul_X_eq_monomial, X, monomial_mul_monomial]
    simp only [mul_one, edgeExponent]
  simp only [edgeProduct, map_prod, map_add, map_one]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  rw [hm]
  simp [mul_comm, mul_left_comm]

 theorem row_product_permanent (M : Matrix I I R) :
    (∏ i, ∑ j, C (M i j)*X j).coeff (allOnes I) = M.permanent := by
  rw [← edgeProduct_permanent]
  have hones : allOnes (I ⊕ I) = (allOnes I).sumElim (allOnes I) := by
    ext i; cases i <;> rfl
  rw [hones, coeff_nested, edgeProduct_nested]
  exact congrArg (fun (p : MvPolynomial I R) => p.coeff (allOnes I))
    (coeff_row_edge_product (fun i j => C (M i j)*X j)).symm

 theorem row_product_diagonal (M : Matrix I I R) (w : I → R) :
    (∏ i, ((∑ j, C (M i j)*X j) + C (w i)*X i)).coeff (allOnes I) =
      (M + Matrix.diagonal w).permanent := by
  rw [← row_product_permanent]
  apply congrArg (fun polynomial : MvPolynomial I R => polynomial.coeff (allOnes I))
  apply Finset.prod_congr rfl
  intro i _
  simp only [Matrix.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  congr 1
  simp only [Matrix.diagonal_apply, apply_ite, map_zero, ite_mul, zero_mul]
  simp

end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {I E R : Type*} [Fintype I] [Fintype E] [DecidableEq I] [CommSemiring R]
noncomputable def graphMatrix (src dst : E → I) (w : E → R) : Matrix I I R :=
  fun i j => ∑ e, if src e = i ∧ dst e = j then w e else 0

 theorem graph_row_sum (src dst : E → I) (w : E → R) (i : I) :
    (∑ e, if src e = i then C (w e)*X (dst e) else 0 : MvPolynomial I R) =
      ∑ j, C (graphMatrix src dst w i j)*X j := by
  classical
  simp only [graphMatrix, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : src e = i
  · simp only [h, true_and, apply_ite, map_zero, ite_mul, zero_mul]
    simp
  · simp [h]

 theorem coeff_graph_edges (src dst : E → I) (w : E → R) :
    (∏ e, (1 + monomial (edgeExponent (src e,dst e)) (w e))).coeff
      (allOnes (I ⊕ I)) = (graphMatrix src dst w).permanent := by
  classical
  have hm (e : E) : monomial (edgeExponent (src e,dst e)) (w e) =
      C (w e)*X (.inl (src e))*X (.inr (dst e)) := by
    rw [C_mul_X_eq_monomial, X, monomial_mul_monomial]
    simp only [mul_one, edgeExponent]
  have hones : allOnes (I ⊕ I) = (allOnes I).sumElim (allOnes I) := by
    ext x; cases x <;> rfl
  rw [hones, coeff_nested]
  simp only [map_prod, map_add, map_one, hm, map_mul,
    sumRingEquiv_C, sumRingEquiv_X_inl, sumRingEquiv_X_inr]
  have hf (e : E) : (1 + C (C (w e))*X (src e)*C (X (dst e)) :
      MvPolynomial I (MvPolynomial I R)) =
      ∏ i, (1 + C (if src e = i then C (w e)*X (dst e) else 0)*X i) := by
    rw [Finset.prod_eq_single (src e)]
    · simp [map_mul, mul_comm, mul_left_comm]
    · intro i hi hie
      simp [Ne.symm hie]
    · simp
  simp_rw [hf]
  rw [Finset.prod_comm]
  change (((_ : MvPolynomial I (MvPolynomial I R)).coeff
    (Finsupp.equivFunOnFinite.symm (fun _ => 1))).coeff (allOnes I)) = _
  rw [coeff_row_edge_product]
  simp_rw [graph_row_sum]
  exact row_product_permanent _
end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {R : Type*} [CommRing R]

noncomputable def threeOnes : Fin 3 →₀ ℕ :=
  Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1
noncomputable def gadgetAfterRows (a b c d : R) : MvPolynomial (Fin 3) R :=
  (1 + C a * X 0) * (1 + C b * X 1) *
    (-X 0 - X 1 + X 2 + C c) * (-X 0 - X 1 + X 2 + C d) *
    (X 0 + X 1 + X 2)

 theorem coeff_gadgetAfterRows (a b c d : R) :
    (gadgetAfterRows a b c d).coeff threeOnes = -2 + a*b*c*d := by
  classical
  unfold gadgetAfterRows
  ring_nf
  have h2 : (2 : MvPolynomial (Fin 3) R) = C (2 : R) := (map_ofNat C 2).symm
  have h3 : (3 : MvPolynomial (Fin 3) R) = C (3 : R) := (map_ofNat C 3).symm
  simp only [h2, h3, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_sub,
    X, C_apply, monomial_pow, monomial_mul_monomial, coeff_monomial]
  have heq (x y : Fin 3 →₀ ℕ) : x = y ↔ x 0 = y 0 ∧ x 1 = y 1 ∧ x 2 = y 2 := by
    rw [Finsupp.ext_iff]
    simp [Fin.forall_fin_succ]
  simp only [threeOnes, heq, Finsupp.add_apply, Finsupp.zero_apply,
    Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  norm_num [h01, h01.symm, h02, h02.symm, h12, h12.symm]
  ring
end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {R : Type*} [CommRing R]

noncomputable def gadgetH : Matrix (Fin 3) (Fin 3) R := !![-1,-1,1; -1,-1,1; 1,1,1]

noncomputable def gadgetRowEntries (c d : R) : Fin 3 → Option (Fin 3) → MvPolynomial (Fin 3) R :=
  fun i j => match j with
  | none => C (![c,d,0] i)
  | some j => C (gadgetH i j) * X j

noncomputable def gadgetNested (a b c d : R) : MvPolynomial (Fin 3) (MvPolynomial (Fin 3) R) :=
  C ((1 + C a * X 0)*(1 + C b * X 1)) *
    ∏ i, ∏ j, (1 + C (gadgetRowEntries c d i j) * X i)

 theorem gadgetNested_rows (a b c d : R) :
    (gadgetNested a b c d).coeff (Finsupp.equivFunOnFinite.symm (fun _ => 1)) =
      gadgetAfterRows a b c d := by
  classical
  rw [gadgetNested, coeff_C_mul, coeff_row_edge_product]
  simp only [Fin.prod_univ_succ, Fintype.prod_empty, mul_one, Fintype.sum_option,
    gadgetRowEntries, Fin.sum_univ_succ, Fintype.sum_empty, add_zero]
  simp [gadgetH, gadgetAfterRows]
  ring

noncomputable def gadgetEdges (a b c d : R) : MvPolynomial (Fin 3 ⊕ Fin 3) R :=
  (1 + C a * X (.inr 0)) * (1 + C b * X (.inr 1)) *
    ∏ i, ((1 + C (![c,d,0] i) * X (.inl i)) *
      ∏ j, (1 + C (gadgetH i j) * X (.inr j) * X (.inl i)))

 theorem gadgetEdges_nested (a b c d : R) :
    sumRingEquiv R (Fin 3) (Fin 3) (gadgetEdges a b c d) = gadgetNested a b c d := by
  classical
  simp [gadgetEdges, gadgetNested, map_prod, Fintype.prod_option, gadgetRowEntries,
    map_mul, mul_assoc]

 theorem gadgetEdges_coefficient (a b c d : R) :
    (gadgetEdges a b c d).coeff (threeOnes.sumElim threeOnes) = -2 + a*b*c*d := by
  rw [coeff_nested, gadgetEdges_nested]
  have hones : threeOnes = Finsupp.equivFunOnFinite.symm (fun _ => 1) := by
    ext i; fin_cases i <;> simp [threeOnes]
  rw [hones, gadgetNested_rows, ← hones, coeff_gadgetAfterRows]

end PermanentBorder.Selector

end OAI

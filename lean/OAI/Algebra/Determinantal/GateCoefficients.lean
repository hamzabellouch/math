import OAI.Algebra.Determinantal.Gates

namespace OAI
namespace PermanentBorder.Selector.Gates
open MvPolynomial
variable {A B R : Type*} [CommSemiring R]
 theorem sumRingEquiv_rename_inl (p : MvPolynomial A R) :
    sumRingEquiv R A B (rename Sum.inl p) = map C p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => simp [hp]
 theorem sumRingEquiv_rename_inr (p : MvPolynomial B R) :
    sumRingEquiv R A B (rename Sum.inr p) = C p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => simp [hp]
 theorem coeff_sum_product (p : MvPolynomial A R) (q : MvPolynomial B R)
    (d : A →₀ ℕ) (e : B →₀ ℕ) :
    (rename Sum.inl p * rename Sum.inr q).coeff (d.sumElim e) = p.coeff d * q.coeff e := by
  rw [coeff_nested, map_mul, sumRingEquiv_rename_inl, sumRingEquiv_rename_inr,
    mul_comm, coeff_C_mul, coeff_map, mul_comm, coeff_C_mul]
end PermanentBorder.Selector.Gates
namespace PermanentBorder.Selector.Gates
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
end PermanentBorder.Selector.Gates

namespace PermanentBorder.Selector.Gates
open MvPolynomial
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]
noncomputable def gateOuter (h : ℕ) : MvPolynomial (I ⊕ I) R :=
  rename Sum.inl ((∑ i, X i)^h) * rename Sum.inr ((∑ i, X i)^h)

 theorem coeff_gateOuter (s : Finset I) (h : ℕ) :
    (gateOuter (R := R) h).coeff ((subsetExponent s).sumElim (subsetExponent s)) =
      if s.card = h then (h.factorial : R)^2 else 0 := by
  rw [gateOuter, coeff_sum_product, coeff_gate_half]
  split_ifs <;> simp [pow_two]

noncomputable def gateCrossEntries (h : ℕ) :
    (Fin h ⊕ Fin h) → I → MvPolynomial (I ⊕ I) R :=
  fun v i => match v with
  | .inl _ => X (.inr i)
  | .inr _ => X (.inl i)

noncomputable def gateCrossEdges (h : ℕ) :
    MvPolynomial (Fin h ⊕ Fin h) (MvPolynomial (I ⊕ I) R) :=
  ∏ v, ∏ i, (1 + C (gateCrossEntries h v i) * X v)

omit [DecidableEq I] in
 theorem gateCrossEdges_coefficient (h : ℕ) :
    (gateCrossEdges (I := I) (R := R) h).coeff
      (Finsupp.equivFunOnFinite.symm (fun _ => 1)) = gateOuter h := by
  rw [gateCrossEdges, coeff_row_edge_product]
  simp [Fintype.prod_sum_type, gateCrossEntries, gateOuter, map_pow, map_sum, mul_comm]

 theorem subsetExponent_add_compl (s : Finset I) :
    subsetExponent sᶜ + subsetExponent s = subsetExponent Finset.univ := by
  ext i
  by_cases hi : i ∈ s <;> simp [hi]

 theorem coeff_gate_prescribed_distinguished (s : Finset I) (h : ℕ) :
    ((gateOuter (R := R) h) *
      monomial ((subsetExponent s).sumElim (subsetExponent s)) 1).coeff
      ((subsetExponent Finset.univ).sumElim (subsetExponent Finset.univ)) =
        if Fintype.card I - s.card = h then (h.factorial : R)^2 else 0 := by
  have heq : (subsetExponent Finset.univ).sumElim (subsetExponent Finset.univ) =
      ((subsetExponent sᶜ).sumElim (subsetExponent sᶜ)) +
      ((subsetExponent s).sumElim (subsetExponent s)) := by
    rw [← subsetExponent_add_compl s]
    ext i; cases i <;> rfl
  rw [heq, coeff_mul_monomial, mul_one, coeff_gateOuter, Finset.card_compl]
end PermanentBorder.Selector.Gates
namespace PermanentBorder.Selector.Gates
open MvPolynomial
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]
noncomputable def pairedExponent (i : I) : I ⊕ I →₀ ℕ :=
  (Finsupp.single i 1).sumElim (Finsupp.single i 1)
omit [Fintype I] in
 theorem sum_pairedExponent (s : Finset I) :
    (∑ i ∈ s, pairedExponent i) = (subsetExponent s).sumElim (subsetExponent s) := by
  classical
  ext v
  cases v with
  | inl i => simp [pairedExponent, Finsupp.finsetSum_apply, Finsupp.sumElim_inl,
      Finsupp.single_apply, eq_comm]
  | inr i => simp [pairedExponent, Finsupp.finsetSum_apply, Finsupp.sumElim_inr,
      Finsupp.single_apply, eq_comm]

 theorem independent_boundary_expansion (a : I → R) :
    (∏ i, (1 + monomial (pairedExponent i) (a i))) =
      ∑ s : Finset I, monomial ((subsetExponent s).sumElim (subsetExponent s)) (∏ i ∈ s, a i) := by
  classical
  simp only [add_comm (1 : MvPolynomial (I ⊕ I) R)]
  rw [Finset.prod_add_one]
  simp only [← monomial_sum_prod, sum_pairedExponent, Finset.powerset_univ]

omit [DecidableEq I] in
 theorem univariate_boundary_coefficient (a : I → R) (q : ℕ) :
    (∏ i, (1 + Polynomial.C (a i) * Polynomial.X)).coeff q =
      ∑ s : Finset I, if s.card = q then ∏ i ∈ s, a i else 0 := by
  classical
  simp only [add_comm (1 : Polynomial R)]
  rw [Finset.prod_add_one]
  simp only [Finset.prod_mul_distrib, ← map_prod, Finset.prod_const, Polynomial.finsetSum_coeff,
    eq_comm, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero,
    Finset.powerset_univ]

 theorem gate_filters_prescribed_count (a : I → R) (q : ℕ) (hq : q ≤ Fintype.card I) :
    (gateOuter (Fintype.card I-q) * ∏ i, (1 + monomial (pairedExponent i) (a i))).coeff
      ((subsetExponent Finset.univ).sumElim (subsetExponent Finset.univ)) =
      ((Fintype.card I-q).factorial : R)^2 *
        (∏ i, (1 + Polynomial.C (a i) * Polynomial.X)).coeff q := by
  classical
  rw [independent_boundary_expansion, Finset.mul_sum, coeff_sum,
    univariate_boundary_coefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have hm (e : I ⊕ I →₀ ℕ) (a : R) : monomial e a = C a * monomial e 1 := by simp only [C_mul_monomial, mul_one]
  rw [hm, ← mul_assoc, mul_comm (gateOuter _), mul_assoc, coeff_C_mul,
    coeff_gate_prescribed_distinguished]
  have hcard : s.card ≤ Fintype.card I := Finset.card_le_univ s
  have heq : Fintype.card I - s.card = Fintype.card I - q ↔ s.card = q := by omega
  simp only [heq]
  split_ifs <;> simp [mul_comm]
end PermanentBorder.Selector.Gates

namespace PermanentBorder.Selector.Gates
open MvPolynomial
variable {I J R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]

noncomputable def blockExponent (d : I → J →₀ ℕ) : I × J →₀ ℕ :=
  ∑ i, (d i).mapDomain (fun j => (i,j))

omit [Fintype I] in
 theorem mapDomain_block_apply (d : J →₀ ℕ) (i k : I) (j : J) :
    d.mapDomain (fun j => (i,j)) (k,j) = if i = k then d j else 0 := by
  classical
  by_cases h : i = k
  · subst k
    simpa using Finsupp.mapDomain_apply_of_injective (fun a b h => congrArg Prod.snd h) d j
  · rw [ite_eq_right h]
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨a, ha⟩
    exact h (congrArg Prod.fst ha)

 @[simp] theorem blockExponent_apply (d : I → J →₀ ℕ) (i : I) (j : J) :
    blockExponent d (i,j) = d i j := by
  classical
  simp only [blockExponent, Finsupp.finsetSum_apply, mapDomain_block_apply]
  simp

 theorem blockExponent_injective : Function.Injective (blockExponent (I := I) (J := J)) := by
  intro d e h
  funext i
  ext j
  simpa using congrArg (fun a : I × J →₀ ℕ => a (i,j)) h

 theorem coeff_independent_blocks (p : I → MvPolynomial J R) (d : I → J →₀ ℕ) :
    (∏ i, rename (fun j => (i,j)) (p i)).coeff (blockExponent d) =
      ∏ i, (p i).coeff (d i) := by
  classical
  have hexp (i : I) : rename (fun j => (i,j)) (p i) =
      ∑ k ∈ (p i).support, monomial (k.mapDomain (fun j => (i,j))) ((p i).coeff k) := by
    conv_lhs => rw [MvPolynomial.as_sum (p i)]
    simp only [map_sum, rename_monomial]
  simp_rw [hexp]
  rw [Finset.prod_univ_sum, coeff_sum]
  simp_rw [← monomial_sum_prod, coeff_monomial]
  change (∑ k ∈ Fintype.piFinset (fun i => (p i).support),
    if blockExponent k = blockExponent d then ∏ i, (p i).coeff (k i) else 0) = _
  simp only [blockExponent_injective.eq_iff]
  rw [Finset.sum_eq_single d]
  · simp
  · intro k _ h; simp [h]
  · intro hd
    have hnot : ¬ ∀ i, d i ∈ (p i).support := by
      simpa only [Fintype.mem_piFinset] using hd
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    simp only [mem_support_iff, not_not] at hi
    simp only [ite_true]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
end PermanentBorder.Selector.Gates

namespace PermanentBorder.Selector.Gates
open MvPolynomial
variable {I C R : Type*} [Fintype I] [Fintype C] [DecidableEq I] [DecidableEq C] [CommSemiring R]
 theorem gate_network_filters (a : C → I → R) (q : ℕ) (hq : q ≤ Fintype.card I) :
    (∏ c, rename (fun v => (c,v))
      (gateOuter (Fintype.card I-q) * ∏ i, (1 + monomial (pairedExponent i) (a c i)))).coeff
      (blockExponent (fun (_ : C) => (subsetExponent Finset.univ).sumElim
        (subsetExponent (Finset.univ : Finset I)))) =
    (((Fintype.card I-q).factorial : R)^2)^Fintype.card C *
      ∏ c, (∏ i, (1 + Polynomial.C (a c i)*Polynomial.X)).coeff q := by
  rw [coeff_independent_blocks]
  simp_rw [gate_filters_prescribed_count _ q hq]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
end PermanentBorder.Selector.Gates

namespace PermanentBorder.Selector.Gates
open MvPolynomial
variable {A B I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]
noncomputable def allOnes (A : Type*) [Fintype A] : A →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => 1)
 theorem allOnes_map_equiv [Fintype A] [Fintype B] (e : A ≃ B) :
    (allOnes A).mapDomain e = allOnes B := by
  classical
  ext b
  obtain ⟨a,rfl⟩ := e.surjective b
  rw [Finsupp.mapDomain_apply_of_injective e.injective]
  rfl
 theorem allOnes_sum [Fintype A] [Fintype B] :
    allOnes (A ⊕ B) = (allOnes A).sumElim (allOnes B) := by
  ext v; cases v <;> rfl
 theorem subset_univ_ones : subsetExponent (Finset.univ : Finset I) = allOnes I := by
  ext i
  simp [allOnes]

def sumSquareSplit : ((A ⊕ B) ⊕ (A ⊕ B)) ≃ ((B ⊕ B) ⊕ (A ⊕ A)) where
  toFun
  | .inl (.inl i) => .inr (.inl i)
  | .inr (.inl i) => .inr (.inr i)
  | .inl (.inr j) => .inl (.inl j)
  | .inr (.inr j) => .inl (.inr j)
  invFun
  | .inr (.inl i) => .inl (.inl i)
  | .inr (.inr i) => .inr (.inl i)
  | .inl (.inl j) => .inl (.inr j)
  | .inl (.inr j) => .inr (.inr j)
  left_inv x := by rcases x with (i|j)|(i|j) <;> rfl
  right_inv x := by rcases x with (i|j)|(i|j) <;> rfl

noncomputable def fullGateEdges (a : I → R) (h : ℕ) :
    MvPolynomial ((I ⊕ Fin h) ⊕ (I ⊕ Fin h)) R :=
  (∏ i, ∏ j, (1 + X (.inl (.inl i))*X (.inr (.inr j)))) *
  (∏ j, ∏ i, (1 + X (.inl (.inr j))*X (.inr (.inl i)))) *
  ∏ i, (1 + C (a i)*X (.inl (.inl i))*X (.inr (.inl i)))

 theorem full_gate_split (a : I → R) (h : ℕ) :
    sumRingEquiv R (Fin h ⊕ Fin h) (I ⊕ I)
      (rename sumSquareSplit (fullGateEdges a h)) =
    gateCrossEdges h * C (∏ i, (1 + monomial (pairedExponent i) (a i))) := by
  classical
  simp only [fullGateEdges, map_mul, map_prod, map_add, map_one, rename_X, rename_C]
  simp only [sumSquareSplit, Equiv.coe_fn_mk, sumRingEquiv_X_inl, sumRingEquiv_X_inr, sumRingEquiv_C]
  apply congrArg₂ (·*·)
  · simp only [gateCrossEdges, Fintype.prod_sum_type, gateCrossEntries]
    rw [mul_comm]
    apply congrArg₂ (·*·)
    · apply Finset.prod_congr rfl
      intro j _
      apply Finset.prod_congr rfl
      intro i _
      rw [mul_comm]
    · exact Finset.prod_comm
  · apply Finset.prod_congr rfl
    intro i _
    have hm : monomial (pairedExponent i) (a i) = C (a i)*X (.inl i)*X (.inr i) := by
      rw [C_mul_X_eq_monomial, X, monomial_mul_monomial]
      congr 1
      · ext v; cases v; simp [pairedExponent]
      · simp
    rw [hm, map_mul, map_mul]

 theorem full_gate_count (a : I → R) (q : ℕ) (hq : q ≤ Fintype.card I) :
    (fullGateEdges a (Fintype.card I-q)).coeff (allOnes _) =
    (((Fintype.card I-q).factorial : R)^2) *
      (∏ i, (1 + Polynomial.C (a i)*Polynomial.X)).coeff q := by
  have hr := coeff_rename_mapDomain sumSquareSplit sumSquareSplit.injective
    (fullGateEdges a (Fintype.card I-q)) (allOnes _)
  rw [allOnes_map_equiv] at hr
  have hc : (gateCrossEdges (I := I) (R := R) (Fintype.card I-q)).coeff
      (allOnes _) = gateOuter (Fintype.card I-q) := gateCrossEdges_coefficient _
  rw [← hr, allOnes_sum, coeff_nested, full_gate_split, mul_comm, coeff_C_mul, hc, mul_comm]
  rw [allOnes_sum, ← subset_univ_ones]
  exact gate_filters_prescribed_count a q hq
end PermanentBorder.Selector.Gates

end OAI

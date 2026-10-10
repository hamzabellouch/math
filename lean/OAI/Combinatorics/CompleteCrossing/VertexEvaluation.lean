import OAI.Combinatorics.CompleteCrossing.OrderPairing
import OAI.Combinatorics.CompleteCrossing.Polynomials

namespace OAI

/-! Vertex specialization, local interpolation tests, and kernel vanishing. -/

section

/-! Evaluation symmetries and genuine degree bounds after fixing a vertex. -/
noncomputable section
open scoped BigOperators
namespace Paper170

theorem evalFour_swapFirst (P : Poly4) (x u y v : ℝ) :
    evalFour x u y v (swapFirstPair P) = evalFour u x y v P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [swapFirstPair, evalFour]
  | add P Q hP hQ => simpa using congrArg₂ (·+·) hP hQ
  | mul_X P i hP =>
    simp only [swapFirstPair, AlgHom.toLinearMap_apply, map_mul, MvPolynomial.rename_X] at hP ⊢
    change MvPolynomial.aeval ![x,u,y,v] _ = MvPolynomial.aeval ![u,x,y,v] _
    change MvPolynomial.aeval ![x,u,y,v] _ = MvPolynomial.aeval ![u,x,y,v] _ at hP
    simp only [map_mul]
    rw [hP]
    fin_cases i <;> simp [Equiv.swap_apply_def, Fin.ext_iff]

theorem evalFour_swapSecond (P : Poly4) (x u y v : ℝ) :
    evalFour x u y v (swapSecondPair P) = evalFour x u v y P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [swapSecondPair, evalFour]
  | add P Q hP hQ => simpa using congrArg₂ (·+·) hP hQ
  | mul_X P i hP =>
    simp only [swapSecondPair, AlgHom.toLinearMap_apply, map_mul, MvPolynomial.rename_X] at hP ⊢
    change MvPolynomial.aeval ![x,u,y,v] _ = MvPolynomial.aeval ![x,u,v,y] _
    change MvPolynomial.aeval ![x,u,y,v] _ = MvPolynomial.aeval ![x,u,v,y] _ at hP
    simp only [map_mul]
    rw [hP]
    fin_cases i <;> simp [Equiv.swap_apply_def, Fin.ext_iff]

theorem vertexSpecialization_monomial (x : ℝ) (m : Fin 4 →₀ ℕ) (c : ℝ) :
    vertexSpecialization x (MvPolynomial.monomial m c) =
      MvPolynomial.C (c*x^m 0*x^m 2) * MvPolynomial.X 0^m 1 * MvPolynomial.X 1^m 3 := by
  simp only [vertexSpecialization, MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
  rw [Finsupp.prod_fintype]
  · simp [Fin.prod_univ_four]
    ring
  · intro i
    simp

theorem vertexSpecialization_rectangle (s : ℕ) (P : endpointSymmetricSpace s) (x : ℝ) :
    vertexSpecialization x P.val ∈ rectangle (s-2) (s-2) := by
  have hp := ((symmetric_space_membership s P.val).mp P.property).1
  have hb (k : Fin 2) : (vertexSpecialization x P.val).degreeOf k ≤ s-2 := by
    rw [P.val.as_sum, map_sum]
    apply (MvPolynomial.degreeOf_sum_le k _ _).trans
    apply Finset.sup_le
    intro m hm
    rw [vertexSpecialization_monomial]
    have h1 := MvPolynomial.degreeOf_le_iff.mp (hp 1) m hm
    have h3 := MvPolynomial.degreeOf_le_iff.mp (hp 3) m hm
    have hmul := MvPolynomial.degreeOf_mul_le k
      (MvPolynomial.C (P.val.coeff m*x^m 0*x^m 2)*MvPolynomial.X 0^m 1)
      (MvPolynomial.X 1^m 3)
    have hC := MvPolynomial.degreeOf_C_mul_le (MvPolynomial.X 0^m 1 : Poly2) k
      (P.val.coeff m*x^m 0*x^m 2)
    have hpow0 := MvPolynomial.degreeOf_pow_le k (MvPolynomial.X 0 : Poly2) (m 1)
    have hpow1 := MvPolynomial.degreeOf_pow_le k (MvPolynomial.X 1 : Poly2) (m 3)
    fin_cases k <;> norm_num [MvPolynomial.degreeOf_X, Fin.ext_iff] at hpow0 hpow1 hmul hC ⊢ <;> omega
  exact (rectangle_membership _ _ _).mpr ⟨hb 0,hb 1⟩

theorem neighbor_nodePolynomial {n : ℕ} (node : Fin n → ℝ) (i : Fin n) :
    Zarankiewicz.nodePolynomial (fun p : {j : Fin n // j ≠ i} => node p.val) =
      omittedNodePolynomial node i := by
  classical
  unfold Zarankiewicz.nodePolynomial omittedNodePolynomial
  exact (Finset.prod_subtype (Finset.univ.erase i) (by simp)
    (fun j => Polynomial.X-Polynomial.C (node j))).symm

theorem neighbor_nodeWeight {n : ℕ} (node : Fin n → ℝ) (hn : Function.Injective node)
    (i : Fin n) (p : {j : Fin n // j ≠ i}) :
    nodeWeight (fun q : {j : Fin n // j ≠ i} => node q.val) p =
      (node p.val-node i)*nodeWeight node p.val := by
  classical
  rw [omitted_node_weight node hn i p.val p.property.symm]
  unfold nodeWeight Zarankiewicz.derivativeAtNode
  rw [neighbor_nodePolynomial]

theorem sum_away {n : ℕ} (i : Fin n) (f : Fin n → ℝ) (hi : f i=0) :
    (∑j, f j) = ∑j : {j : Fin n // j ≠ i}, f j.val := by
  classical
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hi, add_zero]
  exact Finset.sum_subtype (Finset.univ.erase i) (by simp) f

end Paper170

end
end

section

/-! The kernel vanishes on every orientation of an independent supported edge pair. -/
noncomputable section
namespace Paper170

theorem kernel_ordered_eval_zero {n s : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (P : endpointSymmetricSpace s) (hP : supportEvaluation s node J P = 0)
    {i p k q : Fin n} (hip : i<p) (hkq : k<q) (hik : i≠k) (hiq : i≠q)
    (hpk : p≠k) (hpq : p≠q) (hJ : J i p k q ≠ 0) :
    evalFour (node i) (node p) (node k) (node q) P.val = 0 := by
  classical
  let a : SupportCoord J := ⟨((i,p),(k,q)), by
    simp only [supportedPairs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hip,hkq,hik,hiq,hpk,hpq,hJ⟩⟩
  exact congrFun hP a

theorem kernel_independent_eval_zero {n s : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (hreverseLeft : ∀i p k q, J p i k q = -J i p k q)
    (hreverseRight : ∀i p k q, J i p q k = -J i p k q)
    (P : endpointSymmetricSpace s) (hP : supportEvaluation s node J P = 0)
    {i p k q : Fin n} (hip : i≠p) (hkq : k≠q) (hik : i≠k) (hiq : i≠q)
    (hpk : p≠k) (hpq : p≠q) (hJ : J i p k q ≠ 0) :
    evalFour (node i) (node p) (node k) (node q) P.val = 0 := by
  have hsym := (symmetric_space_membership s P.val).mp P.property
  have he1 (x u y v : ℝ) : evalFour x u y v P.val = evalFour u x y v P.val := by
    rw [← evalFour_swapFirst, hsym.2.1]
  have he2 (x u y v : ℝ) : evalFour x u y v P.val = evalFour x u v y P.val := by
    rw [← evalFour_swapSecond, hsym.2.2]
  rcases lt_or_gt_of_ne hip with hip | hpi
  · rcases lt_or_gt_of_ne hkq with hkq | hqk
    · exact kernel_ordered_eval_zero node J P hP hip hkq hik hiq hpk hpq hJ
    · rw [he2]
      apply kernel_ordered_eval_zero node J P hP hip hqk hiq hik hpq hpk
      rw [hreverseRight i p k q]
      exact neg_ne_zero.mpr hJ
  · rw [he1]
    rcases lt_or_gt_of_ne hkq with hkq | hqk
    · apply kernel_ordered_eval_zero node J P hP hpi hkq hpk hpq hik hiq
      rw [hreverseLeft i p k q]
      exact neg_ne_zero.mpr hJ
    · rw [he2]
      apply kernel_ordered_eval_zero node J P hP hpi hqk hpq hpk hiq hik
      rw [hreverseLeft i p q k, hreverseRight i p k q, neg_neg]
      exact hJ

end Paper170

end
end

section

/-! The local test polynomial reduces the global tensor sum to its adjacent-edge pairings. -/
noncomputable section
open scoped BigOperators
namespace Paper170

theorem evalFour_liftUnivariate (x u y v : ℝ) (i : Fin 4) (U : Polynomial ℝ) :
    evalFour x u y v (liftUnivariate i U) = U.eval (![x,u,y,v] i) := by
  change MvPolynomial.aeval ![x,u,y,v] (Polynomial.aeval (MvPolynomial.X i) U) = _
  rw [← Polynomial.aeval_algHom_apply]
  simp

theorem evalFour_liftBivariate13 (x u y v : ℝ) (B : Poly2) :
    evalFour x u y v (liftBivariate 1 3 B) = evalTwo u v B := by
  have h : (MvPolynomial.aeval ![x,u,y,v]).comp
      (MvPolynomial.aeval ![MvPolynomial.X 1,MvPolynomial.X 3] : Poly2 →ₐ[ℝ] Poly4) =
      MvPolynomial.aeval ![u,v] := by
    ext i
    fin_cases i <;> simp
  exact congrArg (fun f : Poly2 →ₐ[ℝ] ℝ => f B) h

theorem evalFour_localTestPolynomial (x u y v : ℝ) (P : Poly4)
    (U V : Polynomial ℝ) (B : Poly2) :
    evalFour x u y v (localTestPolynomial P U V B) =
      evalFour x u y v P * (u-v) * (u-y) * (v-x) *
        U.eval x * V.eval y * evalTwo u v B := by
  have hm (Q R : Poly4) : evalFour x u y v (Q*R) = evalFour x u y v Q*evalFour x u y v R :=
    map_mul (MvPolynomial.aeval ![x,u,y,v]) Q R
  simp only [localTestPolynomial, hm, evalFour_liftUnivariate, evalFour_liftBivariate13]
  simp [evalFour]

def vertexTestSummand {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n) (H : Poly4)
    (i p k q : Fin n) : ℝ :=
  J i p k q * nodeWeight node i * nodeWeight node p * nodeWeight node k * nodeWeight node q *
    evalFour (node i) (node p) (node k) (node q) H

theorem vertexTestSummand_offDiagonal {n s : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (hloopLeft : ∀i k q, J i i k q=0) (hloopRight : ∀i p k, J i p k k=0)
    (hreverseLeft : ∀i p k q, J p i k q = -J i p k q)
    (hreverseRight : ∀i p k q, J i p q k = -J i p k q)
    (P : endpointSymmetricSpace s) (hP : supportEvaluation s node J P=0)
    (U V : Polynomial ℝ) (B : Poly2) (i p k q : Fin n) (hik : i≠k) :
    vertexTestSummand node J (localTestPolynomial P.val U V B) i p k q = 0 := by
  by_cases hip : i=p
  · subst p
    simp [vertexTestSummand, hloopLeft]
  by_cases hkq : k=q
  · subst q
    simp [vertexTestSummand, hloopRight]
  by_cases hpq : p=q
  · subst q
    simp [vertexTestSummand, evalFour_localTestPolynomial]
  by_cases hpk : p=k
  · subst k
    simp [vertexTestSummand, evalFour_localTestPolynomial]
  by_cases hiq : i=q
  · subst q
    simp [vertexTestSummand, evalFour_localTestPolynomial]
  by_cases hJ : J i p k q=0
  · simp [vertexTestSummand, hJ]
  have hz := kernel_independent_eval_zero node J hreverseLeft hreverseRight P hP
    hip hkq hik hiq hpk hpq hJ
  simp [vertexTestSummand, evalFour_localTestPolynomial, hz]

theorem orderPairing_weight_form {ι : Type*} [Fintype ι] (node : ι → ℝ)
    (order : LinearOrder ι) (A B : Poly2) :
    orderPairing node order A B = ∑p, ∑q,
      halfOrder order p q * (node p-node q) * nodeWeight node p * nodeWeight node q *
        evalTwo (node p) (node q) A * evalTwo (node p) (node q) B := by
  simp only [orderPairing, weightedPairing, nodeWeight, div_eq_mul_inv, mul_inv]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem vertexTestSummand_diagonal {n : ℕ} (node : Fin n → ℝ)
    (hn : Function.Injective node) (J : CrossingTensor n)
    (orders : ∀i : Fin n, LinearOrder {j : Fin n // j≠i})
    (hlocal : ∀i (p q : {j : Fin n // j≠i}), J i p.val i q.val=halfOrder (orders i) p q)
    (P : Poly4) (U V : Polynomial ℝ) (B : Poly2) (i : Fin n)
    (p q : {j : Fin n // j≠i}) :
    vertexTestSummand node J (localTestPolynomial P U V B) i p.val i q.val =
      (nodeWeight node i)^2 * U.eval (node i) * V.eval (node i) *
      (halfOrder (orders i) p q * (node p.val-node q.val) *
        nodeWeight (fun j : {j : Fin n // j≠i} => node j.val) p *
        nodeWeight (fun j : {j : Fin n // j≠i} => node j.val) q *
        evalTwo (node p.val) (node q.val) (vertexSpecialization (node i) P) *
        evalTwo (node p.val) (node q.val) B) := by
  rw [vertexTestSummand, evalFour_localTestPolynomial, hlocal]
  rw [neighbor_nodeWeight node hn, neighbor_nodeWeight node hn, vertex_eval]
  ring

theorem polynomialTest_local_reduction {n s : ℕ} (node : Fin n → ℝ)
    (hn : Function.Injective node) (J : CrossingTensor n)
    (orders : ∀i : Fin n, LinearOrder {j : Fin n // j≠i})
    (hloopLeft : ∀i k q, J i i k q=0) (hloopRight : ∀i p k, J i p k k=0)
    (hreverseLeft : ∀i p k q, J p i k q = -J i p k q)
    (hreverseRight : ∀i p k q, J i p q k = -J i p k q)
    (hlocal : ∀i (p q : {j : Fin n // j≠i}), J i p.val i q.val=halfOrder (orders i) p q)
    (P : endpointSymmetricSpace s) (hP : supportEvaluation s node J P=0)
    (U V : Polynomial ℝ) (B : Poly2) :
    polynomialTest node J (localTestPolynomial P.val U V B) =
      ∑i, (nodeWeight node i)^2 * U.eval (node i) * V.eval (node i) *
        orderPairing (fun j : {j : Fin n // j≠i} => node j.val) (orders i)
          (vertexSpecialization (node i) P.val) B := by
  change (∑i, ∑p, ∑k, ∑q, vertexTestSummand node J (localTestPolynomial P.val U V B) i p k q)=_
  apply Finset.sum_congr rfl
  intro i _
  have hk (p : Fin n) :
      (∑k, ∑q, vertexTestSummand node J (localTestPolynomial P.val U V B) i p k q) =
      ∑q, vertexTestSummand node J (localTestPolynomial P.val U V B) i p i q := by
    apply Finset.sum_eq_single i
    · intro k _ hki
      apply Finset.sum_eq_zero
      intro q _
      exact vertexTestSummand_offDiagonal node J hloopLeft hloopRight hreverseLeft hreverseRight
        P hP U V B i p k q hki.symm
    · simp
  simp_rw [hk]
  rw [sum_away i _ (by simp [vertexTestSummand,hloopLeft])]
  have hq (p : {j : Fin n // j≠i}) :
      (∑q, vertexTestSummand node J (localTestPolynomial P.val U V B) i p.val i q) =
      ∑q : {j : Fin n // j≠i}, vertexTestSummand node J (localTestPolynomial P.val U V B) i p.val i q.val :=
    sum_away i _ (by simp [vertexTestSummand,hloopRight])
  simp_rw [hq, vertexTestSummand_diagonal node hn J orders hlocal]
  rw [orderPairing_weight_form]
  simp only [Finset.mul_sum]

end Paper170

end
end

section

/-! Lagrange isolation of each vertex and the full kernel vertex-vanishing theorem. -/
noncomputable section
open scoped BigOperators
namespace Paper170

def vertexPairingFunctional {n : ℕ} (node : Fin n → ℝ)
    (orders : ∀i : Fin n, LinearOrder {j : Fin n // j≠i}) (P : Poly4) (B : Poly2) :
    Polynomial ℝ →ₗ[ℝ] ℝ :=
  ∑i, ((nodeWeight node i)^2 *
    orderPairing (fun j : {j : Fin n // j≠i} => node j.val) (orders i)
      (vertexSpecialization (node i) P) B) • (Polynomial.aeval (node i)).toLinearMap

theorem vertexPairingFunctional_apply {n : ℕ} (node : Fin n → ℝ)
    (orders : ∀i : Fin n, LinearOrder {j : Fin n // j≠i}) (P : Poly4) (B : Poly2)
    (W : Polynomial ℝ) :
    vertexPairingFunctional node orders P B W =
      ∑i, (nodeWeight node i)^2 * W.eval (node i) *
        orderPairing (fun j : {j : Fin n // j≠i} => node j.val) (orders i)
          (vertexSpecialization (node i) P) B := by
  simp only [vertexPairingFunctional, LinearMap.sum_apply, LinearMap.smul_apply,
    AlgHom.toLinearMap_apply, Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

section CrossingTensor
variable {s : ℕ} (hs : 2 ≤ s) (node : Fin (2*s+1) → ℝ)
    (hnode : Function.Injective node) (J : CrossingTensor (2*s+1))
    (orders : ∀i : Fin (2*s+1), LinearOrder {j : Fin (2*s+1) // j≠i})
    (hloopLeft : ∀i k q, J i i k q=0) (hloopRight : ∀i p k, J i p k k=0)
    (hreverseLeft : ∀i p k q, J p i k q = -J i p k q)
    (hreverseRight : ∀i p k q, J i p q k = -J i p k q)
    (hskew : ∀i p k q, J k q i p = -J i p k q)
    (hlocal : ∀i (p q : {j : Fin (2*s+1) // j≠i}), J i p.val i q.val=halfOrder (orders i) p q)
    (htests : ∀H ∈ box4 (2*s-1), polynomialTest node J H=0)

include hs hnode hloopLeft hloopRight hreverseLeft hreverseRight hlocal htests in
theorem vertexPairingFunctional_zero (P : endpointSymmetricSpace s)
    (hP : supportEvaluation s node J P=0) (B : Poly2) (hB : B∈rectangle (s-1) (s-1))
    (W : Polynomial ℝ) (hW : W∈Polynomial.degreeLT ℝ (2*s+1)) :
    vertexPairingFunctional node orders P.val B W=0 := by
  have hspan : Submodule.span ℝ {Q : Polynomial ℝ | ∃U V : Polynomial ℝ,
      U.natDegree≤s ∧ V.natDegree≤s ∧ Q=U*V} ≤
        LinearMap.ker (vertexPairingFunctional node orders P.val B) := by
    rw [Submodule.span_le]
    rintro Q ⟨U,V,hU,hV,rfl⟩
    change vertexPairingFunctional node orders P.val B (U*V)=0
    have hz := htests (localTestPolynomial P.val U V B) (local_test_degree s hs P.val P.property U V hU hV B hB)
    rw [polynomialTest_local_reduction node hnode J orders hloopLeft hloopRight
      hreverseLeft hreverseRight hlocal P hP U V B] at hz
    rw [vertexPairingFunctional_apply]
    convert hz using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Polynomial.eval_mul]
    ring
  rw [products_span_degree] at hspan
  exact hspan hW

include hs hnode hloopLeft hloopRight hreverseLeft hreverseRight hlocal htests in
theorem kernel_local_pairing_zero (P : endpointSymmetricSpace s)
    (hP : supportEvaluation s node J P=0) (i : Fin (2*s+1)) (B : Poly2)
    (hB : B∈rectangle (s-1) (s-1)) :
    orderPairing (fun j : {j : Fin (2*s+1) // j≠i} => node j.val) (orders i)
      (vertexSpecialization (node i) P.val) B = 0 := by
  classical
  let W := Lagrange.basis Finset.univ node i
  have hW : W∈Polynomial.degreeLT ℝ (2*s+1) := by
    apply Polynomial.mem_degreeLT.mpr
    rw [Lagrange.degree_basis hnode.injOn (Finset.mem_univ i)]
    simp only [Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel_right]
    exact_mod_cast (show 2*s < 2*s+1 by omega)
  have hz := vertexPairingFunctional_zero hs node hnode J orders hloopLeft hloopRight
    hreverseLeft hreverseRight hlocal htests P hP B hB W hW
  rw [vertexPairingFunctional_apply] at hz
  have heq : (∑j, (nodeWeight node j)^2 * W.eval (node j) *
      orderPairing (fun k : {k : Fin (2*s+1) // k≠j} => node k.val) (orders j)
        (vertexSpecialization (node j) P.val) B) =
      (nodeWeight node i)^2 *
        orderPairing (fun j : {j : Fin (2*s+1) // j≠i} => node j.val) (orders i)
          (vertexSpecialization (node i) P.val) B := by
    rw [Finset.sum_eq_single i]
    · rw [show W.eval (node i)=1 from Lagrange.eval_basis_self hnode.injOn (Finset.mem_univ i), mul_one]
    · intro j _ hji
      rw [show W.eval (node j)=0 from Lagrange.eval_basis_of_ne hji.symm (Finset.mem_univ j)]
      simp
    · simp
  rw [heq] at hz
  exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 (weight_nonzero node hnode i))

include hs hnode orders hloopLeft hloopRight hreverseLeft hreverseRight hskew hlocal htests in
theorem kernel_vertex_vanishing (P : endpointSymmetricSpace s)
    (hP : supportEvaluation s node J P=0) : ∀i, vertexSpecialization (node i) P.val=0 := by
  have hlocal' : ∀j (p q : {j' : Fin (2*s+1) // j'≠j}),
      J j p.val j q.val=halfOrder (orders j) p q := by
    intro j p q
    by_cases hpq : p=q
    · subst q
      have hh := hskew j p.val j p.val
      have hz : J j p.val j p.val=0 := by linarith
      have hpp := @lt_irrefl _ (orders j).toPartialOrder.toPreorder p
      simp only [hz,halfOrder,ite_eq_right hpp]
    · exact hlocal j p q
  intro i
  apply order_detector s hs (by simp [Fintype.card_subtype_compl])
    (fun j : {j : Fin (2*s+1) // j≠i} => node j.val)
    (hnode.comp Subtype.val_injective) (orders i) _ (vertexSpecialization_rectangle s P (node i))
  intro B hB
  exact kernel_local_pairing_zero hs node hnode J orders hloopLeft hloopRight
    hreverseLeft hreverseRight hlocal' htests P hP i B hB

end CrossingTensor
end Paper170

end
end

end OAI

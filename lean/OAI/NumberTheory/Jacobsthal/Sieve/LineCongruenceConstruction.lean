import OAI.NumberTheory.Jacobsthal.Estimates.LineSubstitution
import OAI.NumberTheory.Jacobsthal.Partitions.CoefficientBoxCollision

namespace OAI

namespace Erdos970

section

namespace ErdosAuxiliaryPolynomial

abbrev ResidueSystem (P : Finset ℕ) (T : ∀ p : P, Finset (ZMod p.val)) (D : ℕ) :=
  ∀ p : P, ∀ _s : T p, Fin (D+1) → ZMod p.val

@[implicit_reducible]
noncomputable def residueFintype (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p)
    (T : ∀ p : P, Finset (ZMod p.val)) (D : ℕ) : Fintype (ResidueSystem P T D) := by
  letI (p : P) : NeZero p.val := ⟨Nat.ne_of_gt (hP p p.property)⟩
  exact inferInstance

theorem residueSystem_card (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p)
    (T : ∀ p : P, Finset (ZMod p.val)) (D : ℕ) :
    @Fintype.card (ResidueSystem P T D) (residueFintype P hP T D) =
      ∏ p : P, p.val^((D+1)*(T p).card) := by
  classical
  let (p : P) : NeZero p.val := ⟨Nat.ne_of_gt (hP p p.property)⟩
  change Fintype.card (∀ p : P, ∀ _s : T p, Fin (D+1) → ZMod p.val) = _
  simp [Fintype.card_pi,← pow_mul]

noncomputable def constraintMap (P : Finset ℕ) (T : ∀ p : P, Finset (ZMod p.val))
    (a : ∀ p : P, ZMod p.val) (D : ℕ) : (MonomialIndex D → ℤ) →+ ResidueSystem P T D where
  toFun v p s k := (lineSub (Int.castRingHom (ZMod p.val)) (a p) s.val (encode v)).coeff k
  map_zero' := by
    funext p s k
    simp [encode]
  map_add' v w := by
    funext p s k
    change (lineSub (Int.castRingHom (ZMod p.val)) (a p) s.val (encode (v+w))).coeff k =
      (lineSub (Int.castRingHom (ZMod p.val)) (a p) s.val (encode v)).coeff k +
      (lineSub (Int.castRingHom (ZMod p.val)) (a p) s.val (encode w)).coeff k
    rw [show encode (v+w) = encode v+encode w from (encodeHom D).map_add v w,
      map_add,Polynomial.coeff_add]

theorem exists_line_congruence_polynomial (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p)
    (T : ∀ p : P, Finset (ZMod p.val)) (a : ∀ p : P, ZMod p.val) (D H : ℕ)
    (hbox : (∏ p : P, p.val^((D+1)*(T p).card)) < (H+1)^((D+2).choose 2)) :
    ∃ Q : MvPolynomial (Fin 2) ℤ, Q ≠ 0 ∧ Q.totalDegree ≤ D ∧
      (∀ m : Fin 2 →₀ ℕ, |Q.coeff m| ≤ (H : ℤ)) ∧
      ∀ p : P, ∀ s : T p, lineSub (Int.castRingHom (ZMod p.val)) (a p) s.val Q = 0 := by
  classical
  let := residueFintype P hP T D
  have hc : Fintype.card (ResidueSystem P T D) < (H+1)^(Fintype.card (MonomialIndex D)) := by
    rw [residueSystem_card,monomialIndex_card]
    exact hbox
  obtain ⟨v,hv,hbound,hzero⟩ := exists_bounded_kernel_vector (constraintMap P T a D) H hc
  refine ⟨encode v,(encode_eq_zero_iff v).not.mpr hv,encode_degree_le v,
    encode_coefficient_bound v hbound,?_⟩
  intro p s
  apply lineSub_encode_eq_zero
  intro k
  have h := congrFun (congrFun (congrFun hzero p) s) k
  exact h

end ErdosAuxiliaryPolynomial

end

end Erdos970

end OAI

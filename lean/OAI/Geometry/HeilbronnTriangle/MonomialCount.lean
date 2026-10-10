import OAI.Geometry.HeilbronnTriangle.Definitions

namespace OAI


noncomputable section

namespace Problem355.Monomials

abbrev DegreeIndex (α : Type*) (d : ℕ) :=
  {m : α →₀ ℕ // m.degree = d}

instance degreeIndexFintype (α : Type*) [Fintype α] [DecidableEq α] (d : ℕ) :
    Fintype (DegreeIndex α d) :=
  Fintype.ofEquiv (Sym α d) (Sym.equivNatSum α d)

theorem card_degreeIndex (α : Type*) [Fintype α] [DecidableEq α] (d : ℕ) :
    Fintype.card (DegreeIndex α d) = Nat.choose (Fintype.card α + d - 1) d := by
  let e : Sym α d ≃ DegreeIndex α d := Sym.equivNatSum α d
  rw [← Fintype.card_congr e, Sym.card_sym_eq_choose]

theorem card_three_groups (d : ℕ) :
    Fintype.card (DegreeIndex (Fin (3 * d)) d) = Nat.choose (4 * d - 1) d := by
  rw [card_degreeIndex, Fintype.card_fin]
  congr 2
  omega

def degreeEquivFin (d : ℕ) :
    DegreeIndex (Fin (3 * d)) d ≃ Fin (Nat.choose (4 * d - 1) d) :=
  Fintype.equivFinOfCardEq (card_three_groups d)

def coordinateDegreeEquivFin (d : ℕ) :
    DegreeIndex (Fin 3 × Fin d) d ≃ Fin (Nat.choose (4 * d - 1) d) :=
  Fintype.equivFinOfCardEq (by
    rw [card_degreeIndex, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    congr 2
    omega)

def heilbronnMonomialEquiv :
    DegreeIndex (Fin (3 * heilbronnD)) heilbronnD ≃ Fin heilbronnM :=
  degreeEquivFin heilbronnD

def heilbronnCoordinateMonomialEquiv :
    DegreeIndex (Fin 3 × Fin heilbronnD) heilbronnD ≃ Fin heilbronnM :=
  coordinateDegreeEquivFin heilbronnD

theorem card_heilbronn_triples :
    Fintype.card {s : Finset (DegreeIndex (Fin (3 * heilbronnD)) heilbronnD) //
      s.card = 3} = heilbronnT := by
  rw [Fintype.card_finset_len, card_three_groups]
  rfl

def heilbronnTripleEquiv :
    {s : Finset (DegreeIndex (Fin (3 * heilbronnD)) heilbronnD) // s.card = 3} ≃
      Fin heilbronnT :=
  Fintype.equivFinOfCardEq card_heilbronn_triples

theorem card_increasing_triples (M : ℕ) :
    Fintype.card (Fin 3 ↪o Fin M) = Nat.choose M 3 := by
  let e : (Fin 3 ↪o Fin M) ≃ {s : Finset (Fin M) // s.card = 3} :=
    Set.powersetCard.ofFinEmbEquiv
  rw [Fintype.card_congr e, Fintype.card_finset_len, Fintype.card_fin]

def heilbronnIncreasingTripleEquiv : (Fin 3 ↪o Fin heilbronnM) ≃ Fin heilbronnT :=
  Fintype.equivFinOfCardEq (card_increasing_triples heilbronnM)

abbrev IncreasingTriple (α : Type*) [LT α] :=
  {t : α × α × α // t.1 < t.2.1 ∧ t.2.1 < t.2.2}

def increasingTripleEquivEmbedding (α : Type*) [LinearOrder α] :
    IncreasingTriple α ≃ (Fin 3 ↪o α) where
  toFun t := OrderEmbedding.ofStrictMono ![t.val.1, t.val.2.1, t.val.2.2] (by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [Fin.lt_def] at hij
    · exact t.property.1
    · exact lt_trans t.property.1 t.property.2
    · exact t.property.2)
  invFun f := ⟨(f 0, f 1, f 2), f.strictMono (by decide), f.strictMono (by decide)⟩
  left_inv t := by cases t; rfl
  right_inv f := by ext i; fin_cases i <;> rfl

def heilbronnIncreasingTupleEquiv : IncreasingTriple (Fin heilbronnM) ≃ Fin heilbronnT :=
  (increasingTripleEquivEmbedding _).trans heilbronnIncreasingTripleEquiv

theorem homogeneous_expansion {α R : Type*} [Fintype α] [DecidableEq α]
    [CommSemiring R] {d : ℕ} (p : MvPolynomial α R) (hp : p.IsHomogeneous d) :
    p = ∑ m : DegreeIndex α d, MvPolynomial.monomial m.val (p.coeff m.val) := by
  classical
  ext m
  rw [MvPolynomial.coeff_sum]
  by_cases hm : m.degree = d
  · let x : DegreeIndex α d := ⟨m, hm⟩
    rw [Finset.sum_eq_single x]
    · simp [x]
    · intro b _ hbx
      rw [MvPolynomial.coeff_monomial]
      split_ifs with h
      · exact False.elim (hbx (Subtype.ext h))
      · rfl
    · simp
  · rw [hp.coeff_eq_zero hm]
    symm
    apply Finset.sum_eq_zero
    intro b _
    rw [MvPolynomial.coeff_monomial]
    split_ifs with h
    · exact False.elim (hm (h ▸ b.property))
    · rfl

theorem homogeneous_expansion_fin {R : Type*} [CommSemiring R] (d : ℕ)
    (p : MvPolynomial (Fin (3 * d)) R) (hp : p.IsHomogeneous d) :
    p = ∑ i : Fin (Nat.choose (4 * d - 1) d),
      MvPolynomial.monomial ((degreeEquivFin d).symm i).val
        (p.coeff ((degreeEquivFin d).symm i).val) := by
  calc
    p = ∑ m : DegreeIndex (Fin (3 * d)) d,
        MvPolynomial.monomial m.val (p.coeff m.val) :=
      homogeneous_expansion p hp
    _ = _ := (Equiv.sum_comp (degreeEquivFin d).symm
      (fun m : DegreeIndex (Fin (3 * d)) d =>
        MvPolynomial.monomial m.val (p.coeff m.val))).symm

theorem homogeneous_eval_expansion {α R : Type*} [Fintype α] [DecidableEq α]
    [CommSemiring R] {d : ℕ} (p : MvPolynomial α R) (hp : p.IsHomogeneous d)
    (x : α → R) :
    MvPolynomial.eval x p = ∑ m : DegreeIndex α d,
      p.coeff m.val * m.val.prod (fun a n => x a ^ n) := by
  conv_lhs => rw [homogeneous_expansion p hp]
  simp only [map_sum, MvPolynomial.eval_monomial]

end Problem355.Monomials

end

end OAI

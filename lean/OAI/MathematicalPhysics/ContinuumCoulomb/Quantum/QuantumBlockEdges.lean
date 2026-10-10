import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBlockFull

namespace OAI

/-! An explicit finite list of physical exchanges, with no implicit many-body terms. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ τ : Type*} [Fintype κ] [Fintype τ]

def qmaFieldEdgeRight (k : Fin 3) : Fin 4 := ![3,2,1] k

def qmaFieldEdgeWeight (a : Fin 2) (t : ℝ) (k : Fin 3) : ℝ :=
  if a = 0 then ![t/(2*Real.sqrt 3),-t/(2*Real.sqrt 3),0] k else ![0,0,-t/2] k

theorem qmaFieldEdgeRight_ne (k : Fin 3) : (0:Fin 4) ≠ qmaFieldEdgeRight k := by
  fin_cases k <;> decide

theorem qmaBlockSourceAxisField_edges (i : Fin n) (a : Fin 2) (t : ℝ) :
    qmaBlockSourceAxisField i a t = ∑ k : Fin 3, (qmaFieldEdgeWeight a t k:ℂ) •
      sourceHeisenbergMatrix (n*4) (finProdFinEquiv (i,0)) (finProdFinEquiv (i,qmaFieldEdgeRight k)) := by
  unfold qmaBlockSourceAxisField qmaFieldEdgeWeight
  split_ifs <;>
    simp only [qmaFieldEdgeRight,Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,
      Matrix.cons_val_succ,add_zero,qmaBlockSourceField,zero_div,Complex.ofReal_zero,
      zero_smul,sub_zero,zero_sub,zero_add,neg_div,Complex.ofReal_neg,neg_smul]
  · rw [smul_sub]
    rw [sub_eq_add_neg]

abbrev QMAFourExchangeIndex (n : ℕ) (κ τ : Type*) :=
  (Fin n × Fin 6) ⊕ ((κ × Fin 4 × Fin 4) ⊕ ((κ × Fin 2 × Fin 3) ⊕ (τ × Fin 3)))

def qmaFourExchangeLeft (left right : κ → Fin n) (site : τ → Fin n) :
    QMAFourExchangeIndex n κ τ → Fin (n*4)
  | .inl (i,k) => finProdFinEquiv (i,qmaFourEdgeLeft k)
  | .inr (.inl (e,p,_)) => finProdFinEquiv (left e,p)
  | .inr (.inr (.inl (e,s,_))) => finProdFinEquiv ((if s = 0 then left e else right e),0)
  | .inr (.inr (.inr (e,_))) => finProdFinEquiv (site e,0)

def qmaFourExchangeRight (left right : κ → Fin n) (site : τ → Fin n) :
    QMAFourExchangeIndex n κ τ → Fin (n*4)
  | .inl (i,k) => finProdFinEquiv (i,qmaFourEdgeRight k)
  | .inr (.inl (e,_,q)) => finProdFinEquiv (right e,q)
  | .inr (.inr (.inl (e,s,k))) => finProdFinEquiv ((if s = 0 then left e else right e),qmaFieldEdgeRight k)
  | .inr (.inr (.inr (e,k))) => finProdFinEquiv (site e,qmaFieldEdgeRight k)

def qmaFourExchangeWeight (r : ℝ) (a b : κ → Fin 2) (t : κ → ℝ)
    (axis : τ → Fin 2) (weight : τ → ℝ) : QMAFourExchangeIndex n κ τ → ℝ
  | .inl _ => r^2
  | .inr (.inl (e,p,q)) => r*qmaFourCouplingSize (a e) (b e) (t e)*
      (qmaFourAxisWeights (a e) true p*qmaFourAxisWeights (b e) (qmaFourCouplingSign (t e)) q)
  | .inr (.inr (.inl (e,s,k))) => if s = 0 then
      qmaFieldEdgeWeight (a e) (qmaFourCounterA (a e) (b e) (t e)) k else
      qmaFieldEdgeWeight (b e) (qmaFourCounterB (a e) (b e) (t e)) k
  | .inr (.inr (.inr (e,k))) => qmaFieldEdgeWeight (axis e) (weight e) k

omit [Fintype κ] [Fintype τ] in
theorem qmaFourExchange_distinct (left right : κ → Fin n) (site : τ → Fin n)
    (hne : ∀ e, left e ≠ right e) (x : QMAFourExchangeIndex n κ τ) :
    qmaFourExchangeLeft left right site x ≠ qmaFourExchangeRight left right site x := by
  cases x with
  | inl x =>
    intro h
    exact qmaFourEdge_distinct x.2 (congrArg Prod.snd (finProdFinEquiv.injective h))
  | inr x =>
    cases x with
    | inl x =>
      intro h
      exact hne x.1 (congrArg Prod.fst (finProdFinEquiv.injective h))
    | inr x =>
      cases x with
      | inl x =>
        intro h
        exact qmaFieldEdgeRight_ne x.2.2 (congrArg Prod.snd (finProdFinEquiv.injective h))
      | inr x =>
        intro h
        exact qmaFieldEdgeRight_ne x.2 (congrArg Prod.snd (finProdFinEquiv.injective h))

theorem qmaFourExchange_count : Fintype.card (QMAFourExchangeIndex n κ τ) =
    6*n+22*Fintype.card κ+3*Fintype.card τ := by
  simp only [QMAFourExchangeIndex,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  omega

def qmaFourExchangeScalar (n : ℕ) (r : ℝ) (axis : τ → Fin 2) (weight : τ → ℝ) (constant : ℝ) : ℝ :=
  r^2*(n*6)+constant-qmaFourTensorFieldShift axis weight

theorem qmaFourExchange_sum (r : ℝ) (left right : κ → Fin n)
    (a b : κ → Fin 2) (t : κ → ℝ) (site : τ → Fin n) (axis : τ → Fin 2)
    (weight : τ → ℝ) (constant : ℝ) :
    (∑ x : QMAFourExchangeIndex n κ τ,
      (qmaFourExchangeWeight r a b t axis weight x:ℂ) • sourceHeisenbergMatrix (n*4)
        (qmaFourExchangeLeft left right site x) (qmaFourExchangeRight left right site x))+
      (qmaFourExchangeScalar n r axis weight constant:ℂ) • 1 =
        qmaBlockSourceFull r left right a b t site axis weight constant := by
  simp only [QMAFourExchangeIndex,Fintype.sum_sum_type,Fintype.sum_prod_type,
    qmaFourExchangeLeft,qmaFourExchangeRight,qmaFourExchangeWeight,
    qmaBlockSourceFull,qmaBlockSourcePenalty,qmaBlockSourceCoupling,
    qmaBlockSourceCounterterm,qmaBlockSourceOnsite,qmaBlockSourceAxisField_edges,
    Fin.sum_univ_two,ite_true,show (1:Fin 2) ≠ 0 by decide,ite_false]
  simp only [smul_add,Finset.smul_sum,smul_smul,Finset.sum_add_distrib,
    qmaFourExchangeScalar,Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_mul,
    Complex.ofReal_pow,Complex.ofReal_natCast,mul_assoc]
  module

end ContinuumCoulomb

end

end OAI

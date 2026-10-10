import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingBounds

namespace OAI

/-! The ordinary nine-edge crossing gadget, retaining arbitrary old graph terms. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix MediatorGraph
open scoped BigOperators Kronecker Classical
variable {ν : Type*} [Fintype ν]

def qmaCrossingBaseLeft {n : ℕ} (left : ν → Fin n) (site : Fin 4 → Fin n) : ν ⊕ Fin 4 → Fin n :=
  Sum.elim left (fun a => site (qmaCrossingLeft a))
def qmaCrossingBaseRight {n : ℕ} (right : ν → Fin n) (site : Fin 4 → Fin n) : ν ⊕ Fin 4 → Fin n :=
  Sum.elim right (fun a => site (qmaCrossingRight a))
def qmaCrossingBaseWeight (weight : ν → ℝ) (J K : ℝ) : ν ⊕ Fin 4 → ℝ :=
  Sum.elim weight (qmaCrossingWeight J K)

omit [Fintype ν] in
theorem qmaCrossingBase_distinct {n : ℕ} (left right : ν → Fin n)
    (hneq : ∀ a, left a ≠ right a) (site : Fin 4 → Fin n) (hsite : Function.Injective site) :
    ∀ a, qmaCrossingBaseLeft left site a ≠ qmaCrossingBaseRight right site a := by
  intro a
  cases a with
  | inl a => exact hneq a
  | inr a =>
    intro h
    have hh := hsite h
    fin_cases a <;> norm_num [qmaCrossingLeft,qmaCrossingRight] at hh

theorem qmaCrossingBase_matrix {n : ℕ} (left right : ν → Fin n) (weight : ν → ℝ)
    (constant J K : ℝ) (site : Fin 4 → Fin n) :
    qmaExchangeMatrix (qmaCrossingBaseLeft left site) (qmaCrossingBaseRight right site)
      (qmaCrossingBaseWeight weight J K) (constant+qmaCrossingOffset J K) =
    qmaExchangeMatrix left right weight constant + qmaCrossingCorrection site J K := by
  rw [qmaCrossingCorrection_exchange]
  simp only [qmaExchangeMatrix,Fintype.sum_sum_type,qmaCrossingBaseLeft,qmaCrossingBaseRight,
    qmaCrossingBaseWeight,Sum.elim_inl,Sum.elim_inr,Complex.ofReal_add,add_smul]
  abel

def qmaCrossingGraph {n : ℕ} (left right : ν → Fin n) (weight : ν → ℝ)
    (constant R J K : ℝ) (site : Fin 4 → Fin n) :
    Matrix (SourceSpinBasis (n+1*2)) (SourceSpinBasis (n+1*2)) ℂ :=
  qmaExchangeMatrix
    (qmaStarGraphLeft (qmaCrossingBaseLeft left site) (0:Fin 1) site)
    (qmaStarGraphRight (qmaCrossingBaseRight right site) (0:Fin 1) qmaCrossingMember)
    (qmaStarGraphWeight (qmaCrossingBaseWeight weight J K) (R^2) (qmaCrossingAmplitude R J K))
    ((constant+qmaCrossingOffset J K)+3*1*(R^2))

theorem qmaCrossingGraph_matrix {n : ℕ} (left right : ν → Fin n)
    (hneq : ∀ a, left a ≠ right a) (weight : ν → ℝ) (constant R J K : ℝ)
    (site : Fin 4 → Fin n) (hsite : Function.Injective site) :
    (qmaCrossingGraph left right weight constant R J K site).submatrix
      (basisEquiv n 1) (basisEquiv n 1) =
      qmaPhysicalRoutingHamiltonian n 1 (R^2)
        (qmaExchangeMatrix left right weight constant+qmaCrossingCorrection site J K)
        0 site qmaCrossingMember (qmaCrossingAmplitude R J K) := by
  unfold qmaCrossingGraph
  simpa only [Nat.cast_one,qmaCrossingBase_matrix] using
    qmaStarGraph_matrix (r := 1) _ _ (qmaCrossingBase_distinct left right hneq site hsite)
      (qmaCrossingBaseWeight weight J K) (constant+qmaCrossingOffset J K) (R^2)
      0 site qmaCrossingMember (qmaCrossingAmplitude R J K)

theorem qmaCrossingGraph_bottom {n : ℕ} (left right : ν → Fin n)
    (hneq : ∀ a, left a ≠ right a) (weight : ν → ℝ) (constant R J K : ℝ)
    (site : Fin 4 → Fin n) (hsite : Function.Injective site) (hR : 0 < R)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1/4)
    (hbound : ‖spinMatrixOperator
      ((qmaExchangeMatrix left right weight constant+qmaCrossingCorrection site J K) ⊗ₖ
        (1 : Matrix (MediatorBasis 1) (MediatorBasis 1) ℂ))‖ +
      3*∑ a, |qmaCrossingAmplitude R J K a| ≤ epsilon*(4*R^2)) :
    |sourceMatrixBottom (n+1*2) (qmaCrossingGraph left right weight constant R J K site) -
      sourceMatrixBottom n (qmaExchangeMatrix left right weight constant +
        ((J:ℂ) • sourceHeisenbergMatrix n (site 0) (site 2) +
          (K:ℂ) • sourceHeisenbergMatrix n (site 1) (site 3)))| ≤ 16*R^2*epsilon^3 := by
  rw [sourceMatrixBottom_eq_mediator n 1,qmaCrossingGraph_matrix left right hneq weight constant R J K site hsite]
  have hC : (qmaExchangeMatrix left right weight constant).conjTranspose =
      qmaExchangeMatrix left right weight constant := by
    simp only [qmaExchangeMatrix,Matrix.conjTranspose_add,Matrix.conjTranspose_sum,
      Matrix.conjTranspose_smul,sourceHeisenbergMatrix_star n _ _ (hneq _),
      Complex.star_def,Complex.conj_ofReal,Matrix.conjTranspose_one]
  exact qmaPhysicalCrossing_bottom 0 site hsite R J K hR _ hC hepsilon hsmall hbound

end ContinuumCoulomb

end

end OAI

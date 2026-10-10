import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumExchangeRounding
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumXZHeisenberg

namespace OAI

/-! A rational finite Heisenberg family with controlled error, before lattice routing. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ τ : Type*} [Fintype κ] [Fintype τ]

theorem qmaBlockSourceFull_exchange (r : ℝ) (left right : κ → Fin n)
    (a b : κ → Fin 2) (t : κ → ℝ) (site : τ → Fin n) (axis : τ → Fin 2)
    (weight : τ → ℝ) (constant : ℝ) :
    qmaBlockSourceFull r left right a b t site axis weight constant =
      qmaExchangeMatrix (qmaFourExchangeLeft left right site) (qmaFourExchangeRight left right site)
        (qmaFourExchangeWeight r a b t axis weight) (qmaFourExchangeScalar n r axis weight constant) :=
  (qmaFourExchange_sum r left right a b t site axis weight constant).symm

theorem qmaBlock_rational_accuracy (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ)
    (hneq : ∀ e, left e ≠ right e)
    (hdist : ∀ e f, e ≠ f → ({left e,right e} : Finset (Fin n)) ≠ {left f,right f})
    (site : τ → Fin n) (axis : τ → Fin 2) (weight : τ → ℝ) (constant : ℝ) (N : ℕ) (hN : 0 < N) :
    let r := 9*(qmaFourTensorFullBudget t weight constant)^3*N
    let m := (3*Fintype.card (QMAFourExchangeIndex n κ τ)+1)*N
    let J := fun x => qmaRationalRound m (qmaFourExchangeWeight r a b t axis weight x)
    let s := qmaRationalRound m (qmaFourExchangeScalar n r axis weight constant)
    |MediatorGraph.normalizedBottom (qmaExchangeMatrix
        (qmaFourExchangeLeft left right site) (qmaFourExchangeRight left right site) (fun x => (J x:ℝ)) (s:ℝ))-
      MediatorGraph.normalizedBottom (qmaFourTensorFullTarget left right a b t site axis weight constant)| ≤
        2/(N:ℝ) := by
  dsimp only
  let r := 9*(qmaFourTensorFullBudget t weight constant)^3*N
  have hphys := qmaBlockSourceFull_accuracy left right a b t hneq hdist site axis weight constant N hN
  have hround := qmaExchangeMatrix_round_accuracy
    (qmaFourExchangeLeft left right site) (qmaFourExchangeRight left right site)
    (qmaFourExchange_distinct left right site hneq)
    (qmaFourExchangeWeight r a b t axis weight)
    (qmaFourExchangeScalar n r axis weight constant) N hN
  dsimp only at hround
  rw [← qmaBlockSourceFull_exchange r left right a b t site axis weight constant] at hround
  rw [abs_sub_comm] at hround
  exact (abs_sub_le _ _ _).trans ((add_le_add hround hphys).trans_eq (by ring))

theorem qmaXZ_rational_heisenberg (t : κ → QMAXZTerm n) (J : κ → ℝ)
    (hprivate : ∀ e f, (qmaPauliSupport (t e).word).card = 2 →
      qmaPauliSupport (t e).word = qmaPauliSupport (t f).word → e = f)
    (N : ℕ) (hN : 0 < N) :
    ∃ (left right : QMAFourExchangeIndex n (QMAXZPairIndex t) (QMAXZFieldIndex t) → Fin (n*4))
      (weight : QMAFourExchangeIndex n (QMAXZPairIndex t) (QMAXZFieldIndex t) → ℚ) (s : ℚ),
      (∀ e, left e ≠ right e) ∧
      |MediatorGraph.normalizedBottom (qmaExchangeMatrix left right (fun e => (weight e:ℝ)) (s:ℝ))-
        MediatorGraph.normalizedBottom (∑ e, (J e:ℂ) • (t e).matrix)| ≤ 2/(N:ℝ) := by
  let left := fun e => (qmaXZPairData t e).left
  let right := fun e => (qmaXZPairData t e).right
  let a := fun e => (qmaXZPairData t e).axisLeft
  let b := fun e => (qmaXZPairData t e).axisRight
  let site := fun e => (qmaXZFieldData t e).site
  let axis := fun e => (qmaXZFieldData t e).axis
  let r := 9*(qmaXZBlockBudget t J)^3*N
  let m := (3*Fintype.card (QMAFourExchangeIndex n (QMAXZPairIndex t) (QMAXZFieldIndex t))+1)*N
  refine ⟨qmaFourExchangeLeft left right site,qmaFourExchangeRight left right site,
    (fun x => qmaRationalRound m (qmaFourExchangeWeight r a b (fun e => J e.val) axis (fun e => J e.val) x)),
    qmaRationalRound m (qmaFourExchangeScalar n r axis (fun e => J e.val) (qmaXZFamilyConstant t J)),?_,?_⟩
  · exact qmaFourExchange_distinct left right site (fun e => (qmaXZPairData t e).distinct)
  · have h := qmaBlock_rational_accuracy left right a b (fun e => J e.val)
      (fun e => (qmaXZPairData t e).distinct)
      (fun e f hef => qmaXZPairData_distinct t hprivate e f hef)
      site axis (fun e => J e.val) (qmaXZFamilyConstant t J) N hN
    change |_-MediatorGraph.normalizedBottom (qmaFourTensorFullTarget left right a b
      (fun e => J e.val) site axis (fun e => J e.val) (qmaXZFamilyConstant t J))| ≤ _ at h
    rw [qmaXZFamily_target] at h
    exact h

end ContinuumCoulomb

end

end OAI

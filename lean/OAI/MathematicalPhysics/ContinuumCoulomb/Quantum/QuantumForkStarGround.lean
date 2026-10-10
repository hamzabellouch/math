import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkStarIndex

namespace OAI

/-! Full-space degree reduction for a star with an arbitrary number of ports. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix MediatorGraph
open scoped BigOperators Kronecker Classical

theorem qmaForkStar_target (d : ℕ) (constant : ℝ) (J : Fin d → ℝ) :
    qmaExchangeMatrix (fun _ : Fin (d%2) => qmaForkCenter d)
        (fun k => qmaForkPort d (qmaForkPortEquiv d (.inr k)))
        (fun k => J (qmaForkPortEquiv d (.inr k))) constant +
      ∑ i, ((J (qmaForkPortEquiv d (.inl (i,0))):ℂ) •
          sourceHeisenbergMatrix (1+d) (qmaForkStarSite d i 0) (qmaForkStarSite d i 1) +
        (J (qmaForkPortEquiv d (.inl (i,1))):ℂ) •
          sourceHeisenbergMatrix (1+d) (qmaForkStarSite d i 0) (qmaForkStarSite d i 2)) =
      qmaExchangeMatrix (fun _ : Fin d => qmaForkCenter d) (qmaForkPort d) J constant := by
  have hs := (qmaForkPortEquiv d).sum_comp (fun j => (J j:ℂ) •
    sourceHeisenbergMatrix (1+d) (qmaForkCenter d) (qmaForkPort d j))
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type] at hs
  simp only [Fin.sum_univ_two] at hs
  simp only [qmaExchangeMatrix,qmaForkStarSite,Matrix.cons_val_zero]
  rw [← hs]
  abel

theorem qmaForkStar_accuracy (d : ℕ) (constant : ℝ) (J : Fin d → ℝ) {N : ℝ} (hN : 0 < N) :
    let B := 3*(∑ k : Fin (d%2), |J (qmaForkPortEquiv d (.inr k))|)+|constant|
    let A := 3*∑ i, (1+2*|J (qmaForkPortEquiv d (.inl (i,0)))|+
      2*|J (qmaForkPortEquiv d (.inl (i,1)))|)
    let D := B+12*∑ i, (1+|J (qmaForkPortEquiv d (.inl (i,0)))|+
      |J (qmaForkPortEquiv d (.inl (i,1)))|)^2
    let R := qmaRoutingScale A D N
    |sourceMatrixBottom ((1+d)+(d/2)*2)
        (qmaExchangeMatrix (fun e => qmaForkStarEmbedding d (qmaForkStarLeft d e))
          (fun e => qmaForkStarEmbedding d (qmaForkStarRight d e)) (qmaForkStarWeight d R J)
          (qmaForkStarOffset d constant R J)) -
      sourceMatrixBottom (1+d)
        (qmaExchangeMatrix (fun _ : Fin d => qmaForkCenter d) (qmaForkPort d) J constant)| ≤ 1/N := by
  have hneq (k : Fin (d%2)) : qmaForkCenter d ≠ qmaForkPort d (qmaForkPortEquiv d (.inr k)) := by
    simp [qmaForkCenter,qmaForkPort]
  have h := qmaForksGraph_accuracy
    (fun _ : Fin (d%2) => qmaForkCenter d)
    (fun k => qmaForkPort d (qmaForkPortEquiv d (.inr k))) hneq
    (fun k => J (qmaForkPortEquiv d (.inr k))) constant
    (qmaForkStarSite d) (qmaForkStarSite_injective d)
    (fun i => J (qmaForkPortEquiv d (.inl (i,0))))
    (fun i => J (qmaForkPortEquiv d (.inl (i,1)))) hN
  dsimp only at h ⊢
  rw [← qmaForkStar_matrix,qmaForkStar_target] at h
  exact h

end ContinuumCoulomb

end

end OAI

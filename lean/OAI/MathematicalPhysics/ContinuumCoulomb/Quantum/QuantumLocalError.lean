import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumMatrixError

namespace OAI

/-! Local matrix errors are bounded independently of the number of
spectator qubits, including on entangled states. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical Kronecker

theorem qmaKronecker_one_action {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (A : Matrix α α ℂ) (u : α × β → ℂ) (p : α × β) :
    (A ⊗ₖ (1 : Matrix β β ℂ)).mulVec u p = A.mulVec (fun i => u (i,p.2)) p.1 := by
  simp [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Matrix.one_apply,
    mul_ite,ite_mul]

theorem qmaKronecker_one_quadratic {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (A : Matrix α α ℂ) (u : α × β → ℂ) :
    qmaQuadratic (A ⊗ₖ (1 : Matrix β β ℂ)) u = ∑ j : β, qmaQuadratic A (fun i => u (i,j)) := by
  simp only [qmaQuadratic,qmaKronecker_one_action,dotProduct,Fintype.sum_prod_type,
    Pi.star_apply,Complex.re_sum]
  rw [Finset.sum_comm]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qmaLocalLift_quadratic (S : Finset ι)
    (A : Matrix (QMASupportBasis S) (QMASupportBasis S) ℂ) (u : (ι → Fin 2) → ℂ) :
    qmaQuadratic (qmaLocalLift S A) u =
      ∑ r : QMASpectatorBasis S, qmaQuadratic A (fun s => u ((qmaSupportSplit S).symm (s,r))) := by
  let e := qmaSupportSplit S
  let v := u ∘ e.symm
  have he : v ∘ e = u := by funext i; simp [v]
  have h := qmaQuadratic_reindex e (A ⊗ₖ (1 : Matrix (QMASpectatorBasis S) (QMASpectatorBasis S) ℂ)) v
  rw [he,qmaKronecker_one_quadratic] at h
  exact h

theorem qmaLocalLift_entry_bound (S : Finset ι)
    (A : Matrix (QMASupportBasis S) (QMASupportBasis S) ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hA : ∀ i j, ‖A i j‖ ≤ B) (u : (ι → Fin 2) → ℂ) :
    |qmaQuadratic (qmaLocalLift S A) u| ≤ (2:ℝ)^S.card*B*(∑ i, ‖u i‖^2) := by
  rw [qmaLocalLift_quadratic]
  have hc : (Fintype.card (QMASupportBasis S):ℝ) = (2:ℝ)^S.card := by
    simp only [QMASupportBasis,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Nat.cast_pow,Nat.cast_ofNat]
  have hm : (∑ r : QMASpectatorBasis S, ∑ s : QMASupportBasis S,
      ‖u ((qmaSupportSplit S).symm (s,r))‖^2) = ∑ i, ‖u i‖^2 := by
    rw [Finset.sum_comm]
    have h := (qmaSupportSplit S).symm.sum_comp (fun i => ‖u i‖^2)
    simpa only [Fintype.sum_prod_type] using h
  calc
    _ ≤ ∑ r : QMASpectatorBasis S,
        |qmaQuadratic A (fun s => u ((qmaSupportSplit S).symm (s,r)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : QMASpectatorBasis S, (2:ℝ)^S.card*B*
        (∑ s : QMASupportBasis S, ‖u ((qmaSupportSplit S).symm (s,r))‖^2) := by
      apply Finset.sum_le_sum
      intro r _
      simpa only [hc] using qmaQuadratic_entry_bound A B hB hA
        (fun s => u ((qmaSupportSplit S).symm (s,r)))
    _ = _ := by rw [←Finset.mul_sum,hm]

end ContinuumCoulomb

end

end OAI

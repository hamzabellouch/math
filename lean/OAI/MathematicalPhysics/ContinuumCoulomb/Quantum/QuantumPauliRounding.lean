import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumExchangeRounding
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPauliAlgebra

namespace OAI

/-! Rounding a finite Pauli family controls its actual full-space ground energy. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

def qmaPauliFamily (w : κ → ι → Fin 4) (J : κ → ℝ) : Matrix (ι → Fin 2) (ι → Fin 2) ℂ :=
  ∑ e, (J e:ℂ) • qmaPauliWord (w e)

theorem qmaPauliFamily_norm (w : κ → ι → Fin 4) (J : κ → ℝ) :
    ‖spinMatrixOperator (qmaPauliFamily w J)‖ ≤ ∑ e, |J e| := by
  rw [qmaPauliFamily,spinMatrixOperator_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro e _
  rw [spinMatrixOperator_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left
    (spinMatrixOperator_unitary_norm _ (qmaPauliWord_gram _)) (abs_nonneg _)).trans_eq (mul_one _)

omit [DecidableEq ι] in
theorem qmaPauliFamily_sub (w : κ → ι → Fin 4) (J K : κ → ℝ) :
    qmaPauliFamily w J-qmaPauliFamily w K = qmaPauliFamily w (fun e => J e-K e) := by
  simp only [qmaPauliFamily,Complex.ofReal_sub,sub_smul,Finset.sum_sub_distrib]

theorem qmaPauliFamily_ground_error (w : κ → ι → Fin 4) (J K : κ → ℝ) :
    |MediatorGraph.normalizedBottom (qmaPauliFamily w J)-
      MediatorGraph.normalizedBottom (qmaPauliFamily w K)| ≤ ∑ e, |J e-K e| := by
  apply qmaNormalizedBottom_norm_error _ _
    (EuclideanSpace.single (fun _ => (0:Fin 2)) 1) (by simp [PiLp.norm_single])
  rw [qmaPauliFamily_sub]
  exact qmaPauliFamily_norm w _

theorem qmaPauliFamily_round_error (w : κ → ι → Fin 4) (J : κ → ℝ)
    (m : ℕ) (hm : 0 < m) :
    |MediatorGraph.normalizedBottom (qmaPauliFamily w J)-
      MediatorGraph.normalizedBottom (qmaPauliFamily w (fun e => (qmaRationalRound m (J e):ℝ)))| ≤
        (Fintype.card κ:ℝ)/(m:ℝ) := by
  apply (qmaPauliFamily_ground_error w J _).trans
  calc
    _ ≤ ∑ _e : κ, 1/(m:ℝ) :=
      Finset.sum_le_sum (fun e _ => qmaRationalRound_error m hm (J e))
    _ = _ := by simp [div_eq_mul_inv]

theorem qmaPauliFamily_round_accuracy (w : κ → ι → Fin 4) (J : κ → ℝ)
    (N : ℕ) (hN : 0 < N) :
    let m := (Fintype.card κ+1)*N
    |MediatorGraph.normalizedBottom (qmaPauliFamily w J)-
      MediatorGraph.normalizedBottom (qmaPauliFamily w (fun e => (qmaRationalRound m (J e):ℝ)))| ≤
        1/(N:ℝ) := by
  dsimp only
  have hm : 0 < (Fintype.card κ+1)*N := Nat.mul_pos (by omega) hN
  apply (qmaPauliFamily_round_error w J _ hm).trans
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hcard : (0:ℝ) < Fintype.card κ+1 := by positivity
  rw [Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  apply (div_le_iff₀ (mul_pos hcard hNR)).mpr
  field_simp
  linarith

end ContinuumCoulomb

end

end OAI

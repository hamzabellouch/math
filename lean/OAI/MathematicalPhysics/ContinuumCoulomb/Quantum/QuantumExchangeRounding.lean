import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBlockEdges
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGroundComparison

namespace OAI

/-! Rational coefficient rounding controls the full physical ground energy. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ : Type*} [Fintype κ]

def qmaExchangeMatrix (left right : κ → Fin n) (J : κ → ℝ) (constant : ℝ) :
    Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ :=
  (∑ e, (J e:ℂ) • sourceHeisenbergMatrix n (left e) (right e))+(constant:ℂ) • 1

theorem qmaExchangeMatrix_sub (left right : κ → Fin n) (J K : κ → ℝ) (s u : ℝ) :
    qmaExchangeMatrix left right J s-qmaExchangeMatrix left right K u =
      qmaExchangeMatrix left right (fun e => J e-K e) (s-u) := by
  simp only [qmaExchangeMatrix,Complex.ofReal_sub,sub_smul,Finset.sum_sub_distrib]
  abel

theorem qmaExchangeMatrix_norm (left right : κ → Fin n) (hne : ∀ e, left e ≠ right e)
    (J : κ → ℝ) (constant : ℝ) :
    ‖spinMatrixOperator (qmaExchangeMatrix left right J constant)‖ ≤
      3*(∑ e, |J e|)+|constant| := by
  have hI : ‖spinMatrixOperator (1 : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)‖ ≤ 1 := by
    apply spinMatrixOperator_unitary_norm
    simp
  have hs : ‖spinMatrixOperator ((∑ e, (J e:ℂ) • sourceHeisenbergMatrix n (left e) (right e)))‖ ≤
      3*(∑ e, |J e|) := by
    rw [spinMatrixOperator_sum,Finset.mul_sum]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro e _
    rw [spinMatrixOperator_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_comm]
    exact mul_le_mul_of_nonneg_right (sourceHeisenbergMatrix_operator_norm n _ _ (hne e)) (abs_nonneg _)
  rw [qmaExchangeMatrix,spinMatrixOperator_add]
  apply (norm_add_le _ _).trans
  rw [spinMatrixOperator_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs]
  have hc := mul_le_mul_of_nonneg_left hI (abs_nonneg constant)
  linarith

theorem qmaExchangeMatrix_ground_error (left right : κ → Fin n)
    (hne : ∀ e, left e ≠ right e) (J K : κ → ℝ) (s u : ℝ) :
    |MediatorGraph.normalizedBottom (qmaExchangeMatrix left right J s)-
      MediatorGraph.normalizedBottom (qmaExchangeMatrix left right K u)| ≤
        3*(∑ e, |J e-K e|)+|s-u| := by
  apply qmaNormalizedBottom_norm_error _ _ (EuclideanSpace.single (fun _ => 0) 1) (by simp [PiLp.norm_single])
  rw [qmaExchangeMatrix_sub]
  exact qmaExchangeMatrix_norm left right hne _ _

def qmaRationalRound (m : ℕ) (x : ℝ) : ℚ := (⌊(m:ℝ)*x⌋:ℚ)/(m:ℚ)

theorem qmaRationalRound_error (m : ℕ) (hm : 0 < m) (x : ℝ) :
    |x-(qmaRationalRound m x:ℝ)| ≤ 1/(m:ℝ) := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have ha : 0 ≤ (m:ℝ)*x-(⌊(m:ℝ)*x⌋:ℝ) := sub_nonneg.mpr (Int.floor_le _)
  have hb : (m:ℝ)*x-(⌊(m:ℝ)*x⌋:ℝ) ≤ 1 := by
    have h := Int.lt_floor_add_one ((m:ℝ)*x)
    linarith
  have he : x-(qmaRationalRound m x:ℝ) = ((m:ℝ)*x-(⌊(m:ℝ)*x⌋:ℝ))/(m:ℝ) := by
    simp only [qmaRationalRound,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast]
    field_simp
  rw [he,abs_of_nonneg (div_nonneg ha hmR.le)]
  exact div_le_div_of_nonneg_right hb hmR.le

theorem qmaRationalRound_abs (m : ℕ) (hm : 0 < m) (x : ℝ) :
    |(qmaRationalRound m x:ℝ)| ≤ |x|+1/(m:ℝ) := by
  have h := qmaRationalRound_error m hm x
  calc
    _ = |x+((qmaRationalRound m x:ℝ)-x)| := by congr 1; ring
    _ ≤ |x|+|(qmaRationalRound m x:ℝ)-x| := abs_add_le _ _
    _ = |x|+|x-(qmaRationalRound m x:ℝ)| := by rw [abs_sub_comm]
    _ ≤ _ := add_le_add le_rfl h

theorem qmaExchangeMatrix_round_error (left right : κ → Fin n) (hne : ∀ e, left e ≠ right e)
    (J : κ → ℝ) (constant : ℝ) (m : ℕ) (hm : 0 < m) :
    |MediatorGraph.normalizedBottom (qmaExchangeMatrix left right J constant)-
      MediatorGraph.normalizedBottom (qmaExchangeMatrix left right
        (fun e => (qmaRationalRound m (J e):ℝ)) (qmaRationalRound m constant:ℝ))| ≤
          (3*(Fintype.card κ:ℝ)+1)/(m:ℝ) := by
  apply (qmaExchangeMatrix_ground_error left right hne _ _ _ _).trans
  have hs : (∑ e, |J e-(qmaRationalRound m (J e):ℝ)|) ≤ (Fintype.card κ:ℝ)/(m:ℝ) := by
    calc
      _ ≤ ∑ _e : κ, 1/(m:ℝ) := Finset.sum_le_sum (fun e _ => qmaRationalRound_error m hm (J e))
      _ = _ := by simp [div_eq_mul_inv]
  have hc := qmaRationalRound_error m hm constant
  calc
    _ ≤ 3*((Fintype.card κ:ℝ)/(m:ℝ))+1/(m:ℝ) := by linarith
    _ = _ := by ring

theorem qmaExchangeMatrix_round_accuracy (left right : κ → Fin n) (hne : ∀ e, left e ≠ right e)
    (J : κ → ℝ) (constant : ℝ) (N : ℕ) (hN : 0 < N) :
    let m := (3*Fintype.card κ+1)*N
    |MediatorGraph.normalizedBottom (qmaExchangeMatrix left right J constant)-
      MediatorGraph.normalizedBottom (qmaExchangeMatrix left right
        (fun e => (qmaRationalRound m (J e):ℝ)) (qmaRationalRound m constant:ℝ))| ≤ 1/(N:ℝ) := by
  dsimp only
  have hm : 0 < (3*Fintype.card κ+1)*N := Nat.mul_pos (by omega) hN
  have h := qmaExchangeMatrix_round_error left right hne J constant _ hm
  have hden : (3*(Fintype.card κ:ℝ)+1) ≠ 0 := by positivity
  have hNR : (N:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  convert h using 1
  push_cast
  field_simp

end ContinuumCoulomb

end

end OAI

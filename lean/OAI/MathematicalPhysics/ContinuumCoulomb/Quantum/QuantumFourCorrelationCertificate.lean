import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourSpinTable

namespace OAI

/-! Exact rational spin correlations in the two-column singlet code. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaFourRawCorrelation (i j : Fin 4) : Matrix (Fin 2) (Fin 2) ℚ :=
  if i = j then Matrix.diagonal ![4,12]
  else (1/3:ℚ) • (Matrix.diagonal ![4,12]*qmaFourRawLogical (min i j) (max i j))

theorem qmaFourRawCorrelation_000 (ν : Fin 3) :
    (qmaFourSpinRawAction 0 0).transpose*qmaFourSpinRawAction 0 ν =
      if (0:Fin 3) = ν then qmaFourRawCorrelation 0 0 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_001 (ν : Fin 3) :
    (qmaFourSpinRawAction 0 1).transpose*qmaFourSpinRawAction 0 ν =
      if (1:Fin 3) = ν then qmaFourRawCorrelation 0 0 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_002 (ν : Fin 3) :
    (qmaFourSpinRawAction 0 2).transpose*qmaFourSpinRawAction 0 ν =
      if (2:Fin 3) = ν then qmaFourRawCorrelation 0 0 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_010 (ν : Fin 3) :
    (qmaFourSpinRawAction 0 0).transpose*qmaFourSpinRawAction 1 ν =
      if (0:Fin 3) = ν then qmaFourRawCorrelation 0 1 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_011 (ν : Fin 3) :
    (qmaFourSpinRawAction 0 1).transpose*qmaFourSpinRawAction 1 ν =
      if (1:Fin 3) = ν then qmaFourRawCorrelation 0 1 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_012 (ν : Fin 3) :
    (qmaFourSpinRawAction 0 2).transpose*qmaFourSpinRawAction 1 ν =
      if (2:Fin 3) = ν then qmaFourRawCorrelation 0 1 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_020 (ν : Fin 3) :
    (qmaFourSpinRawAction 0 0).transpose*qmaFourSpinRawAction 2 ν =
      if (0:Fin 3) = ν then qmaFourRawCorrelation 0 2 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_021 (ν : Fin 3) :
    (qmaFourSpinRawAction 0 1).transpose*qmaFourSpinRawAction 2 ν =
      if (1:Fin 3) = ν then qmaFourRawCorrelation 0 2 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_022 (ν : Fin 3) :
    (qmaFourSpinRawAction 0 2).transpose*qmaFourSpinRawAction 2 ν =
      if (2:Fin 3) = ν then qmaFourRawCorrelation 0 2 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_030 (ν : Fin 3) :
    (qmaFourSpinRawAction 0 0).transpose*qmaFourSpinRawAction 3 ν =
      if (0:Fin 3) = ν then qmaFourRawCorrelation 0 3 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_031 (ν : Fin 3) :
    (qmaFourSpinRawAction 0 1).transpose*qmaFourSpinRawAction 3 ν =
      if (1:Fin 3) = ν then qmaFourRawCorrelation 0 3 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_032 (ν : Fin 3) :
    (qmaFourSpinRawAction 0 2).transpose*qmaFourSpinRawAction 3 ν =
      if (2:Fin 3) = ν then qmaFourRawCorrelation 0 3 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_100 (ν : Fin 3) :
    (qmaFourSpinRawAction 1 0).transpose*qmaFourSpinRawAction 0 ν =
      if (0:Fin 3) = ν then qmaFourRawCorrelation 1 0 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_101 (ν : Fin 3) :
    (qmaFourSpinRawAction 1 1).transpose*qmaFourSpinRawAction 0 ν =
      if (1:Fin 3) = ν then qmaFourRawCorrelation 1 0 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_102 (ν : Fin 3) :
    (qmaFourSpinRawAction 1 2).transpose*qmaFourSpinRawAction 0 ν =
      if (2:Fin 3) = ν then qmaFourRawCorrelation 1 0 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_110 (ν : Fin 3) :
    (qmaFourSpinRawAction 1 0).transpose*qmaFourSpinRawAction 1 ν =
      if (0:Fin 3) = ν then qmaFourRawCorrelation 1 1 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_111 (ν : Fin 3) :
    (qmaFourSpinRawAction 1 1).transpose*qmaFourSpinRawAction 1 ν =
      if (1:Fin 3) = ν then qmaFourRawCorrelation 1 1 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_112 (ν : Fin 3) :
    (qmaFourSpinRawAction 1 2).transpose*qmaFourSpinRawAction 1 ν =
      if (2:Fin 3) = ν then qmaFourRawCorrelation 1 1 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_120 (ν : Fin 3) :
    (qmaFourSpinRawAction 1 0).transpose*qmaFourSpinRawAction 2 ν =
      if (0:Fin 3) = ν then qmaFourRawCorrelation 1 2 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_121 (ν : Fin 3) :
    (qmaFourSpinRawAction 1 1).transpose*qmaFourSpinRawAction 2 ν =
      if (1:Fin 3) = ν then qmaFourRawCorrelation 1 2 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_122 (ν : Fin 3) :
    (qmaFourSpinRawAction 1 2).transpose*qmaFourSpinRawAction 2 ν =
      if (2:Fin 3) = ν then qmaFourRawCorrelation 1 2 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_130 (ν : Fin 3) :
    (qmaFourSpinRawAction 1 0).transpose*qmaFourSpinRawAction 3 ν =
      if (0:Fin 3) = ν then qmaFourRawCorrelation 1 3 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_131 (ν : Fin 3) :
    (qmaFourSpinRawAction 1 1).transpose*qmaFourSpinRawAction 3 ν =
      if (1:Fin 3) = ν then qmaFourRawCorrelation 1 3 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_132 (ν : Fin 3) :
    (qmaFourSpinRawAction 1 2).transpose*qmaFourSpinRawAction 3 ν =
      if (2:Fin 3) = ν then qmaFourRawCorrelation 1 3 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_200 (ν : Fin 3) :
    (qmaFourSpinRawAction 2 0).transpose*qmaFourSpinRawAction 0 ν =
      if (0:Fin 3) = ν then qmaFourRawCorrelation 2 0 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_201 (ν : Fin 3) :
    (qmaFourSpinRawAction 2 1).transpose*qmaFourSpinRawAction 0 ν =
      if (1:Fin 3) = ν then qmaFourRawCorrelation 2 0 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_202 (ν : Fin 3) :
    (qmaFourSpinRawAction 2 2).transpose*qmaFourSpinRawAction 0 ν =
      if (2:Fin 3) = ν then qmaFourRawCorrelation 2 0 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_210 (ν : Fin 3) :
    (qmaFourSpinRawAction 2 0).transpose*qmaFourSpinRawAction 1 ν =
      if (0:Fin 3) = ν then qmaFourRawCorrelation 2 1 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_211 (ν : Fin 3) :
    (qmaFourSpinRawAction 2 1).transpose*qmaFourSpinRawAction 1 ν =
      if (1:Fin 3) = ν then qmaFourRawCorrelation 2 1 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_212 (ν : Fin 3) :
    (qmaFourSpinRawAction 2 2).transpose*qmaFourSpinRawAction 1 ν =
      if (2:Fin 3) = ν then qmaFourRawCorrelation 2 1 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_220 (ν : Fin 3) :
    (qmaFourSpinRawAction 2 0).transpose*qmaFourSpinRawAction 2 ν =
      if (0:Fin 3) = ν then qmaFourRawCorrelation 2 2 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_221 (ν : Fin 3) :
    (qmaFourSpinRawAction 2 1).transpose*qmaFourSpinRawAction 2 ν =
      if (1:Fin 3) = ν then qmaFourRawCorrelation 2 2 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_222 (ν : Fin 3) :
    (qmaFourSpinRawAction 2 2).transpose*qmaFourSpinRawAction 2 ν =
      if (2:Fin 3) = ν then qmaFourRawCorrelation 2 2 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_230 (ν : Fin 3) :
    (qmaFourSpinRawAction 2 0).transpose*qmaFourSpinRawAction 3 ν =
      if (0:Fin 3) = ν then qmaFourRawCorrelation 2 3 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_231 (ν : Fin 3) :
    (qmaFourSpinRawAction 2 1).transpose*qmaFourSpinRawAction 3 ν =
      if (1:Fin 3) = ν then qmaFourRawCorrelation 2 3 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_232 (ν : Fin 3) :
    (qmaFourSpinRawAction 2 2).transpose*qmaFourSpinRawAction 3 ν =
      if (2:Fin 3) = ν then qmaFourRawCorrelation 2 3 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_300 (ν : Fin 3) :
    (qmaFourSpinRawAction 3 0).transpose*qmaFourSpinRawAction 0 ν =
      if (0:Fin 3) = ν then qmaFourRawCorrelation 3 0 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_301 (ν : Fin 3) :
    (qmaFourSpinRawAction 3 1).transpose*qmaFourSpinRawAction 0 ν =
      if (1:Fin 3) = ν then qmaFourRawCorrelation 3 0 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_302 (ν : Fin 3) :
    (qmaFourSpinRawAction 3 2).transpose*qmaFourSpinRawAction 0 ν =
      if (2:Fin 3) = ν then qmaFourRawCorrelation 3 0 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_310 (ν : Fin 3) :
    (qmaFourSpinRawAction 3 0).transpose*qmaFourSpinRawAction 1 ν =
      if (0:Fin 3) = ν then qmaFourRawCorrelation 3 1 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_311 (ν : Fin 3) :
    (qmaFourSpinRawAction 3 1).transpose*qmaFourSpinRawAction 1 ν =
      if (1:Fin 3) = ν then qmaFourRawCorrelation 3 1 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_312 (ν : Fin 3) :
    (qmaFourSpinRawAction 3 2).transpose*qmaFourSpinRawAction 1 ν =
      if (2:Fin 3) = ν then qmaFourRawCorrelation 3 1 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_320 (ν : Fin 3) :
    (qmaFourSpinRawAction 3 0).transpose*qmaFourSpinRawAction 2 ν =
      if (0:Fin 3) = ν then qmaFourRawCorrelation 3 2 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_321 (ν : Fin 3) :
    (qmaFourSpinRawAction 3 1).transpose*qmaFourSpinRawAction 2 ν =
      if (1:Fin 3) = ν then qmaFourRawCorrelation 3 2 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_322 (ν : Fin 3) :
    (qmaFourSpinRawAction 3 2).transpose*qmaFourSpinRawAction 2 ν =
      if (2:Fin 3) = ν then qmaFourRawCorrelation 3 2 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_330 (ν : Fin 3) :
    (qmaFourSpinRawAction 3 0).transpose*qmaFourSpinRawAction 3 ν =
      if (0:Fin 3) = ν then qmaFourRawCorrelation 3 3 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_331 (ν : Fin 3) :
    (qmaFourSpinRawAction 3 1).transpose*qmaFourSpinRawAction 3 ν =
      if (1:Fin 3) = ν then qmaFourRawCorrelation 3 3 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_332 (ν : Fin 3) :
    (qmaFourSpinRawAction 3 2).transpose*qmaFourSpinRawAction 3 ν =
      if (2:Fin 3) = ν then qmaFourRawCorrelation 3 3 else 0 := by
  rw [qmaFourSpinRawAction_table,qmaFourSpinRawAction_table]
  ext a b
  fin_cases ν <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawCorrelation,qmaFourRawLogical,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ,
      qmaFourSpinTable,qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02,qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12,qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22,qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]

theorem qmaFourRawCorrelation_eq (i j : Fin 4) (μ ν : Fin 3) :
    (qmaFourSpinRawAction i μ).transpose*qmaFourSpinRawAction j ν =
      if μ = ν then qmaFourRawCorrelation i j else 0 := by
  fin_cases i
  · fin_cases j
    · fin_cases μ
      · exact qmaFourRawCorrelation_000 ν
      · exact qmaFourRawCorrelation_001 ν
      · exact qmaFourRawCorrelation_002 ν
    · fin_cases μ
      · exact qmaFourRawCorrelation_010 ν
      · exact qmaFourRawCorrelation_011 ν
      · exact qmaFourRawCorrelation_012 ν
    · fin_cases μ
      · exact qmaFourRawCorrelation_020 ν
      · exact qmaFourRawCorrelation_021 ν
      · exact qmaFourRawCorrelation_022 ν
    · fin_cases μ
      · exact qmaFourRawCorrelation_030 ν
      · exact qmaFourRawCorrelation_031 ν
      · exact qmaFourRawCorrelation_032 ν
  · fin_cases j
    · fin_cases μ
      · exact qmaFourRawCorrelation_100 ν
      · exact qmaFourRawCorrelation_101 ν
      · exact qmaFourRawCorrelation_102 ν
    · fin_cases μ
      · exact qmaFourRawCorrelation_110 ν
      · exact qmaFourRawCorrelation_111 ν
      · exact qmaFourRawCorrelation_112 ν
    · fin_cases μ
      · exact qmaFourRawCorrelation_120 ν
      · exact qmaFourRawCorrelation_121 ν
      · exact qmaFourRawCorrelation_122 ν
    · fin_cases μ
      · exact qmaFourRawCorrelation_130 ν
      · exact qmaFourRawCorrelation_131 ν
      · exact qmaFourRawCorrelation_132 ν
  · fin_cases j
    · fin_cases μ
      · exact qmaFourRawCorrelation_200 ν
      · exact qmaFourRawCorrelation_201 ν
      · exact qmaFourRawCorrelation_202 ν
    · fin_cases μ
      · exact qmaFourRawCorrelation_210 ν
      · exact qmaFourRawCorrelation_211 ν
      · exact qmaFourRawCorrelation_212 ν
    · fin_cases μ
      · exact qmaFourRawCorrelation_220 ν
      · exact qmaFourRawCorrelation_221 ν
      · exact qmaFourRawCorrelation_222 ν
    · fin_cases μ
      · exact qmaFourRawCorrelation_230 ν
      · exact qmaFourRawCorrelation_231 ν
      · exact qmaFourRawCorrelation_232 ν
  · fin_cases j
    · fin_cases μ
      · exact qmaFourRawCorrelation_300 ν
      · exact qmaFourRawCorrelation_301 ν
      · exact qmaFourRawCorrelation_302 ν
    · fin_cases μ
      · exact qmaFourRawCorrelation_310 ν
      · exact qmaFourRawCorrelation_311 ν
      · exact qmaFourRawCorrelation_312 ν
    · fin_cases μ
      · exact qmaFourRawCorrelation_320 ν
      · exact qmaFourRawCorrelation_321 ν
      · exact qmaFourRawCorrelation_322 ν
    · fin_cases μ
      · exact qmaFourRawCorrelation_330 ν
      · exact qmaFourRawCorrelation_331 ν
      · exact qmaFourRawCorrelation_332 ν

end ContinuumCoulomb

end

end OAI

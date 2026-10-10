import OAI.Analysis.Triangular.Signs.RemainderSums0
import OAI.Analysis.Triangular.Signs.RemainderSums1
import OAI.Analysis.Triangular.Signs.RemainderSums2
import OAI.Analysis.Triangular.Signs.RemainderSums3
import OAI.Analysis.Triangular.Signs.RemainderSums4
import OAI.Analysis.Triangular.Signs.RemainderSums5
import OAI.Analysis.Triangular.Signs.RemainderSums6

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainder_all_pre (q br : Fin 2) (n : Fin 7) (j : Fin 31) :
    0<((RI.point 1).sub (((nearRadiusBox n).mul (taylorNormTable q br j)).divNat 24)).lo := by
  fin_cases n <;> fin_cases q <;> fin_cases br
  · exact (remainderData0_00_pre j).2
  · exact (remainderData0_01_pre j).2
  · exact (remainderData0_10_pre j).2
  · exact (remainderData0_11_pre j).2
  · exact (remainderData1_00_pre j).2
  · exact (remainderData1_01_pre j).2
  · exact (remainderData1_10_pre j).2
  · exact (remainderData1_11_pre j).2
  · exact (remainderData2_00_pre j).2
  · exact (remainderData2_01_pre j).2
  · exact (remainderData2_10_pre j).2
  · exact (remainderData2_11_pre j).2
  · exact (remainderData3_00_pre j).2
  · exact (remainderData3_01_pre j).2
  · exact (remainderData3_10_pre j).2
  · exact (remainderData3_11_pre j).2
  · exact (remainderData4_00_pre j).2
  · exact (remainderData4_01_pre j).2
  · exact (remainderData4_10_pre j).2
  · exact (remainderData4_11_pre j).2
  · exact (remainderData5_00_pre j).2
  · exact (remainderData5_01_pre j).2
  · exact (remainderData5_10_pre j).2
  · exact (remainderData5_11_pre j).2
  · exact (remainderData6_00_pre j).2
  · exact (remainderData6_01_pre j).2
  · exact (remainderData6_10_pre j).2
  · exact (remainderData6_11_pre j).2
lemma remainder_ratio_lt_one (q br : Fin 2) (n : Fin 7) (j : Fin 31) :
    nearRadius n*‖taylorPhase q br (frequency j)‖/24<1 := by
  have hh := (RI.mem_sub ri1_mem (RI.mem_divNat
    (RI.mem_mul (nearRadiusBox_mem n) (taylorNormTable_mem q br j)) (by norm_num : 0<24))).1
  have hp : (0:ℝ)<((RI.point 1).sub (((nearRadiusBox n).mul (taylorNormTable q br j)).divNat 24)).lo :=
    by exact_mod_cast remainder_all_pre q br n j
  have hs := AtomicTriangular.Interval.scale_pos
  nlinarith
lemma remainder_table (n : Fin 7) (c d : Fin 22) :
    3*(rawRemainderColumn 0 n c+rawRemainderColumn 1 n d)+(6/1000)*(rawRemainderConstant 0 n+rawRemainderConstant 1 n) <
      (if n.val=0 then (161/100000:ℝ) else 75/10000000) := by
  fin_cases n
  · exact remainderTable0 c d
  · exact remainderTable1 c d
  · exact remainderTable2 c d
  · exact remainderTable3 c d
  · exact remainderTable4 c d
  · exact remainderTable5 c d
  · exact remainderTable6 c d
end AtomicTriangular.FiniteCertificate
end

end OAI

import OAI.Analysis.Triangular.Taylor.TaylorExp00
import OAI.Analysis.Triangular.Taylor.TaylorExp01
import OAI.Analysis.Triangular.Taylor.TaylorExp10
import OAI.Analysis.Triangular.Taylor.TaylorExp11

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def taylorExpTable : Fin 2 → Fin 2 → Fin 7 → Fin 31 → CI := ![![![taylorExp0_0_1,taylorExp0_0_3,taylorExp0_0_4,taylorExp0_0_7,taylorExp0_0_9,taylorExp0_0_12,taylorExp0_0_13],![taylorExp0_1_1,taylorExp0_1_3,taylorExp0_1_4,taylorExp0_1_7,taylorExp0_1_9,taylorExp0_1_12,taylorExp0_1_13]],![![taylorExp1_0_1,taylorExp1_0_3,taylorExp1_0_4,taylorExp1_0_7,taylorExp1_0_9,taylorExp1_0_12,taylorExp1_0_13],![taylorExp1_1_1,taylorExp1_1_3,taylorExp1_1_4,taylorExp1_1_7,taylorExp1_1_9,taylorExp1_1_12,taylorExp1_1_13]]]
lemma taylorExpTable_mem (q br : Fin 2) (n : Fin 7) (j : Fin 31) :
    (taylorExpTable q br n j).Mem (exp (taylorPhase q br (frequency j)*(nearNode n:ℂ))) := by
  fin_cases q <;> fin_cases br <;> fin_cases n
  · exact taylorExp0_0_1_mem j
  · exact taylorExp0_0_3_mem j
  · exact taylorExp0_0_4_mem j
  · exact taylorExp0_0_7_mem j
  · exact taylorExp0_0_9_mem j
  · exact taylorExp0_0_12_mem j
  · exact taylorExp0_0_13_mem j
  · exact taylorExp0_1_1_mem j
  · exact taylorExp0_1_3_mem j
  · exact taylorExp0_1_4_mem j
  · exact taylorExp0_1_7_mem j
  · exact taylorExp0_1_9_mem j
  · exact taylorExp0_1_12_mem j
  · exact taylorExp0_1_13_mem j
  · exact taylorExp1_0_1_mem j
  · exact taylorExp1_0_3_mem j
  · exact taylorExp1_0_4_mem j
  · exact taylorExp1_0_7_mem j
  · exact taylorExp1_0_9_mem j
  · exact taylorExp1_0_12_mem j
  · exact taylorExp1_0_13_mem j
  · exact taylorExp1_1_1_mem j
  · exact taylorExp1_1_3_mem j
  · exact taylorExp1_1_4_mem j
  · exact taylorExp1_1_7_mem j
  · exact taylorExp1_1_9_mem j
  · exact taylorExp1_1_12_mem j
  · exact taylorExp1_1_13_mem j
end AtomicTriangular.FiniteCertificate
end

end OAI

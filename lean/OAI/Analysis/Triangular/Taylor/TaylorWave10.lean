import OAI.Analysis.Triangular.Taylor.TaylorWave100
import OAI.Analysis.Triangular.Taylor.TaylorWave101
import OAI.Analysis.Triangular.Taylor.TaylorWave102
import OAI.Analysis.Triangular.Taylor.TaylorWave103
import OAI.Analysis.Triangular.Taylor.TaylorWave104
import OAI.Analysis.Triangular.Taylor.TaylorWave105
import OAI.Analysis.Triangular.Taylor.TaylorWave106

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw1_0 : Fin 7 → Fin 21 → Fin 31 → CI := ![tw1_0_0,tw1_0_1,tw1_0_2,tw1_0_3,tw1_0_4,tw1_0_5,tw1_0_6]
lemma tw1_0_mem (n : Fin 7) (l : Fin 21) (j : Fin 31) : (tw1_0 n l j).Mem (taylorWave 1 0 (nearNode n) l.val (frequency j)) := by
  fin_cases n
  · exact tw1_0_0_mem l j
  · exact tw1_0_1_mem l j
  · exact tw1_0_2_mem l j
  · exact tw1_0_3_mem l j
  · exact tw1_0_4_mem l j
  · exact tw1_0_5_mem l j
  · exact tw1_0_6_mem l j
end AtomicTriangular.FiniteCertificate
end

end OAI

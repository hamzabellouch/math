import OAI.Analysis.Triangular.Taylor.TaylorWave110
import OAI.Analysis.Triangular.Taylor.TaylorWave111
import OAI.Analysis.Triangular.Taylor.TaylorWave112
import OAI.Analysis.Triangular.Taylor.TaylorWave113
import OAI.Analysis.Triangular.Taylor.TaylorWave114
import OAI.Analysis.Triangular.Taylor.TaylorWave115
import OAI.Analysis.Triangular.Taylor.TaylorWave116

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw1_1 : Fin 7 → Fin 21 → Fin 31 → CI := ![tw1_1_0,tw1_1_1,tw1_1_2,tw1_1_3,tw1_1_4,tw1_1_5,tw1_1_6]
lemma tw1_1_mem (n : Fin 7) (l : Fin 21) (j : Fin 31) : (tw1_1 n l j).Mem (taylorWave 1 1 (nearNode n) l.val (frequency j)) := by
  fin_cases n
  · exact tw1_1_0_mem l j
  · exact tw1_1_1_mem l j
  · exact tw1_1_2_mem l j
  · exact tw1_1_3_mem l j
  · exact tw1_1_4_mem l j
  · exact tw1_1_5_mem l j
  · exact tw1_1_6_mem l j
end AtomicTriangular.FiniteCertificate
end

end OAI

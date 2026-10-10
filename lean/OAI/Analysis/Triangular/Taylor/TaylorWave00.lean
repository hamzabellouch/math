import OAI.Analysis.Triangular.Taylor.TaylorWave000
import OAI.Analysis.Triangular.Taylor.TaylorWave001
import OAI.Analysis.Triangular.Taylor.TaylorWave002
import OAI.Analysis.Triangular.Taylor.TaylorWave003
import OAI.Analysis.Triangular.Taylor.TaylorWave004
import OAI.Analysis.Triangular.Taylor.TaylorWave005
import OAI.Analysis.Triangular.Taylor.TaylorWave006

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw0_0 : Fin 7 → Fin 21 → Fin 31 → CI := ![tw0_0_0,tw0_0_1,tw0_0_2,tw0_0_3,tw0_0_4,tw0_0_5,tw0_0_6]
lemma tw0_0_mem (n : Fin 7) (l : Fin 21) (j : Fin 31) : (tw0_0 n l j).Mem (taylorWave 0 0 (nearNode n) l.val (frequency j)) := by
  fin_cases n
  · exact tw0_0_0_mem l j
  · exact tw0_0_1_mem l j
  · exact tw0_0_2_mem l j
  · exact tw0_0_3_mem l j
  · exact tw0_0_4_mem l j
  · exact tw0_0_5_mem l j
  · exact tw0_0_6_mem l j
end AtomicTriangular.FiniteCertificate
end

end OAI

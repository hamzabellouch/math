import OAI.Analysis.Triangular.Taylor.TaylorWave010
import OAI.Analysis.Triangular.Taylor.TaylorWave011
import OAI.Analysis.Triangular.Taylor.TaylorWave012
import OAI.Analysis.Triangular.Taylor.TaylorWave013
import OAI.Analysis.Triangular.Taylor.TaylorWave014
import OAI.Analysis.Triangular.Taylor.TaylorWave015
import OAI.Analysis.Triangular.Taylor.TaylorWave016

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw0_1 : Fin 7 → Fin 21 → Fin 31 → CI := ![tw0_1_0,tw0_1_1,tw0_1_2,tw0_1_3,tw0_1_4,tw0_1_5,tw0_1_6]
lemma tw0_1_mem (n : Fin 7) (l : Fin 21) (j : Fin 31) : (tw0_1 n l j).Mem (taylorWave 0 1 (nearNode n) l.val (frequency j)) := by
  fin_cases n
  · exact tw0_1_0_mem l j
  · exact tw0_1_1_mem l j
  · exact tw0_1_2_mem l j
  · exact tw0_1_3_mem l j
  · exact tw0_1_4_mem l j
  · exact tw0_1_5_mem l j
  · exact tw0_1_6_mem l j
end AtomicTriangular.FiniteCertificate
end

end OAI

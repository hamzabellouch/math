import OAI.Analysis.Triangular.Certificate.WaveExpData
import OAI.Analysis.Triangular.Taylor.TaylorExp

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def taylorAmplitudeBox (q br : Fin 2) (j : Fin 31) : CI :=
  if br.val=0 then CI.point 1 else lambdaTable q j
lemma taylorAmplitudeBox_mem (q br : Fin 2) (j : Fin 31) :
    (taylorAmplitudeBox q br j).Mem (taylorAmplitude q br (frequency j)) := by
  unfold taylorAmplitudeBox taylorAmplitude
  split_ifs
  · simpa using CI.mem_point 1
  · exact lambdaTable_mem q j

def taylorWaveBox (q br : Fin 2) (n : Fin 7) (l : Fin 21) (j : Fin 31) : CI :=
  (((taylorAmplitudeBox q br j).mul (taylorExpTable q br n j)).mul
    ((taylorPhaseTable q br j).pow (l.val+2))).divNat (l.val+2).factorial
lemma taylorWaveBox_mem (q br : Fin 2) (n : Fin 7) (l : Fin 21) (j : Fin 31) :
    (taylorWaveBox q br n l j).Mem (taylorWave q br (nearNode n) l.val (frequency j)) := by
  exact CI.mem_divNat (CI.mem_mul (CI.mem_mul (taylorAmplitudeBox_mem q br j) (taylorExpTable_mem q br n j))
    (CI.mem_pow (taylorPhaseTable_mem q br j) (l.val+2))) (Nat.factorial_pos _)

end AtomicTriangular.FiniteCertificate
end

end OAI

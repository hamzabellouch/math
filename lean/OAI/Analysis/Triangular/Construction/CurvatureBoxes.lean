import OAI.Analysis.Triangular.Envelope.EnvelopeBoxes
import OAI.Analysis.Triangular.Envelope.EnvelopeWaves
import OAI.Analysis.Triangular.Taylor.TaylorPhase

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

def curvatureWave (q br : Fin 2) (s t : ℝ) : ℝ :=
  ‖taylorPhase q br t‖^2 * ‖taylorAmplitude q br t‖ * Real.exp ((taylorPhase q br t).re*s)
def curvaturePoint : Fin 5 → ℝ := ![0,1,2,29/2,23]
def rawCurvatureColumn (br : Fin 2) (s : ℝ) (c : Fin 22) : ℝ :=
  ∑ j : Fin 31, curvatureWave 1 br s (frequency j)*‖finiteColumn ⟨c.val,by omega⟩ j‖
def rawConstantCurvature (s : ℝ) : ℝ :=
  (∑ j : Fin 31, curvatureWave 0 1 s (frequency j)*‖fourierCoeff j‖)/2
def rawTailCurvature (i : Fin 5) : ℝ :=
  60*(curvatureWave 0 0 (curvaturePoint i) (frequency 30)+
    curvatureWave 0 1 (curvaturePoint i) (frequency (if i.val=0 then 15 else 30)))
end AtomicTriangular.Construction
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def curvaturePointBox : Fin 5 → RI :=
  ![RI.point 0,RI.point 1,RI.point 2,(RI.point 29).divNat 2,RI.point 23]
lemma curvaturePointBox_mem (i : Fin 5) : (curvaturePointBox i).Mem (curvaturePoint i) := by
  fin_cases i <;> norm_num [curvaturePointBox,curvaturePoint,RI.Mem,RI.point,RI.divNat,scale]
def amplitudeNormBox (q br : Fin 2) (j : Fin 31) : RI :=
  if br.val=0 then RI.point 1 else if q.val=0 then lambdaNorm0 j else lambdaNorm1 j
lemma amplitudeNormBox_mem (q br : Fin 2) (j : Fin 31) :
    (amplitudeNormBox q br j).Mem ‖taylorAmplitude q br (frequency j)‖ := by
  fin_cases br
  · simpa [amplitudeNormBox,taylorAmplitude] using ri1_mem
  · fin_cases q
    · simpa [amplitudeNormBox,taylorAmplitude] using lambdaNorm0_mem j
    · simpa [amplitudeNormBox,taylorAmplitude] using lambdaNorm1_mem j

def curvatureExpInput (q br : Fin 2) (i : Fin 5) (j : Fin 31) : CI :=
  CI.ofReal ((taylorPhaseTable q br j).re.mul (curvaturePointBox i))
def curvatureBox (q br : Fin 2) (i : Fin 5) (j : Fin 31) : RI :=
  ((taylorPhaseTable q br j).normSq.mul (amplitudeNormBox q br j)).mul
    (curvatureExpInput q br i j).exp.re
lemma curvatureBox_mem (q br : Fin 2) (i : Fin 5) (j : Fin 31)
    (hp : (curvatureExpInput q br i j).normSq.hi ≤ scale*1024^2) :
    (curvatureBox q br i j).Mem (curvatureWave q br (curvaturePoint i) (frequency j)) := by
  have hs := CI.mem_normSq (taylorPhaseTable_mem q br j)
  rw [Complex.normSq_eq_norm_sq] at hs
  exact RI.mem_mul (RI.mem_mul hs (amplitudeNormBox_mem q br j))
    (ri_exp_mem (RI.mem_mul (taylorPhaseTable_mem q br j).1 (curvaturePointBox_mem i)) hp)
end AtomicTriangular.FiniteCertificate
end

end OAI

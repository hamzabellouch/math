import OAI.Analysis.Triangular.Construction.CurvatureBoxes
import OAI.Analysis.Triangular.Taylor.TaylorRowsBase

namespace OAI

noncomputable section
open scoped BigOperators
open AtomicTriangular.FiniteCertificate
namespace AtomicTriangular.Construction

def remainderWave (q br : Fin 2) (m Y t : ℝ) : ℝ :=
  curvatureWave q br m t * (Y*‖taylorPhase q br t‖)^21 / (23).factorial /
    (1-Y*‖taylorPhase q br t‖/24)
def nearRadius : Fin 7 → ℝ := ![1,1,3/2,3/2,3/2,3/2,3/2]
lemma nearDisplacement_le_radius (n : Fin 7) (y : Fin 2) :
    |nearDisplacement n y|≤nearRadius n := by
  fin_cases n <;> fin_cases y <;> norm_num [nearDisplacement,nearDisplacementNum,nearRadius]
lemma nearRadius_nonneg (n : Fin 7) : 0≤nearRadius n := by
  fin_cases n <;> norm_num [nearRadius]
def rawRemainderColumn (br : Fin 2) (n : Fin 7) (c : Fin 22) : ℝ :=
  ∑ j : Fin 31, remainderWave 1 br (nearNode n) (nearRadius n) (frequency j)*
    ‖finiteColumn ⟨c.val,by omega⟩ j‖
def rawRemainderConstant (br : Fin 2) (n : Fin 7) : ℝ :=
  ∑ j : Fin 31, remainderWave 0 br (nearNode n) (nearRadius n) (frequency j)*‖fourierCoeff j‖
end AtomicTriangular.Construction
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def nearRadiusBox (n : Fin 7) : RI := if n.val<2 then RI.point 1 else (RI.point 3).divNat 2
lemma nearRadiusBox_mem (n : Fin 7) : (nearRadiusBox n).Mem (nearRadius n) := by
  fin_cases n <;> norm_num [nearRadiusBox,nearRadius,RI.Mem,RI.point,RI.divNat,scale]
def remainderExpInput (q br : Fin 2) (n : Fin 7) (j : Fin 31) : CI :=
  CI.ofReal ((taylorPhaseTable q br j).re.mul (RI.point (nearNode n)))
def remainderBox (q br : Fin 2) (n : Fin 7) (j : Fin 31) (dnorm : RI) : RI :=
  (((((taylorPhaseTable q br j).normSq.mul (amplitudeNormBox q br j)).mul
    (remainderExpInput q br n j).exp.re).mul (((nearRadiusBox n).mul dnorm).pow 21)).divNat (23).factorial).mul
    ((RI.point 1).sub (((nearRadiusBox n).mul dnorm).divNat 24)).invPos
lemma remainderBox_mem (q br : Fin 2) (n : Fin 7) (j : Fin 31) {dnorm : RI}
    (hd : dnorm.Mem ‖taylorPhase q br (frequency j)‖)
    (hp : (remainderExpInput q br n j).normSq.hi ≤ scale*1024^2)
    (hden : 0<((RI.point 1).sub (((nearRadiusBox n).mul dnorm).divNat 24)).lo) :
    (remainderBox q br n j dnorm).Mem
      (remainderWave q br (nearNode n) (nearRadius n) (frequency j)) := by
  have hs := CI.mem_normSq (taylorPhaseTable_mem q br j)
  rw [Complex.normSq_eq_norm_sq] at hs
  have he := ri_exp_mem (RI.mem_mul (taylorPhaseTable_mem q br j).1 (RI.mem_point (nearNode n))) hp
  have hy := RI.mem_mul (nearRadiusBox_mem n) hd
  have hc := RI.mem_mul (RI.mem_mul hs (amplitudeNormBox_mem q br j)) he
  have hh := RI.mem_mul (RI.mem_divNat (RI.mem_mul hc (RI.mem_pow hy 21)) (by decide : 0<(23).factorial))
    (RI.mem_invPos (RI.mem_sub ri1_mem (RI.mem_divNat hy (by norm_num : 0<24))) hden)
  simpa only [remainderBox,remainderWave,curvatureWave,div_eq_mul_inv,Nat.cast_ofNat,remainderExpInput] using hh
end AtomicTriangular.FiniteCertificate
end

end OAI

import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourStencils
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourFields

namespace OAI

/-! A common interface for the fixed X and Z exchange encodings. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaFourAxis (a : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ := if a = 0 then pauliX else pauliZ
def qmaFourAxisWeights (a : Fin 2) (p : Bool) : Fin 4 → ℝ :=
  if a = 0 then qmaFourXWeights p else qmaFourZWeights p
def qmaFourAxisShift (a : Fin 2) (p : Bool) : ℝ :=
  if a = 0 then 400 else if p then 8/3 else 4/3
def qmaFourAxisScale (a : Fin 2) : ℝ := if a = 0 then 128*Real.sqrt 3 else 4/3
def qmaFourAxisSign (p : Bool) : ℝ := if p then 1 else -1

theorem qmaFourAxisScale_pos (a : Fin 2) : 0 < qmaFourAxisScale a := by
  fin_cases a <;> simp only [qmaFourAxisScale,Fin.zero_eta,ite_true,Fin.isValue,Fin.mk_one,
    Fin.reduceEq,ite_false]
  · positivity
  · norm_num

theorem qmaFourAxisWeights_correlation (a : Fin 2) (p : Bool) :
    qmaFourWeightedCorrelation (qmaFourAxisWeights a p) =
      (qmaFourAxisShift a p:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)+
      ((qmaFourAxisSign p*qmaFourAxisScale a:ℝ):ℂ) • qmaFourAxis a := by
  fin_cases a <;> cases p <;>
    simp [qmaFourAxisWeights,qmaFourAxisShift,qmaFourAxisSign,qmaFourAxisScale,qmaFourAxis,
      qmaFourXWeights_true,qmaFourXWeights_false,qmaFourZWeights_true,qmaFourZWeights_false,neg_div,neg_smul]

def qmaFourAxisField (a : Fin 2) (t : ℝ) : Matrix (Fin 16) (Fin 16) ℂ :=
  if a = 0 then qmaFourField t 0 else qmaFourField 0 t

def qmaFourAxisFieldShift (a : Fin 2) (t : ℝ) : ℝ := if a = 0 then 0 else t/2

theorem qmaFourAxisField_compression (a : Fin 2) (t : ℝ) :
    qmaFourEncoding.conjTranspose*qmaFourAxisField a t*qmaFourEncoding =
      (t:ℂ) • qmaFourAxis a+(qmaFourAxisFieldShift a t:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  fin_cases a <;> simp [qmaFourAxisField,qmaFourAxis,qmaFourAxisFieldShift,qmaFourField_compression]

end ContinuumCoulomb

end

end OAI

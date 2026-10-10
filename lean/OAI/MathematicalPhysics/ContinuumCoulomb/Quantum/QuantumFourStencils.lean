import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourWeighted

namespace OAI

/-! Rational physical-spin weights giving shifted logical X and Z. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaFourXWeights (positive : Bool) : Fin 4 → ℝ :=
  if positive then ![11,-1,-13,3] else ![11,-1,3,-13]

def qmaFourZWeights (positive : Bool) : Fin 4 → ℝ :=
  if positive then ![1,-1,0,0] else ![1,1,0,0]

theorem qmaFourXWeights_true :
    qmaFourWeightedCorrelation (qmaFourXWeights true) =
      (400:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)+(128*(Real.sqrt 3:ℂ)) • pauliX := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourWeightedCorrelation,qmaFourXWeights,qmaFourCorrelation,
      qmaFourLogical,Fin.sum_univ_succ,Matrix.one_apply,pauliX] <;> ring

theorem qmaFourXWeights_false :
    qmaFourWeightedCorrelation (qmaFourXWeights false) =
      (400:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)+(-128*(Real.sqrt 3:ℂ)) • pauliX := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourWeightedCorrelation,qmaFourXWeights,qmaFourCorrelation,
      qmaFourLogical,Fin.sum_univ_succ,Matrix.one_apply,pauliX] <;> ring

theorem qmaFourZWeights_true :
    qmaFourWeightedCorrelation (qmaFourZWeights true) =
      (8/3:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)+(4/3:ℂ) • pauliZ := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourWeightedCorrelation,qmaFourZWeights,qmaFourCorrelation,
      qmaFourLogical,Fin.sum_univ_succ,Matrix.one_apply,pauliZ]

theorem qmaFourZWeights_false :
    qmaFourWeightedCorrelation (qmaFourZWeights false) =
      (4/3:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)+(-4/3:ℂ) • pauliZ := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourWeightedCorrelation,qmaFourZWeights,qmaFourCorrelation,
      qmaFourLogical,Fin.sum_univ_succ,Matrix.one_apply,pauliZ]

end ContinuumCoulomb

end

end OAI

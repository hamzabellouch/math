import Mathlib
import OAI.Analysis.SymmetricDomains.FlatWeightedEuler
import OAI.Analysis.SymmetricDomains.AnalyticSecondJetCoordinates

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
namespace Release061
namespace Biholomorph

abbrev ModelIndex (r k : ℕ) := Fin r ⊕ Fin k

def modelBasis (r k : ℕ) : Module.Basis (ModelIndex r k) ℂ (Affine (r+k)) :=
  ((Pi.basisFun ℂ (Fin r)).prod (Pi.basisFun ℂ (Fin k))).map
    (affineProductCoordinates r k).toLinearEquiv

def modelEulerWeight {r k : ℕ} : ModelIndex r k → ℂ
  | .inl _ => 1/2
  | .inr _ => 1

def modelRotationWeight {r k : ℕ} : ModelIndex r k → ℂ
  | .inl _ => Complex.I
  | .inr _ => 0

 theorem flatWeightedEuler_basis (r k : ℕ) (i : ModelIndex r k) :
    flatWeightedEuler r k (modelBasis r k i)=modelEulerWeight i • modelBasis r k i := by
  rcases i with i|i <;>
    simp [modelBasis,flatWeightedEuler,modelEulerWeight,Module.Basis.prod_apply,
      ←map_smul]

 theorem flatTangentialInfinitesimal_basis (r k : ℕ) (i : ModelIndex r k) :
    flatTangentialInfinitesimal r k (modelBasis r k i)=modelRotationWeight i • modelBasis r k i := by
  rcases i with i|i <;>
    simp [modelBasis,flatTangentialInfinitesimal,modelRotationWeight,Module.Basis.prod_apply,
      ←map_smul]

 theorem modelEulerWeight_cases {r k : ℕ} (i : ModelIndex r k) :
    modelEulerWeight i=(1/2 : ℂ) ∨ modelEulerWeight i=1 := by
  cases i <;> simp [modelEulerWeight]

 theorem secondJet_modelEulerWeight_mem {r k : ℕ} (j : SecondJetIndex (ModelIndex r k)) :
    secondJetWeight modelEulerWeight j∈({-1,-(1/2),0,1/2,1,3/2} : Finset ℂ) := by
  rcases j with i | (⟨i,j⟩ | ⟨i,j,k⟩)
  · cases i <;> norm_num [secondJetWeight,modelEulerWeight]
  · cases i <;> cases j <;> norm_num [secondJetWeight,modelEulerWeight]
  · cases i <;> cases j <;> cases k <;> norm_num [secondJetWeight,modelEulerWeight]

 theorem modelEuler_extreme_rotation {r k : ℕ} (j : SecondJetIndex (ModelIndex r k))
    (hj : secondJetWeight modelEulerWeight j=(3/2 : ℂ)) :
    secondJetWeight modelRotationWeight j=-Complex.I := by
  rcases j with i | (⟨i,j⟩ | ⟨i,j,k⟩)
  · cases i <;> norm_num [secondJetWeight,modelEulerWeight] at hj
  · cases i <;> cases j <;> norm_num [secondJetWeight,modelEulerWeight] at hj
  · cases i <;> cases j <;> cases k <;>
      norm_num [secondJetWeight,modelEulerWeight] at hj
    norm_num [secondJetWeight,modelRotationWeight]

 theorem flatWeightedEuler_normal {r k : ℕ} (a : Fin k → ℝ) :
    flatWeightedEuler r k (flatNormalVector r k a)=flatNormalVector r k a := by
  simp [flatWeightedEuler,flatNormalVector]

 theorem flatTangentialInfinitesimal_normal {r k : ℕ} (a : Fin k → ℝ) :
    flatTangentialInfinitesimal r k (flatNormalVector r k a)=0 := by
  simp [flatTangentialInfinitesimal,flatNormalVector]

end Biholomorph
end Release061

end

end OAI

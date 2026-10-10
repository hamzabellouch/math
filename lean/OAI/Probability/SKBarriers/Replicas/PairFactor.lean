import Mathlib
import OAI.Probability.SKBarriers.Replicas.MatrixGuerraEndpoints
import OAI.Probability.SKBarriers.Replicas.PairBlocks
import OAI.Probability.SKBarriers.Replicas.PairTerminal
import OAI.Probability.SKBarriers.SpinGlass.FinitePrefix

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def pairMatrix (t q : ℝ) (i j : Fin 2) : ℝ := if i=j then t else q

def pairFactor (shared : Bool) (c : ℝ) (u i : Fin 2) : ℝ :=
  if i=0 then (pairBlockVector shared c u).1 else (pairBlockVector shared c u).2

def splitPairFactor {n : ℕ} (a : ℕ) (c : Fin n → ℝ) (j : Fin n) : Fin 2 → Fin 2 → ℝ :=
  pairFactor (decide (j.val<a)) (c j)

theorem pairFactor_covariance (shared : Bool) (c : ℝ) :
    factorCovariance 2 2 (pairFactor shared c)=pairMatrix (c^2) (if shared then c^2 else 0) := by
  funext i j
  fin_cases i <;> fin_cases j <;> cases shared <;>
    simp [factorCovariance,pairFactor,pairBlockVector,pairMatrix,Fin.sum_univ_two,pow_two]

theorem pairFactor_vector (shared : Bool) (β c : ℝ) (u : Fin 2) (s : Config 2) :
    β*(∑ i, pairFactor shared c u i*spin (s i))=pairSpinMap (pairBlockVector shared (β*c) u) s := by
  fin_cases u <;> cases shared <;>
    simp [pairFactor,pairBlockVector,pairSpinMap_apply,Fin.sum_univ_two] <;> ring

theorem splitPairFactor_vector {k : ℕ} (a : ℕ) (β : ℝ) (c : Fin (k+1) → ℝ) :
    matrixSiteVector β (splitPairFactor a c) (fun (s : Config 2) i => spin (s i))=
      pairSpinMap ∘ (fun j => splitPairVector a (fun i => β*c i) (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2) := by
  funext j s
  exact pairFactor_vector _ _ _ _ _

theorem splitPairFactor_path {k : ℕ} (a : ℕ) (c : Fin (k+1) → ℝ) (j : Fin (k+1)) :
    factorPath 2 2 k (splitPairFactor a c) j=
      pairMatrix (finitePrefix (fun l => (c l)^2) j)
        (finitePrefix (fun l => if l.val<a then (c l)^2 else 0) j) := by
  funext u v
  simp only [factorPath,splitPairFactor,pairFactor_covariance,pairMatrix,finitePrefix]
  by_cases h : u=v <;> simp [h]

def pairMultiplier : Fin 2 → Fin 2 → ℝ := pairMatrix 0 (1/2)

theorem pairMultiplier_observable :
    matrixSiteWeight pairMultiplier (fun (s : Config 2) i => spin (s i))=pairSpinObservable := by
  funext s
  simp only [matrixSiteWeight,pairMultiplier,pairMatrix,Fin.sum_univ_two,ite_true,
    show (0:Fin 2)≠1 by decide,show (1:Fin 2)≠0 by decide,ite_false,zero_mul,zero_add,add_zero,pairSpinObservable]
  ring

theorem pairMultiplier_inner (t q : ℝ) : matrixInner 2 pairMultiplier (pairMatrix t q)=q := by
  norm_num [matrixInner,pairMultiplier,pairMatrix,Fin.sum_univ_two]
  ring

theorem pairMatrix_square (t q : ℝ) : matrixSquare 2 (pairMatrix t q)=2*t^2+2*q^2 := by
  norm_num [matrixSquare,pairMatrix,Fin.sum_univ_two]
  ring

theorem matrixInner_self (d : ℕ) (D : Fin d → Fin d → ℝ) : matrixInner d D D=matrixSquare d D := by
  simp only [matrixInner,matrixSquare,pow_two]

end SK.Analytic

end
end

end OAI

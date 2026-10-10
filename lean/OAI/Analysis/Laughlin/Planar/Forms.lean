import OAI.Analysis.Laughlin.Planar.Restriction
import OAI.Analysis.Laughlin.Fock.Bidegree
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace OAI

namespace Laughlin.Planar
open Fock
open scoped BigOperators ENNReal

structure HomogeneousState (N : ℕ) where
  block : (L : ℕ) → Space L
  homogeneous : ∀ L, OccupationBidegree L N L (block L)

noncomputable def fullNormSq {N : ℕ} (ψ : HomogeneousState N) : ℝ≥0∞ :=
  ∑' L, ENNReal.ofReal (occupationNormSq L (ψ.block L))

def IsHilbertState {N : ℕ} (ψ : HomogeneousState N) : Prop := fullNormSq ψ < ⊤

noncomputable def fullEnergy {N : ℕ} (ψ : HomogeneousState N) : ℝ≥0∞ :=
  ∑' L, ENNReal.ofReal (pairEnergy L (planarPairMatrix L)
    (fun A => (occupationBasis L).repr (ψ.block L) A))

noncomputable def fullSquareNorm {N : ℕ} (ψ : HomogeneousState N) : ℝ≥0∞ :=
  ∑' L, ENNReal.ofReal (squareNorm L (planarHamiltonian L)
    (fun A => (occupationBasis L).repr (ψ.block L) A))

theorem full_planar_endpoint {N : ℕ} (ψ : HomogeneousState N) :
    ENNReal.ofReal gammaStar * fullEnergy ψ ≤ fullSquareNorm ψ := by
  unfold fullEnergy fullSquareNorm
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro L
  have hd : DegreeAtMost L L (ψ.block L) := by
    intro A hA
    exact ψ.homogeneous L A (Or.inr (ne_of_gt hA))
  have h := finite_degree_endpoint L (ψ.block L) hd
  have hγ : 0 ≤ gammaStar :=
    le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 1/25) one_twenty_fifth_lt_gammaStar)
  rw [← ENNReal.ofReal_mul hγ]
  exact ENNReal.ofReal_le_ofReal h

end Laughlin.Planar

end OAI

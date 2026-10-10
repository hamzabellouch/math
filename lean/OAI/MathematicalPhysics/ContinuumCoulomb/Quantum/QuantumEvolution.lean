import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGateUnitary

namespace OAI

/-! Norm preservation for the actual verifier evolution. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators

theorem qma_matrix_mass_preserved {n : ℕ}
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (hM : M.conjTranspose*M = 1) (u : SourceSpinVector n) :
    sourceSpinMass (M.mulVec u) = sourceSpinMass u := by
  have hinner : star (M.mulVec u) ⬝ᵥ M.mulVec u = star u ⬝ᵥ u := by
    rw [Matrix.star_mulVec,←Matrix.dotProduct_mulVec,Matrix.mulVec_mulVec,hM,Matrix.one_mulVec]
  have hreal := congrArg Complex.re hinner
  have hre (z : ℂ) : (star z*z).re = Complex.normSq z := by
    simp [Complex.mul_re,Complex.normSq_apply]
  simpa only [dotProduct,Pi.star_apply,Complex.re_sum,hre,sourceSpinMass] using hreal

def qmaApplyMatrix {n : ℕ}
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (u : EuclideanSpace ℂ (SourceSpinBasis n)) : EuclideanSpace ℂ (SourceSpinBasis n) :=
  WithLp.toLp 2 (M.mulVec (fun s => u s))

theorem qmaApplyMatrix_norm {n : ℕ}
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (hM : M.conjTranspose*M = 1) (u : EuclideanSpace ℂ (SourceSpinBasis n)) :
    ‖qmaApplyMatrix M u‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
  simpa only [qmaApplyMatrix,PiLp.toLp_apply,Complex.sq_norm,sourceSpinMass] using
    qma_matrix_mass_preserved M hM (fun s => u s)

theorem qmaCircuit_mass_preserved (c : QMACircuit) (hc : c.WellFormed)
    (u : SourceSpinVector (c.work+1)) :
    sourceSpinMass ((qmaCircuitMatrix c).mulVec u) = sourceSpinMass u :=
  qma_matrix_mass_preserved _ (qmaCircuitMatrix_gram c hc) u

end ContinuumCoulomb

end

end OAI

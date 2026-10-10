import OAI.Analysis.CircleDomains.Sobolev.MetricInterpolation

namespace OAI

/-!
# The separate coordinate energies in the chosen metric

The inverse-matrix trace density is exactly the sum of the nonnegative
squared covector norms. Thus control of the Gram energy controls every
coordinate, and in the identity metric these are the usual squared
Euclidean differential norms.
-/

open Matrix Finset
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def covectorEnergy (v : Fin 2 → ℝ) (g : PlanarMetric) : ℝ :=
  v ⬝ᵥ (g⁻¹ *ᵥ v) * Real.sqrt g.det

theorem covectorEnergy_eq_matrixEnergy (v : Fin 2 → ℝ) (g : PlanarMetric) :
    covectorEnergy v g = matrixEnergy (Matrix.vecMulVec v v) g := by
  rw [matrixEnergy, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
  exact congrArg (fun a : ℝ => a * Real.sqrt g.det) (dotProduct_comm _ _)

theorem covectorEnergy_nonneg (v : Fin 2 → ℝ) {g : PlanarMetric} (hg : g.PosDef) :
    0 ≤ covectorEnergy v g := by
  apply mul_nonneg _ (Real.sqrt_nonneg _)
  simpa only [star_trivial] using hg.inv.posSemidef.dotProduct_mulVec_nonneg v

@[simp] theorem covectorEnergy_identity (a b : ℝ) :
    covectorEnergy ![a,b] 1 = a ^ 2 + b ^ 2 := by
  simp [covectorEnergy, dotProduct, Fin.sum_univ_two, pow_two]

theorem gramEnergy_eq_sum_covectorEnergy (x y : ℕ → ℝ) (n : ℕ) (g : PlanarMetric) :
    matrixEnergy (gramTensor x y n) g =
      ∑ i ∈ range n, covectorEnergy ![x i,y i] g := by
  rw [gramTensor_eq_sum]
  simp only [covectorEnergy_eq_matrixEnergy, matrixEnergy, Finset.mul_sum,
    Matrix.trace_sum, Finset.sum_mul]

theorem covectorEnergy_le_gramEnergy (x y : ℕ → ℝ) {i n : ℕ} (hi : i < n)
    {g : PlanarMetric} (hg : g.PosDef) :
    covectorEnergy ![x i,y i] g ≤ matrixEnergy (gramTensor x y n) g := by
  rw [gramEnergy_eq_sum_covectorEnergy]
  exact single_le_sum (f := fun j => covectorEnergy ![x j,y j] g)
    (fun j _ => covectorEnergy_nonneg _ hg) (mem_range.mpr hi)

theorem gramEnergy_nonneg (x y : ℕ → ℝ) (n : ℕ) {g : PlanarMetric} (hg : g.PosDef) :
    0 ≤ matrixEnergy (gramTensor x y n) g := by
  rw [gramEnergy_eq_sum_covectorEnergy]
  exact sum_nonneg (fun i _ => covectorEnergy_nonneg _ hg)

end CircleDomainRigidity.FiniteTransfer

end

end OAI

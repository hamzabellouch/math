import OAI.Geometry.EinsteinFour.CotangentHamiltonian
import OAI.Geometry.EinsteinFour.MetricInverseCalculus

namespace OAI

/-! The actual kinetic Hamiltonian of the metric in one chart, and the
unit-energy normalization of the cotangent lift of an orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def kineticHamiltonian (g : SmoothMetric M) (c : M)
    (z : CotangentCoordinates) : ℝ :=
  (WithLp.ofLp z.2 ⬝ᵥ ((metricInChart g c z.1)⁻¹ *ᵥ WithLp.ofLp z.2)) / 2

theorem kineticHamiltonian_contDiffAt (g : SmoothMetric M) (c : M)
    (z : CotangentCoordinates) (hz : z.1 ∈ (chartAt FourSpace c).target) :
    ContDiffAt ℝ ∞ (kineticHamiltonian g c) z := by
  have hdet := (metricInChart_posDef g c z.1 hz).det_pos.ne'
  have hG (i j : Fin 4) : ContDiffAt ℝ ∞
      (fun w : CotangentCoordinates => (metricInChart g c w.1)⁻¹ i j) z :=
    (metricInChart_inv_contDiffAt g c z.1 hz hdet i j).comp z contDiffAt_fst
  have hp (i : Fin 4) : ContDiffAt ℝ ∞
      (fun w : CotangentCoordinates => w.2 i) z := by fun_prop
  unfold kineticHamiltonian dotProduct Matrix.mulVec
  apply ContDiffAt.div_const
  apply ContDiffAt.sum
  intro i _
  apply (hp i).mul
  exact ContDiffAt.sum (fun j _ => (hG i j).mul (hp j))

def frameCotangentMomentum (g : SmoothMetric M) (c : M) (x : FourSpace)
    (E : Mat4) (k : Fin 4) : FourSpace :=
  WithLp.toLp 2 (metricInChart g c x *ᵥ fun i => E i k)

/-- Lowering the first chosen frame vector with the metric places it
on the kinetic-energy shell `H = 1/2`. -/
theorem kineticHamiltonian_frame_eq_half (g : SmoothMetric M) (c : M)
    (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (E : Mat4) (hE : Eᵀ * metricInChart g c x * E = 1) (k : Fin 4) :
    kineticHamiltonian g c (x, frameCotangentMomentum g c x E k) = 1 / 2 := by
  let G := metricInChart g c x
  let v : Fin 4 → ℝ := fun i => E i k
  have hinv : G⁻¹ *ᵥ (G *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
      (isUnit_iff_ne_zero.mpr (metricInChart_posDef g c x hx).det_pos.ne'),
      Matrix.one_mulVec]
  have hquad : v ⬝ᵥ (G *ᵥ v) = 1 := by
    calc
      _ = (Eᵀ * G * E) k k := by
        simp only [v, dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
          Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 1 := by rw [show Eᵀ * G * E = 1 from hE]; simp
  change ((G *ᵥ v) ⬝ᵥ (G⁻¹ *ᵥ (G *ᵥ v))) / 2 = 1 / 2
  rw [hinv, dotProduct_comm, hquad]

end
end PositiveEinsteinFour.Geometry

end OAI

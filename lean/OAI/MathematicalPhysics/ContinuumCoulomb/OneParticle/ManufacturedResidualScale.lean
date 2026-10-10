import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabHighAspectRatio
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedOrbitalResidual

namespace OAI

/-! A numerical bound on the actual residual expression used by the full
complement theorem, at the high-aspect slab parameters. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem manufacturedOrbitalSquaredError_tenthPower {rho T freq δ D : ℝ}
    (hrho : 0 ≤ rho) (hT : 2 ≤ T) {m : ℕ} (u : Fin m → PlanarPosition) (j : Fin m) :
    manufacturedOrbitalSquaredError rho (T^10) T freq δ D T u j ≤
      3*((m:ℝ)^2*(PlanarSobolev.wellBound*planarWellMatrixConstant)*Real.exp (-(19/10:ℝ)*D)+
        slabResidualSeventySecondBound rho freq (u j)/T^14+
        ((m:ℝ)*δ*PlanarSobolev.wellBound)^2+
        256*((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2*localizedDensityMoment freq (u j) 8/T^8) := by
  have ht : T ≠ 0 := by linarith
  have htail := slabSeventySecondTail_tenthPower_bound (freq := freq) hrho hT (u j)
  have he : ((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2*
      (localizedDensityMoment freq (u j) 8/(T/2)^8) =
      256*((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2*localizedDensityMoment freq (u j) 8/T^8 := by
    field_simp [ht]
    ring
  unfold manufacturedOrbitalSquaredError
  rw [he]
  linarith

theorem manufacturedResidual_mesh_balance {R a C D B k : ℝ} (hR : 1 ≤ R) :
    a*R^30*(C/(R^5)^14+D/(R^5)^8+B*(k/R^30)^2) =
      a*C/R^40+a*D/R^10+a*B*k^2/R^30 := by
  have hR0 : R ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hR)
  field_simp [hR0]

end ContinuumCoulomb

end

end OAI

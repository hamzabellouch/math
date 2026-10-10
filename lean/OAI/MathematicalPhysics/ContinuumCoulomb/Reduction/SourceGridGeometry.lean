import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.SourceNuclearProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.GridNodePrecision
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.EnumeratedGridNuclei

namespace OAI

/-! Exact scale and box identities for the existing source nuclear program.
The calibrated source-site geometry is handled separately. -/

noncomputable section
namespace ContinuumCoulomb.SourceNuclearProgram

theorem amplification_real (rho k : ℕ) (d : BinaryHeisenberg) :
    (amplification rho k d:ℝ) = (8/(rho:ℝ))*((SourceContactProgram.size d:ℝ)^k)^30 := by
  simp only [amplification,CenteredPhysicalThreshold.amplification,SourcePhysicalThreshold.mesh,
    Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat,Nat.cast_pow]
  rw [← pow_mul,← pow_mul]
  ring

theorem inverse_mesh_real (k : ℕ) (d : BinaryHeisenberg) :
    (SourcePhysicalThreshold.mesh k d:ℝ)⁻¹ = 1/((SourceContactProgram.size d:ℝ)^k)^10 := by
  simp only [SourcePhysicalThreshold.mesh,Nat.cast_pow,one_div,← pow_mul]
  congr 2
  omega

theorem horizontal_bounds (k : ℕ) (d : BinaryHeisenberg) :
    ((SourceContactProgram.size d:ℝ)^k)^50 ≤ (SourcePhysicalThreshold.slabHorizontal k d:ℝ) ∧
      (SourcePhysicalThreshold.slabHorizontal k d:ℝ) ≤ 2*((SourceContactProgram.size d:ℝ)^k)^50 := by
  have h := SourcePhysicalThreshold.slabHorizontal_bounds k d
  exact_mod_cast (show ((SourceContactProgram.size d:ℚ)^k)^50 ≤ SourcePhysicalThreshold.slabHorizontal k d ∧
    SourcePhysicalThreshold.slabHorizontal k d ≤ 2*((SourceContactProgram.size d:ℚ)^k)^50 by
      simpa only [← pow_mul,Nat.cast_pow,show k*50=50*k by omega] using h)

theorem vertical_bounds (k : ℕ) (d : BinaryHeisenberg) :
    ((SourceContactProgram.size d:ℝ)^k)^5 ≤ (SourcePhysicalThreshold.slabVertical k d:ℝ) ∧
      (SourcePhysicalThreshold.slabVertical k d:ℝ) ≤ 2*((SourceContactProgram.size d:ℝ)^k)^5 := by
  have h := SourcePhysicalThreshold.slabVertical_bounds k d
  exact_mod_cast (show ((SourceContactProgram.size d:ℚ)^k)^5 ≤ SourcePhysicalThreshold.slabVertical k d ∧
    SourcePhysicalThreshold.slabVertical k d ≤ 2*((SourceContactProgram.size d:ℚ)^k)^5 by
      simpa only [← pow_mul,Nat.cast_pow,show k*5=5*k by omega] using h)

def radii (k : ℕ) (d : BinaryHeisenberg) : CenteredGaussLabels.Radii :=
  (SourcePhysicalThreshold.horizontalRadius k d,
    (SourcePhysicalThreshold.horizontalRadius k d,SourcePhysicalThreshold.verticalRadius k d))

theorem grid_cover (k : ℕ) (d : BinaryHeisenberg) :
    (⋃ j : {j // j ∈ centeredGridIndices (CenteredGaussLabels.radiiVector (radii k d))},
      positionCube (gaussCellCenter (1/((SourceContactProgram.size d:ℝ)^k)^10) j.val)
        (1/((SourceContactProgram.size d:ℝ)^k)^10)) =
      slabDomain (SourcePhysicalThreshold.slabHorizontal k d) (SourcePhysicalThreshold.slabVertical k d) := by
  rw [← inverse_mesh_real]
  rw [centeredGrid_covers (CenteredGaussLabels.radiiVector (radii k d)) (by
    exact inv_pos.mpr (by exact_mod_cast SourcePhysicalThreshold.mesh_positive k d))]
  ext y
  change (∀ i, |y i| ≤ ((CenteredGaussLabels.radiiVector (radii k d) i:ℝ)+1/2)*
    (SourcePhysicalThreshold.mesh k d:ℝ)⁻¹) ↔ _
  simp only [SourcePhysicalThreshold.slabHorizontal,SourcePhysicalThreshold.slabVertical,
    SlabBoxSchedule.centeredWidth_real,slabDomain,Set.mem_ofPred_eq]
  constructor
  · intro h
    exact ⟨by simpa [CenteredGaussLabels.radiiVector,radii,div_eq_mul_inv] using h 0,
      by simpa [CenteredGaussLabels.radiiVector,radii,div_eq_mul_inv] using h 1,
      by simpa [CenteredGaussLabels.radiiVector,radii,div_eq_mul_inv] using h 2⟩
  · rintro ⟨h0,h1,h2⟩ i
    fin_cases i
    · simpa [CenteredGaussLabels.radiiVector,radii,div_eq_mul_inv] using h0
    · simpa [CenteredGaussLabels.radiiVector,radii,div_eq_mul_inv] using h1
    · simpa [CenteredGaussLabels.radiiVector,radii,div_eq_mul_inv] using h2

theorem factor_amplification {rho : ℕ} (hrho : 0 < rho) (k : ℕ) (d : BinaryHeisenberg) :
    (PhysicalNuclearProgram.factor rho (SourcePhysicalThreshold.mesh k d):ℝ)=
      (amplification rho k d:ℝ)⁻¹ := by
  have hm : (SourcePhysicalThreshold.mesh k d:ℝ) ≠ 0 := by
    exact_mod_cast (SourcePhysicalThreshold.mesh_positive k d).ne'
  have hr : (rho:ℝ) ≠ 0 := by exact_mod_cast hrho.ne'
  rw [PhysicalNuclearProgram.factor_real]
  simp only [amplification,CenteredPhysicalThreshold.amplification,Rat.cast_div,Rat.cast_mul,
    Rat.cast_pow,Rat.cast_ofNat,Rat.cast_natCast]
  field_simp

theorem grid_count (k : ℕ) (d : BinaryHeisenberg) :
    ((CenteredGaussLabels.labels (radii k d)).length:ℝ) ≤
      (SourceContactProgram.size d:ℝ)^(135*k+8) := by
  apply centered_grid_count_power (by exact_mod_cast SourceContactProgram.size_ge_two d) k
  all_goals simp only [radii,SourcePhysicalThreshold.horizontalRadius,SourcePhysicalThreshold.verticalRadius,Nat.cast_pow]; rfl

end ContinuumCoulomb.SourceNuclearProgram

end

end OAI

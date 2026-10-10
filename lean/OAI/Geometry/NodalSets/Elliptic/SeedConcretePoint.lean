import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import OAI.Geometry.NodalSets.Elliptic.SphericalSeed

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff RealInnerProductSpace
noncomputable section

def seedPointVector : SeedAmbient := WithLp.toLp 2 ![1/3,0,2/3,0,2/3]

lemma seedPointVector_norm : ‖seedPointVector‖ = 1 := by
  have h : ⟪seedPointVector,seedPointVector⟫ = (1:ℝ) := by
    rw [PiLp.inner_apply]
    norm_num [seedPointVector,Fin.sum_univ_succ,Matrix.cons_val_succ]
  rw [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg seedPointVector]

def seedPoint : Base := ⟨seedPointVector,mem_sphere_zero_iff_norm.mpr seedPointVector_norm⟩

lemma seedPoint_z1 : seedZ1 (seedPoint : SeedAmbient) = (1/3:ℂ) := by
  norm_num [seedPoint,seedPointVector,seedZ1_apply]

lemma seedPoint_z2 : seedZ2 (seedPoint : SeedAmbient) = (2/3:ℂ) := by
  rw [seedZ2_apply]
  change ((2/3:ℝ):ℂ) + Complex.I * (0:ℂ) = 2/3
  norm_num

lemma seedPoint_quadratic : seedQuadratic (seedPoint : SeedAmbient) = (2/9:ℂ) := by
  rw [seedQuadratic,seedPoint_z1,seedPoint_z2]; norm_num

lemma seedPoint_unequal_radii : ‖seedZ1 (seedPoint : SeedAmbient)‖ ≠
    ‖seedZ2 (seedPoint : SeedAmbient)‖ := by
  rw [seedPoint_z1,seedPoint_z2]; norm_num

lemma seedPoint_slitPlane : seedQuadratic (seedPoint : SeedAmbient) ∈ Complex.slitPlane := by
  rw [seedPoint_quadratic,Complex.mem_slitPlane_iff]
  left; norm_num

lemma sphericalSeed_at_seedPoint (N : ℕ) : sphericalSeed N seedPoint = (2/9:ℝ)^N := by
  simp only [sphericalSeed,ambientRealSeed,ambientComplexSeed,seedPoint_quadratic]
  rw [show (2/9:ℂ) = ((2/9:ℝ):ℂ) by norm_num,← Complex.ofReal_pow,Complex.ofReal_re]

lemma sphericalSeed_nonzero (N : ℕ) : sphericalSeed N ≠ 0 := by
  intro h
  have he := congrFun h seedPoint
  rw [sphericalSeed_at_seedPoint] at he
  exact (pow_ne_zero N (by norm_num : (2/9:ℝ) ≠ 0)) he

end
end Yau.Target

end OAI

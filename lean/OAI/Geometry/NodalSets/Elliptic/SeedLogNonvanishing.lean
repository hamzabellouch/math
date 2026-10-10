import OAI.Geometry.NodalSets.Charts.SphereCovectorRestriction
import OAI.Geometry.NodalSets.Elliptic.SeedLogarithmicBranch

namespace OAI

namespace Yau.Target
open Manifold Set
open scoped ContDiff RealInnerProductSpace
noncomputable section
local instance : Fact (Module.finrank ℝ SeedAmbient = 4+1) := ⟨by simp [SeedAmbient]⟩

def seedRealTestVector : SeedAmbient := WithLp.toLp 2 ![2/3,0,-1/3,0,0]
def seedImagTestVector : SeedAmbient := WithLp.toLp 2 ![0,1,0,0,0]

lemma seedRealTest_tangent : ⟪(seedPoint : SeedAmbient),seedRealTestVector⟫ = (0:ℝ) := by
  rw [PiLp.inner_apply]
  norm_num [seedPoint,seedPointVector,seedRealTestVector,Fin.sum_univ_succ,Matrix.cons_val_succ]

lemma seedImagTest_tangent : ⟪(seedPoint : SeedAmbient),seedImagTestVector⟫ = (0:ℝ) := by
  rw [PiLp.inner_apply]
  norm_num [seedPoint,seedPointVector,seedImagTestVector,Fin.sum_univ_succ,Matrix.cons_val_succ]

lemma seedLog_real_test : fderiv ℝ seedLogReal (seedPoint : SeedAmbient) seedRealTestVector = 3/2 := by
  rw [(seedLogReal_hasFDerivAt seedPoint_mem_logDomain).fderiv]
  simp only [ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul,seedPoint_quadratic,
    seedQuadraticDerivative,add_apply,seedPoint_z1,seedPoint_z2]
  have h1 : seedZ1 seedRealTestVector = (2/3:ℂ) := by
    rw [seedZ1_apply]; change ((2/3:ℝ):ℂ) + Complex.I*0 = 2/3; norm_num
  have h2 : seedZ2 seedRealTestVector = (-1/3:ℂ) := by
    rw [seedZ2_apply]; change ((-1/3:ℝ):ℂ) + Complex.I*0 = -1/3; norm_num
  rw [h1,h2]
  norm_num

lemma seedLog_imag_test : fderiv ℝ seedLogImag (seedPoint : SeedAmbient) seedImagTestVector = 3 := by
  rw [(seedLogImag_hasFDerivAt seedPoint_mem_logDomain).fderiv]
  simp only [ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul,seedPoint_quadratic,
    seedQuadraticDerivative,add_apply,seedPoint_z1,seedPoint_z2]
  have h1 : seedZ1 seedImagTestVector = Complex.I := by
    rw [seedZ1_apply]; change (0:ℂ) + Complex.I*1 = Complex.I; ring
  have h2 : seedZ2 seedImagTestVector = 0 := by
    rw [seedZ2_apply]; change (0:ℂ) + Complex.I*0 = 0; ring
  rw [h1,h2]
  norm_num

lemma sphere_restriction_mfderiv (f : SeedAmbient → ℝ) {x : Base}
    (hf : DifferentiableAt ℝ f (x : SeedAmbient)) :
    mfderiv (𝓡 4) 𝓘(ℝ,ℝ) (fun y : Base ↦ f y) x =
      (fderiv ℝ f (x : SeedAmbient)).comp (sphereAmbientDerivative x) := by
  have h := mfderiv_comp x hf.mdifferentiableAt
    ((contMDiff_coe_sphere (n := 4) (m := ∞)).mdifferentiable (by simp) x)
  rw [mfderiv_eq_fderiv] at h
  exact h

lemma sphere_restriction_differential_ne_zero (f : SeedAmbient → ℝ) {x : Base}
    (hf : DifferentiableAt ℝ f (x : SeedAmbient)) (v : SeedAmbient)
    (hv : ⟪(x : SeedAmbient),v⟫ = (0:ℝ)) (hd : fderiv ℝ f (x : SeedAmbient) v ≠ 0) :
    mfderiv (𝓡 4) 𝓘(ℝ,ℝ) (fun y : Base ↦ f y) x ≠ 0 := by
  have hm : v ∈ (ℝ ∙ (x : SeedAmbient))ᗮ :=
    (Submodule.mem_orthogonal_singleton_iff_inner_left (𝕜 := ℝ) (E := SeedAmbient)).mpr
      (by simpa only [real_inner_comm] using hv)
  rw [← range_mvfderiv_subtypeVal (n := 4)] at hm
  obtain ⟨u,hu⟩ := hm
  intro he
  have hz := congrArg (fun L : TangentSpace (𝓡 4) x →L[ℝ] ℝ ↦ L u) he
  rw [sphere_restriction_mfderiv f hf] at hz
  change fderiv ℝ f (x : SeedAmbient) (sphereAmbientDerivative x u) = 0 at hz
  change sphereAmbientDerivative x u = v at hu
  rw [hu] at hz
  exact hd hz

lemma sphereSeedLogReal_differential_ne_zero :
    mfderiv (𝓡 4) 𝓘(ℝ,ℝ) sphereSeedLogReal seedPoint ≠ 0 := by
  apply sphere_restriction_differential_ne_zero seedLogReal
    (seedLogReal_hasFDerivAt seedPoint_mem_logDomain).differentiableAt
    seedRealTestVector seedRealTest_tangent
  rw [seedLog_real_test]; norm_num

lemma sphereSeedLogImag_differential_ne_zero :
    mfderiv (𝓡 4) 𝓘(ℝ,ℝ) sphereSeedLogImag seedPoint ≠ 0 := by
  apply sphere_restriction_differential_ne_zero seedLogImag
    (seedLogImag_hasFDerivAt seedPoint_mem_logDomain).differentiableAt
    seedImagTestVector seedImagTest_tangent
  rw [seedLog_imag_test]; norm_num

end
end Yau.Target

end OAI

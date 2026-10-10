import OAI.MathematicalPhysics.Boltzmann.Branching.ReferenceCollisionGeometry

namespace OAI

/-! # The exact reflected relative direction in the hard-sphere angular map -/

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

def normalReflectionVector (g n : Velocity) : Velocity := g-(2*inner ℝ g n) • n

theorem normalReflectionVector_norm (g n : Velocity) (hn : ‖n‖ = 1) :
    ‖normalReflectionVector g n‖ = ‖g‖ := by
  have hs : ‖normalReflectionVector g n‖^2 = ‖g‖^2 := by
    unfold normalReflectionVector
    rw [norm_sub_sq_real,real_inner_smul_right,norm_smul]
    simp only [Real.norm_eq_abs,mul_pow,sq_abs,hn,mul_one]
    ring
  nlinarith [norm_nonneg (normalReflectionVector g n),norm_nonneg g]

def normalReflection (e n : Sphere) : Sphere :=
  ⟨normalReflectionVector e.1 n.1,by
    rw [Metric.mem_sphere,dist_zero_right,normalReflectionVector_norm _ _
      (mem_sphere_zero_iff_norm.mp n.property)]
    exact mem_sphere_zero_iff_norm.mp e.property⟩

theorem normalReflection_measurable (e : Sphere) : Measurable (normalReflection e) := by
  unfold normalReflection normalReflectionVector
  fun_prop

theorem normalReflection_neg_normal (e n : Sphere) :
    normalReflectionVector e.1 (-n.1) = normalReflectionVector e.1 n.1 := by
  unfold normalReflectionVector
  simp only [inner_neg_right,mul_neg,neg_smul,smul_neg,neg_neg]

theorem normalReflection_relative_scatter (v w n : Velocity) :
    (1/2:ℝ) • (v+w)+(1/2:ℝ) • normalReflectionVector (v-w) n = scatterLeft v w n := by
  unfold normalReflectionVector scatterLeft normalComponent
  module

theorem normalReflection_relative_scatter_right (v w n : Velocity) :
    (1/2:ℝ) • (v+w)-(1/2:ℝ) • normalReflectionVector (v-w) n = scatterRight v w n := by
  unfold normalReflectionVector scatterRight normalComponent
  module

theorem normalReflectionVector_smul (c : ℝ) (g n : Velocity) :
    normalReflectionVector (c • g) n = c • normalReflectionVector g n := by
  unfold normalReflectionVector
  rw [real_inner_smul_left]
  module

theorem normalReflection_child (e : Sphere) (r : ℝ) (hr : 0 ≤ r)
    (v w : Velocity) (hg : v-w = r • e.1) (n : Sphere) :
    ReferenceGeometry.child v w (normalReflection e n).1 = scatterLeft v w n.1 := by
  have hn : ‖v-w‖ = r := by rw [hg,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,
    mem_sphere_zero_iff_norm.mp e.property,mul_one]
  rw [ReferenceGeometry.child,hn]
  change (1/2:ℝ) • (v+w)+(r/2) • normalReflectionVector e.1 n.1 = _
  rw [← normalReflection_relative_scatter v w n.1,hg,normalReflectionVector_smul]
  module

end BoltzmannNonuniqueness

end

end OAI

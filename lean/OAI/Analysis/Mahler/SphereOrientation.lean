import OAI.Analysis.Mahler.SphereAreaTransport
import OAI.Analysis.Mahler.LogDilation

namespace OAI

open Complex MeasureTheory Metric Set
open scoped Topology

namespace Mahler

/-- The coordinate frame used in the flux density is Euclidean orthonormal. -/
lemma interleavedBasis_orthonormal (n : ℕ) : Orthonormal ℝ (interleavedBasis (n := n)) := by
  classical
  rw [orthonormal_iff_ite]
  intro a b
  obtain ⟨i,α,ha⟩ : ∃ i α, pairSlotEquiv n a = (i,α) := ⟨_,_,rfl⟩
  obtain ⟨j,β,hb⟩ : ∃ j β, pairSlotEquiv n b = (j,β) := ⟨_,_,rfl⟩
  have hab : a = b ↔ i = j ∧ α = β := by
    rw [← (pairSlotEquiv n).injective.eq_iff, ha, hb, Prod.mk.injEq]
  simp only [interleavedBasis, ha, hb]
  fin_cases α <;> fin_cases β <;> by_cases hij : i = j <;>
    simp [PiLp.inner_apply, Complex.inner, hab, hij, eq_comm, apply_ite]

lemma sphereFluxFrame_orthonormal (k : ℕ) : Orthonormal ℝ (sphereFluxFrame k) := by
  classical
  rw [orthonormal_iff_ite]
  intro a b
  simpa [sphereFluxFrame, Function.comp_def] using
    (orthonormal_iff_ite.mp (interleavedBasis_orthonormal (k+1))
      (sphereFrameSlots k a) (sphereFrameSlots k b))

lemma sphereNormal_outward {n : ℕ} (z : sphere (0 : ComplexEuclidean n) 1) :
    sphereNormal (z : ComplexEuclidean n) (fun _ => (z : ComplexEuclidean n)) = 1 := by
  change (inner ℝ (z : ComplexEuclidean n) (z : ComplexEuclidean n) : ℂ) = 1
  have hz : ‖(z : ComplexEuclidean n)‖ = 1 := by simp
  rw [real_inner_self_eq_norm_sq, hz]
  norm_num

lemma sphereNormal_tangent {n : ℕ} (z : ComplexEuclidean n) (v : sphereTangent z) :
    sphereNormal z (fun _ => (v : ComplexEuclidean n)) = 0 := by
  change (inner ℝ z (v : ComplexEuclidean n) : ℂ) = 0
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right.mp v.property]
  rfl

lemma sphereDilation_surjective {n : ℕ} (r : ℝ) (hr : 0 < r) :
    Function.Surjective (sphereDilation (n := n) r hr) := by
  intro z
  have hz : ‖(z : ComplexEuclidean n)‖ = r := by simp
  let w : sphere (0 : ComplexEuclidean n) 1 := ⟨r⁻¹ • (z : ComplexEuclidean n), by
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hz, hr.ne']⟩
  refine ⟨w, ?_⟩
  apply Subtype.ext
  change r • (r⁻¹ • (z : ComplexEuclidean n)) = z
  simp [smul_smul, hr.ne']

lemma continuous_radiusFluxDensity {k : ℕ} {u : ComplexEuclidean (k+1) → ℂ} (r : ℝ)
    (hu : ∀ z : sphere (0 : ComplexEuclidean (k+1)) r,
      ContDiffAt ℝ 2 u (z : ComplexEuclidean (k+1))) :
    Continuous (fun z : sphere (0 : ComplexEuclidean (k+1)) r =>
      sphereDensity k (r⁻¹ • (z : ComplexEuclidean (k+1))) (boundaryForm u k z)) := by
  have hc : ContinuousOn (actualRealComplexJet u) (sphere (0 : ComplexEuclidean (k+1)) r) :=
    continuousOn_actualRealComplexJet (fun x hx => hu ⟨x,hx⟩)
  have hj : Continuous (fun z : sphere (0 : ComplexEuclidean (k+1)) r => actualRealComplexJet u z) :=
    hc.comp_continuous continuous_subtype_val (fun z => z.property)
  have hn : Continuous (fun z : sphere (0 : ComplexEuclidean (k+1)) r => r⁻¹ • (z : ComplexEuclidean (k+1))) :=
    (continuous_const : Continuous (fun _ : sphere (0 : ComplexEuclidean (k+1)) r => r⁻¹)).smul
      (continuous_subtype_val : Continuous (fun z : sphere (0 : ComplexEuclidean (k+1)) r => (z : ComplexEuclidean (k+1))))
  have ht := (continuous_sphereJetDensity k).comp (hn.prodMk hj)
  convert ht using 1
  funext z
  exact congrArg (sphereDensity k (r⁻¹ • (z : ComplexEuclidean (k+1))))
    (boundaryForm_eq_jet ((hu z).fderiv_right (m := 1) (by norm_num)
      |>.differentiableAt (by norm_num)) k)

/-- Flux on the radius-r sphere itself. For nonpositive radii we use zero;
this branch is irrelevant to the right-sided small-sphere limit. -/
noncomputable def radiusSphereFlux (k : ℕ) (u : ComplexEuclidean (k+1) → ℂ) (r : ℝ) : ℂ :=
  if hr : 0 < r then
    ∫ z : sphere (0 : ComplexEuclidean (k+1)) r,
      sphereDensity k (r⁻¹ • (z : ComplexEuclidean (k+1))) (boundaryForm u k z)
        ∂radiusSphereArea (k+1) r hr
  else 0

/-- No measurability premise is needed: C2 regularity supplies it. -/
theorem radiusSphereFlux_eq_small {k : ℕ} {u : ComplexEuclidean (k+1) → ℂ}
    (r : ℝ) (hr : 0 < r)
    (hu : ∀ z : sphere (0 : ComplexEuclidean (k+1)) r,
      ContDiffAt ℝ 2 u (z : ComplexEuclidean (k+1))) :
    radiusSphereFlux k u r = smallSphereFlux k u r := by
  rw [radiusSphereFlux, dite_eq_left hr]
  exact (smallSphereFlux_eq_radiusIntegral u r hr
    (continuous_radiusFluxDensity r hu).aestronglyMeasurable).symm

end Mahler

end OAI

import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneCompactIntegration

namespace OAI

/-! The weak transport-diffusion identity with compact spatial tests.
The scalar may have a noncompact diffusion tail. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows PlanarHamiltonian Set MeasureTheory
open scoped ContDiff BigOperators

theorem integral_compact_transport {φ g : Plane → ℝ} {a : Plane → Plane}
    (hφ : ContDiff ℝ ∞ φ) (hg : ContDiff ℝ ∞ g) (ha : ContDiff ℝ ∞ a)
    (hc : HasCompactSupport φ) (hdiv : ∀ x, divergence a x = 0) :
    (∫ x, φ x * fderiv ℝ g x (a x)) = -(∫ x, g x * fderiv ℝ φ x (a x)) := by
  have hi (j : Fin 2) : Integrable (fun x => (φ x * a x j) * spatialD j g x) :=
    ((hφ.mul ((contDiff_apply ℝ ℝ j).comp ha)).mul (spatialD_smooth j hg)).continuous.integrable_of_hasCompactSupport hc.mul_right.mul_right
  have hj (j : Fin 2) : Integrable (fun x => g x * spatialD j (fun y => φ y * a y j) x) :=
    (hg.mul (spatialD_smooth j (hφ.mul ((contDiff_apply ℝ ℝ j).comp ha)))).continuous.integrable_of_hasCompactSupport
        ((hc.mul_right).fderiv_apply ℝ (basis j)).mul_left
  have he (x : Plane) :
      (∑ j : Fin 2, g x * spatialD j (fun y => φ y * a y j) x) =
        g x * fderiv ℝ φ x (a x) := by
    have hz : spatialD 0 (fun y => a y 0) x + spatialD 1 (fun y => a y 1) x = 0 := by
      simpa only [PlanarHamiltonian.divergence, Fin.sum_univ_two] using hdiv x
    have ha0 : ContDiff ℝ ∞ (fun y : Plane => a y 0) :=
      (contDiff_apply ℝ ℝ 0).comp ha
    have ha1 : ContDiff ℝ ∞ (fun y : Plane => a y 1) :=
      (contDiff_apply ℝ ℝ 1).comp ha
    simp only [Fin.sum_univ_two]
    rw [spatialD_mul hφ ha0, spatialD_mul hφ ha1,
      scalar_directional_basis, Fin.sum_univ_two]
    linear_combination (g x * φ x) * hz

  calc
    _ = ∫ x, ∑ j : Fin 2, (φ x * a x j) * spatialD j g x := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [scalar_directional_basis, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ j : Fin 2, ∫ x, (φ x * a x j) * spatialD j g x :=
      integral_finsetSum Finset.univ (fun j _ => hi j)
    _ = ∑ j : Fin 2, -(∫ x, g x * spatialD j (fun y => φ y * a y j) x) := by
      apply Finset.sum_congr rfl
      intro j _
      exact integral_compact_spatialD (hφ.mul ((contDiff_apply ℝ ℝ j).comp ha)) hg
        hc.mul_right j
    _ = -(∫ x, ∑ j : Fin 2, g x * spatialD j (fun y => φ y * a y j) x) := by
      rw [integral_finsetSum Finset.univ (fun j _ => hj j), Finset.sum_neg_distrib]
    _ = _ := by simp_rw [he]

theorem integral_compact_generator {φ g : Plane → ℝ} {a : Plane → Plane}
    (hφ : ContDiff ℝ ∞ φ) (hg : ContDiff ℝ ∞ g) (ha : ContDiff ℝ ∞ a)
    (hc : HasCompactSupport φ) (hdiv : ∀ x, divergence a x = 0) (ν : ℝ) :
    (∫ x, φ x * scalarGenerator ν a g x) =
      ∫ x, g x * (ν * scalarLaplacian φ x + fderiv ℝ φ x (a x)) := by
  have hl : ContDiff ℝ ∞ (scalarLaplacian g) := by
    unfold scalarLaplacian
    exact ContDiff.sum (fun j _ => spatialD_smooth j (spatialD_smooth j hg))
  have hd := (hg.fderiv_right (m := ∞) (by simp)).clm_apply ha
  have hpl : Integrable (fun x => φ x * scalarLaplacian g x) :=
    (hφ.mul hl).continuous.integrable_of_hasCompactSupport hc.mul_right
  have hpd : Integrable (fun x => φ x * fderiv ℝ g x (a x)) :=
    (hφ.mul hd).continuous.integrable_of_hasCompactSupport hc.mul_right
  have hdl : Integrable (fun x => g x * scalarLaplacian φ x) := by
    have hh : ContDiff ℝ ∞ (scalarLaplacian φ) := by
      unfold scalarLaplacian
      exact ContDiff.sum (fun j _ => spatialD_smooth j (spatialD_smooth j hφ))
    have hs : HasCompactSupport (scalarLaplacian φ) := by
      have he : scalarLaplacian φ = (fun x => spatialD 0 (spatialD 0 φ) x +
          spatialD 1 (spatialD 1 φ) x) := by
        funext x
        simp only [scalarLaplacian, Fin.sum_univ_two]
      rw [he]
      exact ((hc.fderiv_apply ℝ (basis 0)).fderiv_apply ℝ (basis 0)).add
        ((hc.fderiv_apply ℝ (basis 1)).fderiv_apply ℝ (basis 1))
    exact (hg.mul hh).continuous.integrable_of_hasCompactSupport hs.mul_left
  have hsupport : HasCompactSupport (fun x => fderiv ℝ φ x (a x)) := by
    apply hc.mono'
    intro x hx
    by_contra hn
    exact hx (by simp [fderiv_of_notMem_tsupport ℝ hn])
  have hdd : Integrable (fun x => g x * fderiv ℝ φ x (a x)) :=
    (hg.mul ((hφ.fderiv_right (m := ∞) (by simp)).clm_apply ha)).continuous.integrable_of_hasCompactSupport hsupport.mul_left
  have he (x : Plane) : φ x * scalarGenerator ν a g x =
      ν * (φ x * scalarLaplacian g x) - φ x * fderiv ℝ g x (a x) := by
    unfold scalarGenerator
    ring
  have hf (x : Plane) : g x * (ν * scalarLaplacian φ x + fderiv ℝ φ x (a x)) =
      ν * (g x * scalarLaplacian φ x) + g x * fderiv ℝ φ x (a x) := by ring
  simp_rw [he, hf]
  rw [integral_sub (hpl.const_mul ν) hpd, integral_add (hdl.const_mul ν) hdd,
    integral_const_mul, integral_const_mul,
    integral_compact_laplacian hφ hg hc, integral_compact_transport hφ hg ha hc hdiv]
  ring

end ForcedComputation.VelocityDetector

end

end OAI

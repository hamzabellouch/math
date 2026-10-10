import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CompactDetectorCenter

namespace OAI

/-! Spatial translation of the scalar equation and its torus mass.  The
center is an arbitrary real point; no rationality restriction is imposed. -/

noncomputable section
namespace ForcedComputation.VelocityDetector.CompactCenter
open ShearFlows PlanarHamiltonian Set MeasureTheory
open scoped ContDiff BigOperators

theorem spatialD_translated (δ : Plane) (f : Plane → ℝ) (j : Fin 2) (x : Plane) :
    spatialD j (fun y => f (y + δ)) x = spatialD j f (x + δ) := by
  unfold spatialD
  rw [fderiv_comp_add_right]

theorem scalarLaplacian_translated (δ : Plane) (f : Plane → ℝ) (x : Plane) :
    scalarLaplacian (fun y => f (y + δ)) x = scalarLaplacian f (x + δ) := by
  unfold scalarLaplacian
  apply Finset.sum_congr rfl
  intro j _
  have he : spatialD j (fun y => f (y + δ)) = fun y => spatialD j f (y + δ) :=
    funext (spatialD_translated δ f j)
  rw [he, spatialD_translated]

theorem scalarGenerator_translated (δ : Plane) (ν : ℝ) (a : Plane → Plane)
    (f : Plane → ℝ) (x : Plane) :
    scalarGenerator ν (fun y => a (y + δ)) (fun y => f (y + δ)) x =
      scalarGenerator ν a f (x + δ) := by
  simp only [scalarGenerator, scalarLaplacian_translated, fderiv_comp_add_right]

theorem scalar_solution_translated {T ν : ℝ} {a : ℝ → Plane → Plane}
    {h w : ℝ → Plane → ℝ} {w₀ : Plane → ℝ}
    (hw : TorusScalarSolution T ν a h w w₀) (δ : Plane) :
    TorusScalarSolution T ν (translateField δ a) (translateField δ h)
      (translateField δ w) (fun x => w₀ (x + δ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hg : ContDiff ℝ ∞ (fun y : ℝ × Plane => (y.1, y.2 + δ)) :=
      contDiff_fst.prodMk (contDiff_snd.add contDiff_const)
    exact hw.smooth.comp hg.contDiffOn (fun y hy => ⟨hy.1, mem_univ _⟩)
  · intro t ht
    exact translated_periodic δ (fun _ => hw.periodic t ht) t
  · funext x
    exact congrFun hw.initial (x + δ)
  · intro t ht x
    change HasDerivWithinAt (fun s => w s (x + δ))
      (scalarGenerator ν (fun y => a t (y + δ)) (fun y => w t (y + δ)) x + h t (x + δ))
      (Icc 0 T) t
    rw [scalarGenerator_translated]
    exact hw.equation t ht (x + δ)

theorem global_scalar_solution_translated {ν : ℝ} {a : ℝ → Plane → Plane}
    {h w : ℝ → Plane → ℝ} {w₀ : Plane → ℝ}
    (hw : GlobalTorusScalarSolution ν a h w w₀) (δ : Plane) :
    GlobalTorusScalarSolution ν (translateField δ a) (translateField δ h)
      (translateField δ w) (fun x => w₀ (x + δ)) :=
  fun T hT => scalar_solution_translated (hw T hT) δ

/-- Translation preserves the integral over the torus.  The proof uses
the zero integral of each periodic derivative along the translation path. -/
theorem integral_translated {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PlanePeriodic f) (δ : Plane) :
    (∫ x in Icc (0 : Plane) (fun _ => 1), f (x + δ)) =
      ∫ x in Icc (0 : Plane) (fun _ => 1), f x := by
  let W : ℝ → Plane → ℝ := fun s x => f (x + s • δ)
  let D : ℝ → Plane → ℝ := fun s x => fderiv ℝ f (x + s • δ) δ
  have hW : ContDiff ℝ ∞ (Function.uncurry W) :=
    hf.comp (contDiff_snd.add (contDiff_fst.smul contDiff_const))
  have hD : Continuous (Function.uncurry D) :=
    ((hf.fderiv_right (m := ∞) (by simp)).comp
      (contDiff_snd.add (contDiff_fst.smul contDiff_const))).continuous.clm_apply
        continuous_const
  have hderiv (s : ℝ) (x : Plane) : HasDerivAt (fun r => W r x) (D s x) s := by
    have hi := ((hasDerivAt_id s).smul_const δ).const_add x
    have hd := ((hf.differentiable (by simp) (x + s • δ)).hasFDerivAt).comp_hasDerivAt s hi
    simpa only [Function.comp_def, id_eq, one_smul] using hd
  have hzero (s : ℝ) : scalarMass D s = 0 := by
    let g : Plane → ℝ := fun x => f (x + s • δ)
    have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_id.add contDiff_const)
    have hpg : PlanePeriodic g := translated_periodic (s • δ) (fun _ => hp) 0
    have he (x : Plane) : D s x = ∑ j : Fin 2, δ j * spatialD j g x := by
      rw [← scalar_directional_basis]
      exact congrArg (fun A : Plane →L[ℝ] ℝ => A δ) (fderiv_comp_add_right (s • δ)).symm
    unfold scalarMass
    simp_rw [he]
    rw [integral_finsetSum]
    · apply Finset.sum_eq_zero
      intro j _
      rw [integral_const_mul]
      change δ j * (∫ x in Icc (0 : Plane) (fun _ => 1),
        fderiv ℝ g x (PlanarHamiltonian.basis j)) = 0
      rw [integral_planar_periodic_derivative hg hpg j, mul_zero]
    · intro j _
      exact ((spatialD_smooth j hg).continuous.const_mul _).integrableOn_Icc
  have hm (s : ℝ) : HasDerivAt (scalarMass W) 0 s := by
    simpa only [hzero] using scalarMass_hasDerivAt hW.continuous hD hderiv s
  have he := is_const_of_deriv_eq_zero (fun s => (hm s).differentiableAt)
    (fun s => (hm s).deriv) (1 : ℝ) 0
  simpa only [scalarMass, W, one_smul, zero_smul, add_zero] using he

theorem scalarMass_translated {w : ℝ → Plane → ℝ}
    (hw : ContDiff ℝ ∞ (Function.uncurry w)) (hp : ∀ t, PlanePeriodic (w t))
    (δ : Plane) (t : ℝ) : scalarMass (translateField δ w) t = scalarMass w t :=
  integral_translated (hw.comp (contDiff_const.prodMk contDiff_id)) (hp t) δ

end ForcedComputation.VelocityDetector.CompactCenter

end

end OAI

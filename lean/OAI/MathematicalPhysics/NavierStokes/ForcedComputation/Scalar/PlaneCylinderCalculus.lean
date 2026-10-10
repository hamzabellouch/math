import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneInteriorCalculus

namespace OAI

/-! Spatial differentiation preserves smoothness on a closed time cylinder.
Only spatial directions are used at the two time endpoints. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows PlanarHamiltonian Set
open scoped ContDiff

theorem planeWithinD_spatial {T : ℝ} {f : ℝ × Plane → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Icc 0 T ×ˢ univ))
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Plane) (j : Fin 2) :
    fderivWithin ℝ f (Icc 0 T ×ˢ univ) (t, x) (0, basis j) =
      spatialD j (fun y => f (t, y)) x := by
  have hd := (hf.differentiableOn (by simp) (t, x) ⟨ht, mem_univ x⟩).hasFDerivWithinAt
  have hi := (hasFDerivAt_const (𝕜 := ℝ) t x).prodMk (hasFDerivAt_id (𝕜 := ℝ) x)
  have hc := hd.comp_hasFDerivAt x hi
    (Filter.Eventually.of_forall (fun y => ⟨ht, mem_univ y⟩))
  change _ = fderiv ℝ (fun y => f (t, y)) x (basis j)
  have hce := hc.fderiv
  change fderiv ℝ (fun y => f (t, y)) x = _ at hce
  rw [hce]
  simp

theorem spatialD_contDiffOn_cylinder {T : ℝ} (hT : 0 < T)
    {f : ℝ × Plane → ℝ} (hf : ContDiffOn ℝ ∞ f (Icc 0 T ×ˢ univ))
    (j : Fin 2) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Plane => spatialD j (fun y => f (p.1, y)) p.2)
      (Icc 0 T ×ˢ univ) := by
  have hS : UniqueDiffOn ℝ (Icc 0 T ×ˢ (univ : Set Plane)) :=
    (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ
  have hd : ContDiffOn ℝ ∞
      (fun p => fderivWithin ℝ f (Icc 0 T ×ˢ univ) p (0, basis j))
      (Icc 0 T ×ˢ univ) :=
    (hf.fderivWithin hS (by simp)).clm_apply contDiffOn_const
  apply hd.congr
  rintro ⟨t, x⟩ hp
  exact (planeWithinD_spatial hf hp.1 x j).symm

theorem PlaneScalarSolution.cylinder_spatialD {T ν : ℝ}
    {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : PlaneScalarSolution T ν a h w) (hT : 0 < T) (j : Fin 2) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Plane => spatialD j (w p.1) p.2)
      (Icc 0 T ×ˢ univ) := by
  simpa only [Function.uncurry_apply_pair] using spatialD_contDiffOn_cylinder hT hw.smooth j

theorem PlaneScalarSolution.cylinder_second_spatialD {T ν : ℝ}
    {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : PlaneScalarSolution T ν a h w) (hT : 0 < T) (j k : Fin 2) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Plane => spatialD j (spatialD k (w p.1)) p.2)
      (Icc 0 T ×ˢ univ) :=
  spatialD_contDiffOn_cylinder hT (hw.cylinder_spatialD hT k) j

end ForcedComputation.VelocityDetector

end

end OAI

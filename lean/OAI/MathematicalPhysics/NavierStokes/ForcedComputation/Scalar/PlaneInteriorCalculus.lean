import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarInput
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarMassCalculus

namespace OAI

/-! Joint interior derivatives of a finite-cylinder scalar solution. These
lemmas use only the smoothness supplied by the narrow existence input. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows PlanarHamiltonian Set
open scoped ContDiff

def planeJointD (v : ℝ × Plane) (f : ℝ × Plane → ℝ) (p : ℝ × Plane) : ℝ :=
  fderiv ℝ f p v

theorem planeJointD_smoothOn {f : ℝ × Plane → ℝ} {S : Set (ℝ × Plane)}
    (hf : ContDiffOn ℝ ∞ f S) (hS : IsOpen S) (v : ℝ × Plane) :
    ContDiffOn ℝ ∞ (planeJointD v f) S :=
  (hf.fderiv_of_isOpen hS (by simp)).clm_apply contDiffOn_const

theorem planeJointD_spatial {f : ℝ × Plane → ℝ} {t : ℝ} {x : Plane}
    (hf : DifferentiableAt ℝ f (t, x)) (j : Fin 2) :
    planeJointD (0, basis j) f (t, x) = spatialD j (fun y => f (t, y)) x := by
  have hh := hf.hasFDerivAt.comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  change _ = fderiv ℝ (fun y => f (t, y)) x (basis j)
  change HasFDerivAt (fun y => f (t, y)) _ x at hh
  rw [hh.fderiv]
  simp [planeJointD]

theorem PlaneScalarSolution.interior_smooth {T ν : ℝ} {a : ℝ → Plane → Plane}
    {h w : ℝ → Plane → ℝ} (hw : PlaneScalarSolution T ν a h w) :
    ContDiffOn ℝ ∞ (Function.uncurry w) (Ioo 0 T ×ˢ univ) :=
  hw.smooth.mono (fun _ hp => ⟨Ioo_subset_Icc_self hp.1, hp.2⟩)

theorem PlaneScalarSolution.interior_spatialD {T ν : ℝ} {a : ℝ → Plane → Plane}
    {h w : ℝ → Plane → ℝ} (hw : PlaneScalarSolution T ν a h w) (j : Fin 2) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Plane => spatialD j (w p.1) p.2)
      (Ioo 0 T ×ˢ univ) := by
  have ho : IsOpen (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) := isOpen_Ioo.prod isOpen_univ
  apply (planeJointD_smoothOn hw.interior_smooth ho (0, basis j)).congr
  intro p hp
  exact (planeJointD_spatial
    ((hw.interior_smooth.contDiffAt (ho.mem_nhds hp)).differentiableAt (by simp)) j).symm

theorem PlaneScalarSolution.interior_laplacian {T ν : ℝ} {a : ℝ → Plane → Plane}
    {h w : ℝ → Plane → ℝ} (hw : PlaneScalarSolution T ν a h w) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Plane => scalarLaplacian (w p.1) p.2)
      (Ioo 0 T ×ˢ univ) := by
  have ho : IsOpen (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) := isOpen_Ioo.prod isOpen_univ
  have hh (j : Fin 2) : ContDiffOn ℝ ∞
      (fun p : ℝ × Plane => spatialD j (spatialD j (w p.1)) p.2)
      (Ioo 0 T ×ˢ univ) := by
    apply (planeJointD_smoothOn (hw.interior_spatialD j) ho (0, basis j)).congr
    intro p hp
    exact (planeJointD_spatial
      (((hw.interior_spatialD j).contDiffAt (ho.mem_nhds hp)).differentiableAt (by simp)) j).symm
  exact ContDiffOn.sum (fun j _ => hh j)

theorem PlaneScalarSolution.interior_generator {T ν : ℝ} {a : ℝ → Plane → Plane}
    {h w : ℝ → Plane → ℝ} (hw : PlaneScalarSolution T ν a h w)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Plane => scalarGenerator ν (a p.1) (w p.1) p.2)
      (Ioo 0 T ×ˢ univ) := by
  have hprod : ContDiffOn ℝ ∞
      (fun p : ℝ × Plane => ∑ j : Fin 2, a p.1 p.2 j * spatialD j (w p.1) p.2)
      (Ioo 0 T ×ˢ univ) :=
    ContDiffOn.sum (fun j _ => ((contDiff_apply ℝ ℝ j).comp ha).contDiffOn.mul
      (hw.interior_spatialD j))
  have hc : ContDiffOn ℝ ∞ (fun p : ℝ × Plane => ν * scalarLaplacian (w p.1) p.2)
      (Ioo 0 T ×ˢ univ) := contDiffOn_const.mul hw.interior_laplacian
  have hh := hc.sub hprod
  exact hh.congr (fun p _ => by rw [scalarGenerator, scalar_directional_basis])

end ForcedComputation.VelocityDetector

end

end OAI

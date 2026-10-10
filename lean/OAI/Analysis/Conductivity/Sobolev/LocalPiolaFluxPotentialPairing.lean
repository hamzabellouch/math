import Mathlib
import OAI.Analysis.Conductivity.Sobolev.LocalPiolaFlux

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
namespace ScalarConductivity

theorem localPiolaFlux_potential_pairing
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (X : OpenPartialHomeomorph E E) (hX : DifferentiableOn ℝ X X.source)
    (hXi : DifferentiableOn ℝ X.symm X.target)
    (D : E →L[ℝ] V) (u : E → V)
    (hu : ∀ y ∈ X.source, D (X y) = u y) (F : E → E)
    {y : E} (hy : y ∈ X.source) :
    fderiv ℝ u y (localPiolaFlux X.symm F y) =
      |(fderiv ℝ X.symm (X y)).det|⁻¹ • D (F (X y)) := by
  classical
  have hxy := X.map_source hy
  have he : u =ᶠ[𝓝 y] D ∘ X := by
    filter_upwards [X.open_source.mem_nhds hy] with z hz
    exact (hu z hz).symm
  have hd := (hX y hy).differentiableAt (X.open_source.mem_nhds hy)
  have hinv := local_fderiv_symm_comp X.symm hXi hX hxy
  simp only [OpenPartialHomeomorph.symm_symm, X.left_inv hy] at hinv
  rw [he.fderiv_eq, fderiv_comp y D.differentiableAt hd, D.fderiv]
  have hflux : localPiolaFlux X.symm F y =
      |(fderiv ℝ X.symm (X y)).det|⁻¹ • (fderiv ℝ X.symm (X y)) (F (X y)) := by
    simp [localPiolaFlux, hy]
  rw [ContinuousLinearMap.comp_apply, hflux, map_smul, map_smul]
  congr 1
  exact congrArg D (congrArg (fun T : E →L[ℝ] E => T (F (X y))) hinv)

end ScalarConductivity

end

end OAI

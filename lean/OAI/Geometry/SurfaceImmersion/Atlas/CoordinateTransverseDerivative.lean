import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateAxisDerivative
import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapDerivativeNonzero

namespace OAI

/-! The transverse coordinate derivative never vanishes at a rank-one
crosscap whose longitudinal coordinate is the kernel. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma horizontal_ne_zero_of_vertical_zero (L : Base →L[ℝ] V)
    (hL : L ≠ 0) (hv : L (![0,1] : Base) = 0) : L (![1,0] : Base) ≠ 0 := by
  intro hh
  apply hL
  ext x
  have hx : x = (x 0) • (![1,0] : Base) + (x 1) • (![0,1] : Base) := by
    ext i
    fin_cases i <;> simp
  rw [hx,map_add,map_smul,map_smul,hh,hv]
  simp

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma coordinate_representative_derivative_ne_zero (c : OpenPartialHomeomorph M Base)
    (hcs : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source)
    (hci : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target)
    {f : M → V} (hf : ContMDiff planeModel 𝓘(ℝ,V) ∞ f)
    {φ : Base → V} {U : Set Base} (hU : IsOpen U) (hUt : U ⊆ c.target)
    (hEq : EqOn φ (f ∘ c.symm) U) {x : Base} (hx : x ∈ U)
    (hn : mfderiv planeModel 𝓘(ℝ,V) f (c.symm x) ≠ 0) : fderiv ℝ φ x ≠ 0 := by
  intro hz
  apply hn
  have hcD : c.symm.MDifferentiable 𝓘(ℝ,Base) planeModel :=
    ⟨hci.mdifferentiableOn (by simp),hcs.mdifferentiableOn (by simp)⟩
  have hsur := (hcD.mfderiv_bijective (hUt hx)).2
  rw [(hEq.eventuallyEq_of_mem (hU.mem_nhds hx)).fderiv_eq,← mfderiv_eq_fderiv,
    mfderiv_comp x (hf.mdifferentiable (by simp) _) (hcD.mdifferentiableAt (hUt hx))] at hz
  ext v
  obtain ⟨w,rfl⟩ := hsur v
  exact congrArg (fun L => L w) hz

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

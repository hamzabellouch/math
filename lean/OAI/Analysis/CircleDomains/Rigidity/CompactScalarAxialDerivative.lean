import OAI.Analysis.CircleDomains.Rigidity.AxialLineDifferentiation

namespace OAI

/-! A scalar test agreeing with an axial coordinate near a source point
has exactly the same line derivative there. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem compact_scalar_axial_deriv_le {W : Set ℂ} (hW : IsOpen W)
    {b : ℂ → ℝ} {F : ℂ → ℂ} (i k : Fin 2) (y x : ℝ)
    (hx : complexCoordinateLine i y x ∈ W)
    (hF : DifferentiableAt ℂ F (complexCoordinateLine i y x))
    (hb : ∀ z ∈ W, b z = (complexPlaneCoordinates.symm (F z)) k) :
    |deriv (fun t => b (complexCoordinateLine i y t)) x| ≤
      ‖deriv F (complexCoordinateLine i y x)‖ := by
  have he : (fun t => b (complexCoordinateLine i y t)) =ᶠ[𝓝 x]
      (fun t => (complexPlaneCoordinates.symm (F (complexCoordinateLine i y t))) k) := by
    filter_upwards [((complexCoordinateLine_contDiff i y).continuous.continuousAt.preimage_mem_nhds
      (hW.mem_nhds hx))] with t ht
    exact hb _ ht
  rw [he.deriv_eq]
  exact axial_coordinate_deriv_le i k y x hF

end CircleDomainRigidity

end

end OAI

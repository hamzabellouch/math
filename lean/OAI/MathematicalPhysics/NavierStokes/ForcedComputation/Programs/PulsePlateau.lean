import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarSegments

namespace OAI

/-! Exact local motion on the open plateau surrounding a pulse rectangle.
The explicit collar allows source neighborhoods, rather than only the closed
source rectangles, to follow the same affine motion. -/

noncomputable section
namespace ForcedComputation.PlanarHamiltonian
open ShearFlows Set Filter
open scoped Topology

theorem rectangleCutoff_one_near_plateau {R : RationalBox 2} {δ : ℚ}
    (hδ : 0 < δ) {x : Plane} (hx : x ∈ rectanglePlateau R δ) :
    rectangleCutoff R δ =ᶠ[𝓝 x] fun _ => 1 :=
  Filter.eventually_of_mem ((rectanglePlateau_open R δ).mem_nhds hx)
    (fun _ hy => rectangleCutoff_one hδ hy)

theorem Pulse.spatial_on_plateau {p : Pulse} (hp : p.Valid) {x : Plane}
    (hx : x ∈ rectanglePlateau p.rectangle p.collar) :
    p.spatial x = field p.primitive.potential x := by
  exact field_cutoff_plateau _ _ (rectangleCutoff_one_near_plateau hp.1 hx)

theorem Pulse.curve_ode_plateau {p : Pulse} (hp : p.Valid) (x : Plane) (t : ℝ)
    (hx : p.curve x t ∈ rectanglePlateau p.rectangle p.collar) :
    HasDerivAt (p.curve x) (p.velocity t (p.curve x t)) t := by
  rw [Pulse.velocity, p.spatial_on_plateau hp hx]
  exact p.primitive.path_hasDerivAt x
    (((smoothRamp_smooth p.start p.finish).differentiable (by simp) t).hasDerivAt)

/-- A perturbation smaller than the rational collar remains on the exact
polynomial plateau. The norm here is the coordinate maximum norm. -/
theorem rectanglePlateau_of_dist_lt {R : RationalBox 2} {δ : ℚ}
    {x y : Plane} (hx : x ∈ R.carrier) (hxy : dist y x < (δ : ℝ)) :
    y ∈ rectanglePlateau R δ := by
  intro j
  have hj : |y j - x j| < (δ : ℝ) :=
    (norm_le_pi_norm (y - x) j).trans_lt (by simpa only [dist_eq_norm] using hxy)
  obtain ⟨hj₀, hj₁⟩ := abs_lt.mp hj
  constructor <;> linarith [(hx j).1, (hx j).2]

/-- Endpoint-gap separation survives a controlled perturbation. -/
theorem notMem_collar_of_dist_lt {R S : RationalBox 2} {gap δ ε : ℚ}
    (hgap : PlanarRouting.EndpointGap gap R S) (hsmall : 2 * δ + ε ≤ gap)
    {x y : Plane} (hx : x ∈ S.carrier) (hxy : dist y x < (ε : ℝ)) :
    y ∉ (rectangleCollar R δ).carrier := by
  obtain ⟨j, hj⟩ := hgap
  have hdist : |y j - x j| < (ε : ℝ) :=
    (norm_le_pi_norm (y - x) j).trans_lt (by simpa only [dist_eq_norm] using hxy)
  obtain ⟨hd₀, hd₁⟩ := abs_lt.mp hdist
  have hb : (2 : ℝ) * δ + ε ≤ gap := by exact_mod_cast hsmall
  intro hy
  have hR := hy j
  have hS := hx j
  dsimp [rectangleCollar] at hR
  push_cast at hR
  rcases hj with hj | hj
  · have hg : (R.upper j : ℝ) + gap ≤ S.lower j := by exact_mod_cast hj
    linarith [hR.2, hS.1]
  · have hg : (S.upper j : ℝ) + gap ≤ R.lower j := by exact_mod_cast hj
    linarith [hS.2, hR.1]

end ForcedComputation.PlanarHamiltonian

end

end OAI

import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RationalHeatPlaneError
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarHeatTimeModulus
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarHeatTruncation

namespace OAI

/-! The actual computed three-dimensional heat quadrature approximates
the constructed planar resolvent. The bound includes both numerical
quadrature and the explicitly proved short/long-time tails. -/

noncomputable section
namespace ContinuumCoulomb.RationalHeatBox

def timeEndpoint (x : Input) : ℚ :=
  RationalQuadratureProgram.node x.2.2.1 x.2.2.2 x.1

def planeErrorBound (e : Settings) (η : ℝ) : ℝ :=
  4 * (2 * planarBoxSpatialConstant (PlanarForcingProgram.position e.2.1) η *
    (spatialStep e.2.2 : ℝ) +
    ((2 ^ e.1.2.1 : ℝ)⁻¹ + 8 / (e.1.2.2 : ℝ)) / (4 * η))

def resolventErrorBound (x : Input) : ℝ :=
  (x.1 : ℝ) * (4 * planarBoxTimeConstant (PlanarForcingProgram.position x.2.1.2.1)
    (x.2.2.1 : ℝ) * (x.2.2.2 : ℝ) ^ 2 +
    (x.2.2.2 : ℝ) * planeErrorBound x.2.1 (x.2.2.1 : ℝ)) +
    (x.2.2.1 : ℝ) + Real.exp (-(timeEndpoint x : ℝ))

theorem resolvent_error (x : Input)
    (hη : 0 < (x.2.2.1 : ℝ)) (hh : 0 ≤ (x.2.2.2 : ℝ))
    (hN : 0 < x.2.1.2.2) (hpi : 0 < x.2.1.1.2.2)
    (hM : (timeEndpoint x : ℝ) +
      (‖PlanarForcingProgram.position x.2.1.2.1‖ + 2) ^ 2 / (4 * (x.2.2.1 : ℝ)) ≤ x.2.1.1.1) :
    |(value x : ℝ) - planarResolventMode (PlanarForcingProgram.position x.2.1.2.1)| ≤
      resolventErrorBound x := by
  let r := PlanarForcingProgram.position x.2.1.2.1
  let η := (x.2.2.1 : ℝ)
  let h := (x.2.2.2 : ℝ)
  let T := (timeEndpoint x : ℝ)
  let f := fun t => Real.exp (-t) * planarHeatAverage t r
  have hT : T = UniformQuadrature.node η h x.1 :=
    RationalQuadratureProgram.node_cast _ _ _
  have hηT : η ≤ T := by rw [hT]; exact (UniformQuadrature.node_mem hh (Nat.le_refl x.1)).1
  have hL : 0 ≤ 4 * planarBoxTimeConstant r η := by
    dsimp [planarBoxTimeConstant, η]
    positivity
  have hLip : ∀ t ∈ Set.Icc η (UniformQuadrature.node η h x.1),
      ∀ s ∈ Set.Icc η (UniformQuadrature.node η h x.1),
      |f t - f s| ≤ (4 * planarBoxTimeConstant r η) * |t - s| := by
    intro t ht s hs
    exact planarHeatTime_lipschitz r hη ht.1 hs.1
  have hSample : ∀ i < x.1,
      |(plane x.2.1 (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 i) : ℝ) -
        f (UniformQuadrature.node η h i)| ≤ planeErrorBound x.2.1 η := by
    intro i hi
    have htmem := UniformQuadrature.node_mem (a := η) hh hi.le
    have htmem' : (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 i : ℝ) ∈ Set.Icc η T := by
      rw [RationalQuadratureProgram.node_cast, hT]
      exact htmem
    have hm : (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 i : ℝ) +
        (‖r‖ + 2) ^ 2 / (4 * η) ≤ x.2.1.1.1 := by
      linarith [htmem'.2, hM]
    have hp := plane_error_of_magnitude x.2.1
      (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 i) hη htmem'.1 hN hpi hm
    dsimp only [f, r, η, h, planeErrorBound]
    simpa only [RationalQuadratureProgram.node_cast] using hp
  have hQuad := UniformQuadrature.samples_error_lipschitz f
    (fun i => (plane x.2.1 (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 i) : ℝ))
    η h x.1 hh hL hLip hSample
  have hQuad' : |(value x : ℝ) - planarTruncatedHeat r η T| ≤
      (x.1 : ℝ) * (4 * planarBoxTimeConstant r η * h ^ 2 + h * planeErrorBound x.2.1 η) := by
    rw [value, RationalQuadratureProgram.value_cast]
    rw [← hT] at hQuad
    exact hQuad
  have hTail : |planarTruncatedHeat r η T - planarResolventMode r| ≤ η + Real.exp (-T) := by
    rw [abs_sub_comm]
    exact planarTruncatedHeat_error r hη.le hηT
  calc
    _ = |((value x : ℝ) - planarTruncatedHeat r η T) +
        (planarTruncatedHeat r η T - planarResolventMode r)| := by congr 1; ring
    _ ≤ |(value x : ℝ) - planarTruncatedHeat r η T| +
        |planarTruncatedHeat r η T - planarResolventMode r| := abs_add_le _ _
    _ ≤ (x.1 : ℝ) * (4 * planarBoxTimeConstant r η * h ^ 2 + h * planeErrorBound x.2.1 η) +
        (η + Real.exp (-T)) := add_le_add hQuad' hTail
    _ = _ := by dsimp [resolventErrorBound, r, η, h, T]; ring

end ContinuumCoulomb.RationalHeatBox

end

end OAI

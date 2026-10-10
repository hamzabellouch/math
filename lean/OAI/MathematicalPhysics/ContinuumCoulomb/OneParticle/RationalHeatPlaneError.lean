import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RationalHeatBox
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RectangleQuadrature
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.HeatSampleError

namespace OAI

/-! Error of the actual rational two-coordinate heat quadrature.
The sample evaluator is the concrete Taylor/π/forcing program. -/

namespace ContinuumCoulomb.RationalHeatBox

def spatialStep (N : ℕ) : ℚ := 2 / (N : ℚ)
def spatialNode (N i : ℕ) : ℚ := RationalQuadratureProgram.node (-1) (spatialStep N) i

theorem spatialEndpoint (N : ℕ) (hN : 0 < N) : spatialNode N N = 1 := by
  have hn : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold spatialNode RationalQuadratureProgram.node spatialStep
  field_simp
  ring

theorem spatialNode_mem (N i : ℕ) (hN : 0 < N) (hi : i ≤ N) :
    (spatialNode N i : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
  have hh : 0 ≤ (spatialStep N : ℝ) := by unfold spatialStep; positivity
  have h := UniformQuadrature.node_mem (a := (-1 : ℝ)) hh hi
  have hend : UniformQuadrature.node (-1 : ℝ) (spatialStep N : ℝ) N = 1 := by
    have hc := RationalQuadratureProgram.node_cast (-1) (spatialStep N) N
    norm_num only [Rat.cast_neg, Rat.cast_one] at hc
    rw [← hc]
    exact_mod_cast spatialEndpoint N hN
  simpa only [spatialNode, RationalQuadratureProgram.node_cast, Rat.cast_neg, Rat.cast_one,
    hend] using h

theorem plane_cast (e : Settings) (t : ℚ) :
    (plane e t : ℝ) =
      UniformQuadrature.rectangleSum (spatialStep e.2.2 : ℝ) (spatialStep e.2.2 : ℝ) e.2.2 e.2.2
        (fun i j => (RationalHeatSample.value
          (e.1, t, e.2.1, spatialNode e.2.2 i, spatialNode e.2.2 j) : ℝ)) := by
  simp [plane, planeInput, line, lineInput, sample, RationalQuadratureProgram.value,
    RationalQuadratureProgram.sample, spatialNode, spatialStep,
    UniformQuadrature.rectangleSum, UniformQuadrature.sampleSum]

theorem plane_error (e : Settings) (t : ℚ) {η : ℝ}
    (hη : 0 < η) (ht : η ≤ (t : ℝ)) (hN : 0 < e.2.2) (hpi : 0 < e.1.2.2)
    (hM : ∀ i < e.2.2, ∀ j < e.2.2,
      |(RationalHeatSample.exponent (t, e.2.1, spatialNode e.2.2 i, spatialNode e.2.2 j) : ℝ)|
        ≤ e.1.1) :
    |(plane e t : ℝ) - Real.exp (-(t : ℝ)) * planarHeatAverage t
      (PlanarForcingProgram.position e.2.1)| ≤
      4 * (2 * planarBoxSpatialConstant (PlanarForcingProgram.position e.2.1) η *
        (spatialStep e.2.2 : ℝ) +
        ((2 ^ e.1.2.1 : ℝ)⁻¹ + 8 / (e.1.2.2 : ℝ)) / (4 * η)) := by
  let r := PlanarForcingProgram.position e.2.1
  let L := planarBoxSpatialConstant r η
  let δ := ((2 ^ e.1.2.1 : ℝ)⁻¹ + 8 / (e.1.2.2 : ℝ)) / (4 * η)
  let f := fun x y => HeatKernelModulus.density r t (planarPairEquiv.symm (x, y))
  let v := fun i j => (RationalHeatSample.value
    (e.1, t, e.2.1, spatialNode e.2.2 i, spatialNode e.2.2 j) : ℝ)
  have hh : 0 ≤ (spatialStep e.2.2 : ℝ) := by unfold spatialStep; positivity
  have hL : 0 ≤ L := by dsimp [L, planarBoxSpatialConstant]; positivity
  have hend : UniformQuadrature.node (-1 : ℝ) (spatialStep e.2.2 : ℝ) e.2.2 = 1 := by
    have hc := RationalQuadratureProgram.node_cast (-1) (spatialStep e.2.2) e.2.2
    norm_num only [Rat.cast_neg, Rat.cast_one] at hc
    rw [← hc]
    exact_mod_cast spatialEndpoint e.2.2 hN
  have hLipX : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ x' ∈ Set.Icc (-1 : ℝ) 1,
      ∀ y ∈ Set.Icc (-1 : ℝ) 1, |f x y - f x' y| ≤ L * |x - x'| := by
    intro x hx x' hx' y hy
    exact planarBox_spatial_first r hη ht hx hx' hy
  have hLipY : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      ∀ y' ∈ Set.Icc (-1 : ℝ) 1, |f x y - f x y'| ≤ L * |y - y'| := by
    intro x hx y hy y' hy'
    exact planarBox_spatial_second r hη ht hx hy hy'
  have hsample : ∀ i < e.2.2, ∀ j < e.2.2,
      |v i j - f (UniformQuadrature.node (-1) (spatialStep e.2.2 : ℝ) i)
        (UniformQuadrature.node (-1) (spatialStep e.2.2 : ℝ) j)| ≤ δ := by
    intro i hi j hj
    have h := RationalHeatSample.error_density_uniform
      (e.1, t, e.2.1, spatialNode e.2.2 i, spatialNode e.2.2 j) hη ht hpi (hM i hi j hj)
    dsimp only [v, f, r, δ]
    simpa only [rationalPosition_eq_pair, spatialNode, RationalQuadratureProgram.node_cast,
      Rat.cast_neg, Rat.cast_one] using h
  have h := UniformQuadrature.rectangle_error f v (-1) (spatialStep e.2.2 : ℝ) e.2.2
    (-1) (spatialStep e.2.2 : ℝ) e.2.2 hh hh hL hL
    (by simpa only [hend] using hLipX) (by simpa only [hend] using hLipY) hsample
  have hlen : (e.2.2 : ℝ) * (spatialStep e.2.2 : ℝ) = 2 := by
    have hn : (e.2.2 : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    simp only [spatialStep, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast]
    field_simp
  rw [hend, hlen] at h
  rw [plane_cast, planarHeatResolvent_box]
  change |UniformQuadrature.rectangleSum _ _ _ _ v - ∫ x in (-1 : ℝ)..1,
    ∫ y in (-1 : ℝ)..1, f x y| ≤ _
  convert h using 1
  ring

theorem plane_error_of_magnitude (e : Settings) (t : ℚ) {η : ℝ}
    (hη : 0 < η) (ht : η ≤ (t : ℝ)) (hN : 0 < e.2.2) (hpi : 0 < e.1.2.2)
    (hM : (t : ℝ) + (‖PlanarForcingProgram.position e.2.1‖ + 2) ^ 2 / (4 * η) ≤ e.1.1) :
    |(plane e t : ℝ) - Real.exp (-(t : ℝ)) * planarHeatAverage t
      (PlanarForcingProgram.position e.2.1)| ≤
      4 * (2 * planarBoxSpatialConstant (PlanarForcingProgram.position e.2.1) η *
        (spatialStep e.2.2 : ℝ) +
        ((2 ^ e.1.2.1 : ℝ)⁻¹ + 8 / (e.1.2.2 : ℝ)) / (4 * η)) := by
  apply plane_error e t hη ht hN hpi
  intro i hi j hj
  exact (RationalHeatSample.exponent_abs_le _ hη ht le_rfl
    (spatialNode_mem _ _ hN hi.le) (spatialNode_mem _ _ hN hj.le)).trans hM

end ContinuumCoulomb.RationalHeatBox

end OAI

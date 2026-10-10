import OAI.Geometry.SurfaceImmersion.Geometry.PreferredJetGeometry

namespace OAI

/-! An open domain of genuine second jets carrying the normal-frame geometry.
The preferred normal is projected from the original spatial normal field. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame PhaseGeometry

def preferredJetDomain (U : Set Base) (n : Base → Vec) : Set GeometricJet :=
  {j | j.1 ∈ U ∧ jetTangentGram j ≠ 0 ∧
    (jetAccelerationCoefficients j).1 < 0 ∧ jetProjectedPreferred n j ≠ 0}

lemma preferredJetDomain_open {U : Set Base} (hU : IsOpen U) {n : Base → Vec}
    (hn : ContDiffOn ℝ ∞ n U) : IsOpen (preferredJetDomain U n) := by
  rw [isOpen_iff_mem_nhds]
  intro j hj
  have hp := hn.contDiffAt (hU.mem_nhds hj.1)
  have hu := (hU.preimage continuous_fst).mem_nhds hj.1
  have hD := jetTangentGram_smooth.continuous.continuousAt.eventually_ne hj.2.1
  have hmu := (jetAccelerationCoefficients_smoothAt hj.2.1).fst.continuousAt.eventually
    (gt_mem_nhds hj.2.2.1)
  have hproj := (jetProjectedPreferred_smoothAt hp hj.2.1).continuousAt.eventually_ne hj.2.2.2
  filter_upwards [hu,hD,hmu,hproj] with k hk hd hm hp
  exact ⟨hk,hd,hm,hp⟩

lemma preferredJetDomain_geometry {U : Set Base} {n : Base → Vec}
    {j : GeometricJet} (hj : j ∈ preferredJetDomain U n) :
    gramDet (j.2 0) (j.2 1) ≠ 0 ∧ (jetAccelerationCoefficients j).1 < 0 ∧
      j.2 0 ⬝ᵥ jetSecondNormal j = 0 ∧ j.2 1 ⬝ᵥ jetSecondNormal j = 0 ∧
      j.2 4 = (jetAccelerationCoefficients j).1 • j.2 0 +
        (jetAccelerationCoefficients j).2 • j.2 1 + jetSecondNormal j ∧
      j.2 0 ⬝ᵥ jetPreferred n j = 0 ∧ j.2 1 ⬝ᵥ jetPreferred n j = 0 ∧
      jetPreferred n j ⬝ᵥ jetPreferred n j = 1 := by
  have hB := realNormalPart_perp (j.2 0) (j.2 1) (j.2 4) hj.2.1
  have hN := realNormalPart_perp (j.2 0) (j.2 1) (n j.1) hj.2.1
  exact ⟨hj.2.1,hj.2.2.1,hB.1,hB.2,jetAcceleration_decomposition j,
    dot_normalize_zero hN.1,dot_normalize_zero hN.2,normalize_unit hj.2.2.2⟩

lemma actual_jet_mem_preferred_domain {F n : Base → Vec}
    (hF : ContDiff ℝ ∞ F) {U : Set Base} {p : Base} (hp : p ∈ U)
    (hI : Function.Injective (fderiv ℝ F p))
    (hN : coordDeriv dx F p ⬝ᵥ n p = 0 ∧ coordDeriv dy F p ⬝ᵥ n p = 0 ∧
      n p ⬝ᵥ n p = 1)
    (hHess : 0 < coordinateMetricHessian (inducedCoordinateMetric F) Prod.fst p dy dy) :
    CollarVelocity.jetSection F p ∈ preferredJetDomain U n := by
  have hmu : (jetAccelerationCoefficients (CollarVelocity.jetSection F p)).1 < 0 := by
    rw [jetAccelerationCoefficients_on_section hF]
    rw [coordinateMetricHessian_fst_dy] at hHess
    exact neg_pos.mp hHess
  have hpN : jetProjectedPreferred n (CollarVelocity.jetSection F p) = n p := by
    exact realNormalPart_eq_self hN.1 hN.2.1
  refine ⟨hp,gramDet_ne_zero_of_injective _ hI,hmu,?_⟩
  rw [hpN]
  intro hz
  have hh := hN.2.2
  rw [hz] at hh
  norm_num at hh

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI

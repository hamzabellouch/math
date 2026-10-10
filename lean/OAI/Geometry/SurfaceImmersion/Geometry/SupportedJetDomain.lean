import OAI.Geometry.SurfaceImmersion.Geometry.PreferredJetFrame

namespace OAI

/-! The velocity radius stays nonzero on an open neighborhood of the
actual compact jet set, including the zero-amplitude boundary. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame PhaseGeometry

def supportedJetDomain (U : Set Base) (n : Base → Vec) (a : Base → ℝ) : Set GeometricJet :=
  {j | j ∈ preferredJetDomain U n ∧ (jetNormal j ≠ 0 ∨ a j.1 ≠ 0)}

lemma supportedJetDomain_open {U : Set Base} (hU : IsOpen U) {n : Base → Vec}
    (hn : ContDiffOn ℝ ∞ n U) {a : Base → ℝ} (ha : ContDiff ℝ ∞ a) :
    IsOpen (supportedJetDomain U n a) := by
  have hΩ := preferredJetDomain_open hU hn
  rw [isOpen_iff_mem_nhds]
  intro j hj
  have hjΩ := hj.1
  have hv : ContDiffAt ℝ ∞ jetNormal j :=
    contDiffAt_realNormalPart (jetSlot_smooth 1).contDiffAt (jetSlot_smooth 4).contDiffAt
      (jetSlot_smooth 0).contDiffAt (preferredJetDomain_velocity_gram hjΩ)
  have hamp : ContinuousAt (fun j : GeometricJet => a j.1) j :=
    (ha.continuous.comp continuous_fst).continuousAt
  rcases hj.2 with hv0 | ha0
  · filter_upwards [hΩ.mem_nhds hjΩ,hv.continuousAt.eventually_ne hv0] with k hk hvk
    exact ⟨hk,Or.inl hvk⟩
  · filter_upwards [hΩ.mem_nhds hjΩ,hamp.eventually_ne ha0] with k hk hak
    exact ⟨hk,Or.inr hak⟩

lemma actual_jet_mem_supported_domain {F n : Base → Vec}
    (hF : ContDiff ℝ ∞ F) {a : Base → ℝ} {U : Set Base} {p : Base} (hp : p ∈ U)
    (hI : Function.Injective (fderiv ℝ F p))
    (hN : coordDeriv dx F p ⬝ᵥ n p = 0 ∧ coordDeriv dy F p ⬝ᵥ n p = 0 ∧
      n p ⬝ᵥ n p = 1)
    (hHess : 0 < coordinateMetricHessian (inducedCoordinateMetric F) Prod.fst p dy dy)
    (hboundary : a p = 0 → realSecondForm F dy dy p ≠ 0) :
    CollarVelocity.jetSection F p ∈ supportedJetDomain U n a := by
  have hj := actual_jet_mem_preferred_domain hF hp hI hN hHess
  refine ⟨hj,?_⟩
  by_cases ha : a p = 0
  · left
    have hg := preferredJetDomain_velocity_gram hj
    have hgeom := preferredJetDomain_geometry hj
    have hb := hboundary ha
    have hproj := projected_normal_ne_zero hgeom.1 hgeom.2.1.ne hgeom.2.2.1 hgeom.2.2.2.1
      hgeom.2.2.2.2.1 hgeom.2.2.1 hgeom.2.2.2.1 hb
    have he := projected_second_form hg hgeom.2.2.2.2.1
    intro hv
    apply hproj
    rw [he]
    change -((jetAccelerationCoefficients (CollarVelocity.jetSection F p)).1) •
      jetNormal (CollarVelocity.jetSection F p) = 0
    rw [hv,smul_zero]
  · exact Or.inr ha

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI

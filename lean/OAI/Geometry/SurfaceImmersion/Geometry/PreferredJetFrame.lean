import OAI.Geometry.SurfaceImmersion.Geometry.PreferredJetDomain

namespace OAI

/-! A smooth velocity frame on an open neighborhood of the actual second
jets, equal to the projected tangent frame near the selected boundary. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame PhaseGeometry

lemma preferredJetDomain_velocity_gram {U : Set Base} {n : Base → Vec}
    {j : GeometricJet} (hj : j ∈ preferredJetDomain U n) :
    gramDet (j.2 1) (j.2 4) ≠ 0 := by
  obtain ⟨hD,hmu,hXB,hYB,hC,_,_,_⟩ := preferredJetDomain_geometry hj
  exact (velocity_gram_pos hD hmu.ne hXB hYB hC).ne'

theorem exists_preferred_jet_frame {F n : Base → Vec}
    (hF : ContDiff ℝ ∞ F) {U C₀ : Set Base} (hU : IsOpen U)
    (hn : ContDiffOn ℝ ∞ n U) (hC₀ : IsCompact C₀) (hCU : C₀ ⊆ U)
    (hI : ∀ p ∈ U, Function.Injective (fderiv ℝ F p))
    (hN : ∀ p ∈ U, coordDeriv dx F p ⬝ᵥ n p = 0 ∧ coordDeriv dy F p ⬝ᵥ n p = 0 ∧
      n p ⬝ᵥ n p = 1)
    (hHess : ∀ p ∈ U, 0 < coordinateMetricHessian (inducedCoordinateMetric F) Prod.fst p dy dy)
    (hboundary : ∀ p ∈ C₀, realSecondForm F dy dy p ≠ 0 ∧
      normalize (realSecondForm F dy dy p) ≠ -n p) :
    ∃ W : Set GeometricJet, IsOpen W ∧ CollarVelocity.jetSection F '' C₀ ⊆ W ∧
      W ⊆ preferredJetDomain U n ∧
      ∃ e₁ e₂ : GeometricJet → Vec,
        ContDiffOn ℝ ∞ e₁ (preferredJetDomain U n) ∧
        ContDiffOn ℝ ∞ e₂ (preferredJetDomain U n) ∧
        (∀ j ∈ preferredJetDomain U n,
          e₁ j ⬝ᵥ e₁ j = 1 ∧ e₂ j ⬝ᵥ e₂ j = 1 ∧ e₁ j ⬝ᵥ e₂ j = 0 ∧
          j.2 1 ⬝ᵥ e₁ j = 0 ∧ j.2 4 ⬝ᵥ e₁ j = 0 ∧
          j.2 1 ⬝ᵥ e₂ j = 0 ∧ j.2 4 ⬝ᵥ e₂ j = 0) ∧
        (∀ j ∈ W, jetNormal j ≠ 0 ∧ e₁ j = normalize (jetNormal j)) := by
  let Ω := preferredJetDomain U n
  have hΩ : IsOpen Ω := preferredJetDomain_open hU hn
  have hmem (p : Base) (hp : p ∈ U) : CollarVelocity.jetSection F p ∈ Ω :=
    actual_jet_mem_preferred_domain hF hp (hI p hp) (hN p hp) (hHess p hp)
  have hK : IsCompact (CollarVelocity.jetSection F '' C₀) :=
    hC₀.image (CollarVelocity.jetSection_smooth hF).continuous
  have hKΩ : CollarVelocity.jetSection F '' C₀ ⊆ Ω := by
    rintro _ ⟨p,hp,rfl⟩
    exact hmem p (hCU hp)
  have hBn : ContDiffOn ℝ ∞ jetSecondNormal Ω :=
    fun j hj => (jetSecondNormal_smoothAt hj.2.1).contDiffWithinAt
  have hNn : ContDiffOn ℝ ∞ (jetPreferred n) Ω := by
    intro j hj
    exact (jetPreferred_smoothAt (hn.contDiffAt (hU.mem_nhds hj.1)) hj.2.1 hj.2.2.2).contDiffWithinAt
  have hb : ∀ j ∈ CollarVelocity.jetSection F '' C₀,
      jetSecondNormal j ≠ 0 ∧ normalize (jetSecondNormal j) ≠ -jetPreferred n j := by
    rintro _ ⟨p,hp,rfl⟩
    have he : jetSecondNormal (CollarVelocity.jetSection F p) = realSecondForm F dy dy p := rfl
    rw [he,jetPreferred_on_section (hN p (hCU hp)).1 (hN p (hCU hp)).2.1 (hN p (hCU hp)).2.2]
    exact hboundary p hp
  obtain ⟨W,hW,hKW,hWΩ,e₁,e₂,he₁,he₂,hframe,hfirst⟩ := exists_projected_collar_frame
    hK hΩ hKΩ (jetSlot_smooth 0).contDiffOn (jetSlot_smooth 1).contDiffOn
    (jetSlot_smooth 4).contDiffOn hBn hNn
    (fun j hj => preferredJetDomain_geometry hj) hb
  refine ⟨W,hW,hKW,hWΩ,e₁,e₂,he₁,he₂,hframe,?_⟩
  intro j hj
  have he : e₁ j = normalize (jetNormal j) := hfirst j hj
  refine ⟨?_,he⟩
  intro hz
  have hu := (hframe j (hWΩ hj)).1
  rw [he,hz] at hu
  norm_num [VelocityFrame.normalize] at hu

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI

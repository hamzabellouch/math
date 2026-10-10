import OAI.Analysis.CircleDomains.Modulus.WeightedCollarNeighborhoods

namespace OAI

/-! Only the density near the requested collar is used. Extending it by
zero removes any unnecessary global planar square-integrability requirement. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_weighted_collar_of_local_energy
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ Gᶜ, π x ∈ B) {p : Sphere} (hpB : p ∈ B) (hp : p ≠ π OnePoint.infty)
    {O : Set Sphere} (hO : IsOpen O) (hpO : p ∈ O)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g)
    (hg2 : (∫⁻z in (fun z : ℂ => π (z : Sphere)) ⁻¹' O, g z ^ 2) < ∞) :
    ∃ D : WeightedCollar G π B p g,
      closure D.region ⊆ O ∧ {z | D.function z = D.level} ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' O := by
  let P : Set ℂ := (fun z : ℂ => π (z : Sphere)) ⁻¹' O
  have hP : MeasurableSet P := (hO.preimage (hπ.comp OnePoint.continuous_coe)).measurableSet
  let q := P.indicator g
  have hq : Measurable q := hg.indicator hP
  have hq2 : (∫⁻z, q z ^ 2) < ∞ := by
    have he : (fun z => q z ^ 2) = P.indicator (fun z => g z ^ 2) := by
      funext z
      by_cases hz : z ∈ P <;> simp [q, hz]
    rw [he, lintegral_indicator hP]
    exact hg2
  obtain ⟨D, hD, hlevel⟩ := exists_weighted_collar_in_neighborhood hcoarea hsard hsch
    G π hπ hclosed hsurj hr hB hTD hbad hpB hp hO hpO q hq hq2
  have hcost : (∫⁻z in {z | D.function z = D.level}, g z ∂(μH[1] : Measure ℂ)) < ∞ := by
    have hm : MeasurableSet {z | D.function z = D.level} :=
      isClosed_eq D.smooth.continuous continuous_const |>.measurableSet
    have he : (∫⁻z in {z | D.function z = D.level}, g z ∂(μH[1] : Measure ℂ)) =
        ∫⁻z in {z | D.function z = D.level}, q z ∂(μH[1] : Measure ℂ) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hm] with z hz
      exact (indicator_of_mem (hlevel hz) g).symm
    rw [he]
    exact D.cost_finite
  let E : WeightedCollar G π B p g :=
    ⟨D.disk, D.curve, D.function, D.level, D.fiber_inside, D.curve_smooth,
      D.curve_embedding, D.frontier_eq, D.frontier_level, D.smooth, D.regular, D.level_good, hcost⟩
  exact ⟨E, hD, hlevel⟩

end CircleDomainRigidity

end

end OAI

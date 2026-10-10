import OAI.Analysis.CircleDomains.Modulus.InterposedWeightedCollars

namespace OAI

/-! Interpose weighted collars between successive pairs of prescribed
collars. All joining levels miss every prescribed boundary. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem exists_interposed_weighted_collars_of_local_energy
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B : Set Sphere} (hB : IsClosed B) (hbad : ∀x ∈ Gᶜ, π x ∈ B)
    {p : Sphere} {g₀ : ℂ → ℝ≥0∞} (D : ℕ → WeightedCollar G π B p g₀)
    (hnest : ∀n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, closure (D n).region ⊆ V)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) (hg2 : (∫⁻z in (fun z : ℂ => π (z : Sphere)) ⁻¹' (D 0).region, g z ^ 2) < ∞) :
    ∃ E : ℕ → WeightedCollar G π B p g,
      closure (E 0).region ⊆ (D 0).region ∧
      (∀n, closure (E (n+1)).region ⊆ (E n).region) ∧
      (∀n, {z | (E (n+1)).function z = (E (n+1)).level} ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' (E n).region) ∧
      (∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, closure (E n).region ⊆ V) ∧
      (∀n z, (E n).function z = (E n).level → ∀j, π (z : Sphere) ∉ frontier (D j).region) ∧
      (∀n, {z | (E n).function z = (E n).level} ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' (D 0).region) := by
  let P := (fun z : ℂ => π (z : Sphere)) ⁻¹' (D 0).region
  have hP : MeasurableSet P :=
    (((D 0).isOpen_region hπ hclosed hsurj hr).preimage
      (hπ.comp OnePoint.continuous_coe)).measurableSet
  let q := P.indicator g
  have hq : Measurable q := hg.indicator hP
  have hq2 : (∫⁻z, q z ^ 2) < ∞ := by
    have heq : (fun z => q z ^ 2) = P.indicator (fun z => g z ^ 2) := by
      funext z
      by_cases hz : z ∈ P <;> simp [q, hz]
    rw [heq, lintegral_indicator hP]
    exact hg2
  obtain ⟨E, hE0, hEn, hEl, hEs, hEa, hEp⟩ := exists_interposed_weighted_collars
    hcoarea hsard hsch G π hπ hclosed hsurj hr hB hbad D hnest hshrink q hq hq2
  have hcost (n : ℕ) : (∫⁻z in {z | (E n).function z = (E n).level}, g z ∂(μH[1] : Measure ℂ)) < ∞ := by
    have hm : MeasurableSet {z | (E n).function z = (E n).level} :=
      (isClosed_eq (E n).smooth.continuous continuous_const).measurableSet
    have heq : (∫⁻z in {z | (E n).function z = (E n).level}, g z ∂(μH[1] : Measure ℂ)) =
        ∫⁻z in {z | (E n).function z = (E n).level}, q z ∂(μH[1] : Measure ℂ) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hm] with z hz
      exact (indicator_of_mem (hEp n hz) g).symm
    rw [heq]
    exact (E n).cost_finite
  let H : ℕ → WeightedCollar G π B p g := fun n =>
    ⟨(E n).disk, (E n).curve, (E n).function, (E n).level, (E n).fiber_inside,
      (E n).curve_smooth, (E n).curve_embedding, (E n).frontier_eq, (E n).frontier_level,
      (E n).smooth, (E n).regular, (E n).level_good, hcost n⟩
  exact ⟨H, hE0, hEn, hEl, hEs, hEa, hEp⟩

end CircleDomainRigidity

end

end OAI

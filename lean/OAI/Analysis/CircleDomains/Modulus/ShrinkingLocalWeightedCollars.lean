import OAI.Analysis.CircleDomains.Modulus.ShrinkingWeightedCollars

namespace OAI

/-! Shrinking weighted collars require square integrability only in the
chosen outer neighborhood. This allows densities positive near infinity. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric

theorem exists_shrinking_local_weighted_collars
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ Gᶜ, π x ∈ B) {p : Sphere} (hpB : p ∈ B) (hp : p ≠ π OnePoint.infty)
    {W : Set Sphere} (hW : IsOpen W) (hpW : p ∈ W)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g)
    (hg2 : (∫⁻z in (fun z : ℂ => π (z : Sphere)) ⁻¹' W, g z ^ 2) < ∞) :
    ∃ D : ℕ → WeightedCollar G π B p g,
      closure (D 0).region ⊆ W ∧
      (∀n, closure (D (n+1)).region ⊆ (D n).region) ∧
      (∀n, {z | (D (n+1)).function z = (D (n+1)).level} ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' (D n).region) ∧
      (∀V ∈ 𝓝 p, ∃N : ℕ, ∀n ≥ N, closure (D n).region ⊆ V) := by
  let P : Set ℂ := (fun z : ℂ => π (z : Sphere)) ⁻¹' W
  have hP : MeasurableSet P := (hW.preimage (hπ.comp OnePoint.continuous_coe)).measurableSet
  let q := P.indicator g
  have hq : Measurable q := hg.indicator hP
  have hq2 : (∫⁻z, q z ^ 2) < ∞ := by
    have heq : (fun z => q z ^ 2) = P.indicator (fun z => g z ^ 2) := by
      funext z
      by_cases hz : z ∈ P <;> simp [q, hz]
    rw [heq, lintegral_indicator hP]
    exact hg2
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hrpos (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  let O : ℕ → Set Sphere := fun n => W ∩ ball p (r n)
  obtain ⟨D, hD, hnest, hlevel, hlevelNest⟩ := exists_nested_weighted_collars
    hcoarea hsard hsch G π hπ hclosed hsurj hr hB hTD hbad hpB hp O
    (fun _ => hW.inter isOpen_ball) (fun n => ⟨hpW, mem_ball_self (hrpos n)⟩) q hq hq2
  have hcost (n : ℕ) : (∫⁻z in {z | (D n).function z = (D n).level}, g z ∂(μH[1] : Measure ℂ)) < ∞ := by
    have hm : MeasurableSet {z | (D n).function z = (D n).level} :=
      (isClosed_eq (D n).smooth.continuous continuous_const).measurableSet
    have heq : (∫⁻z in {z | (D n).function z = (D n).level}, g z ∂(μH[1] : Measure ℂ)) =
        ∫⁻z in {z | (D n).function z = (D n).level}, q z ∂(μH[1] : Measure ℂ) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hm] with z hz
      exact (indicator_of_mem (show z ∈ P from (hlevel n hz).1) g).symm
    rw [heq]
    exact (D n).cost_finite
  let E : ℕ → WeightedCollar G π B p g := fun n =>
    ⟨(D n).disk, (D n).curve, (D n).function, (D n).level, (D n).fiber_inside,
      (D n).curve_smooth, (D n).curve_embedding, (D n).frontier_eq, (D n).frontier_level,
      (D n).smooth, (D n).regular, (D n).level_good, hcost n⟩
  refine ⟨E, (hD 0).trans inter_subset_left, hnest, hlevelNest, ?_⟩
  intro V hV
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hV
  have hrzero : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hrzero.eventually (gt_mem_nhds hδ))
  refine ⟨N, fun n hn => (hD n).trans ?_⟩
  exact inter_subset_right.trans ((ball_subset_ball (hN n hn).le).trans hball)

end CircleDomainRigidity

end

end OAI

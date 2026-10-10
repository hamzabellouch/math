import OAI.Analysis.CircleDomains.Modulus.NestedWeightedCollars
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! The chosen collar closures and all their joining levels shrink to the
actual quotient point. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric

theorem exists_shrinking_weighted_collars
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ Gᶜ, π x ∈ B) {p : Sphere} (hpB : p ∈ B) (hp : p ≠ π OnePoint.infty)
    {W : Set Sphere} (hW : IsOpen W) (hpW : p ∈ W)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) (hg2 : (∫⁻z, g z ^ 2) < ∞) :
    ∃ D : ℕ → WeightedCollar G π B p g,
      closure (D 0).region ⊆ W ∧
      (∀n, closure (D (n+1)).region ⊆ (D n).region) ∧
      (∀n, {z | (D (n+1)).function z = (D (n+1)).level} ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' (D n).region) ∧
      (∀V ∈ 𝓝 p, ∃N : ℕ, ∀n ≥ N, closure (D n).region ⊆ V ∧
        {z | (D n).function z = (D n).level} ⊆
          (fun z : ℂ => π (z : Sphere)) ⁻¹' V) := by
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ)+1)
  have hrpos (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hrzero : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let O : ℕ → Set Sphere := fun n => W ∩ ball p (r n)
  obtain ⟨D, hD, hnested, hlevel, hlevelNested⟩ := exists_nested_weighted_collars
    hcoarea hsard hsch G π hπ hclosed hsurj hr hB hTD hbad hpB hp O
    (fun _ => hW.inter isOpen_ball) (fun n => ⟨hpW, mem_ball_self (hrpos n)⟩) g hg hg2
  refine ⟨D, (hD 0).trans inter_subset_left, hnested, hlevelNested, ?_⟩
  intro V hV
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hrzero.eventually (gt_mem_nhds hδ))
  refine ⟨N, ?_⟩
  intro n hn
  have hsub : O n ⊆ V := inter_subset_right.trans ((ball_subset_ball (hN n hn).le).trans hball)
  exact ⟨(hD n).trans hsub, (hlevel n).trans (preimage_mono hsub)⟩

end CircleDomainRigidity

end

end OAI

import OAI.Analysis.CircleDomains.Modulus.WeightedOneEndedLevelTolls
import OAI.Analysis.CircleDomains.Modulus.WeightedTwoEndedLevelTolls
import OAI.Analysis.CircleDomains.Selection.ExclusionTolls

namespace OAI

/-! Collar splicing preserves avoidance of any set missed by both the
original paths and the chosen collar levels, including forbidden gate hits. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)]

private theorem collar_level_exclusion_zero
    (d : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (S : Set Sphere) {B : Set Sphere} {p : Sphere} {g : ℂ → ℝ≥0∞}
    (D : WeightedCollar d.physicalDomain π B p g)
    (havoid : ∀z, D.function z = D.level → π (z : Sphere) ∉ S) :
    ∀z, D.function z = D.level → exclusionToll S m (π (z : Sphere)) = 0 := by
  intro z hz
  rw [exclusionToll_eq S m (havoid z hz)]
  apply hm
  rw [← he ⟨(z : Sphere), (D.level_good z hz).1⟩]
  exact (d.domainEquiv _).property

theorem exists_weighted_oneEnded_splicing_avoiding_set
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (F : Set Sphere) (hF : F ⊆ d.quotientDomain) (hstart : ∀n, (Γ n).1.val ⊥ ∈ F)
    (p : Sphere) (hp : p ≠ π OnePoint.infty)
    (hend : Tendsto (fun n => (Γ n).1.val ⊤) atTop (𝓝 p))
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (S : Set Sphere) (havoid : ∀n t, (Γ n).1.val t ∉ S)
    {B : Set Sphere}
    (D : ℕ → WeightedCollar d.physicalDomain π B p (fun z => g (z : Sphere)))
    (hlevelAvoid : ∀j z, (D j).function z = (D j).level → π (z : Sphere) ∉ S)
    (hnest : ∀j, closure (D (j+1)).region ⊆ (D j).region)
    (hshrink : ∀O ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, closure (D j).region ⊆ O)
    (hlevel : ∀j, {z | (D (j+1)).function z = (D (j+1)).level} ⊆
      (fun z : ℂ => π (z : Sphere)) ⁻¹' (D j).region)
    (hDF : Disjoint F (closure (D 0).region))
    (A : ℝ≥0∞) (hA : A < ∞)
    (hcost : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A))
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∧ ρ.val ⊤ = p ∧
      (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
        preterminalToll ρ.val m ≤ A + ENNReal.ofReal η ∧
      ∀t < (⊤ : PathTime), ρ.val t ∉ S := by
  have hcostS : Tendsto (fun n => physicalTollCost d g (exclusionToll S m) (Γ n).1)
      atTop (𝓝 A) := by
    convert hcost using 1
    funext n
    exact physicalTollCost_exclusion d g m S (Γ n).1 (havoid n)
  have hzeroS (n : ℕ) : exclusionToll S m ((Γ n).1.val ⊥) = 0 := by
    rw [exclusionToll_eq S m (havoid n ⊥)]
    exact hm _ (hF (hstart n))
  obtain ⟨ρ, θ, hρ, hρ0, hρ1, hC⟩ := exists_weighted_oneEnded_splicing_of_level_toll_zero
    d hU hG hdisj π hπ hclosed hsurj hr he ν N Γ hΓ F hstart p hp hend
    g hg (exclusionToll S m) hzeroS D
    (fun j => collar_level_exclusion_zero d π he m hm S (D j) (hlevelAvoid j))
    hnest hshrink hlevel hDF A hA hcostS w hw hpos hpoint hη
  have hfinite : preterminalToll ρ.val (exclusionToll S m) < ∞ :=
    (show preterminalToll ρ.val (exclusionToll S m) ≤
      (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
      preterminalToll ρ.val (exclusionToll S m) from le_add_self).trans_lt
      (hC.trans_lt (ENNReal.add_lt_top.mpr ⟨hA, ENNReal.ofReal_lt_top⟩))
  refine ⟨ρ, θ, hρ, hρ0, hρ1,
    (add_le_add le_rfl (preterminalToll_mono ρ.val (le_exclusionToll S m))).trans hC, ?_⟩
  rw [preterminalToll_eq_timeToll] at hfinite
  exact avoids_of_finite_exclusionToll ρ.val _ S m hfinite

theorem exists_weighted_twoEnded_splicing_avoiding_set
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (p q : Sphere) (hp : p ≠ π OnePoint.infty) (hq : q ≠ π OnePoint.infty)
    (hstart : Tendsto (fun n => (Γ n).1.val ⊥) atTop (𝓝 p))
    (hend : Tendsto (fun n => (Γ n).1.val ⊤) atTop (𝓝 q))
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (S : Set Sphere) (havoid : ∀n t, (Γ n).1.val t ∉ S)
    {B : Set Sphere}
    (D : ℕ → WeightedCollar d.physicalDomain π B p (fun z => g (z : Sphere)))
    (E : ℕ → WeightedCollar d.physicalDomain π B q (fun z => g (z : Sphere)))
    (havoidD : ∀j z, (D j).function z = (D j).level → π (z : Sphere) ∉ S)
    (havoidE : ∀j z, (E j).function z = (E j).level → π (z : Sphere) ∉ S)
    (hnestD : ∀j, closure (D (j+1)).region ⊆ (D j).region)
    (hnestE : ∀j, closure (E (j+1)).region ⊆ (E j).region)
    (hshrinkD : ∀O ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, closure (D j).region ⊆ O)
    (hshrinkE : ∀O ∈ 𝓝 q, ∃k : ℕ, ∀j ≥ k, closure (E j).region ⊆ O)
    (hlevelD : ∀j, {z | (D (j+1)).function z = (D (j+1)).level} ⊆
      (fun z : ℂ => π (z : Sphere)) ⁻¹' (D j).region)
    (hlevelE : ∀j, {z | (E (j+1)).function z = (E (j+1)).level} ⊆
      (fun z : ℂ => π (z : Sphere)) ⁻¹' (E j).region)
    (hDE : Disjoint (closure (D 0).region) (closure (E 0).region))
    (A : ℝ≥0∞) (hA : A < ∞)
    (hcost : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A))
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ = p ∧ ρ.val ⊤ = q ∧
      interiorPhysicalTollCost d g m ρ ≤ A + ENNReal.ofReal η ∧
      ∀t ∈ Ioo (⊥ : PathTime) ⊤, ρ.val t ∉ S := by
  have hcostS : Tendsto (fun n => physicalTollCost d g (exclusionToll S m) (Γ n).1)
      atTop (𝓝 A) := by
    convert hcost using 1
    funext n
    exact physicalTollCost_exclusion d g m S (Γ n).1 (havoid n)
  obtain ⟨ρ, θ, hρ, hρ0, hρ1, hC⟩ := exists_weighted_twoEnded_splicing_of_level_toll_zero
    d hU hG hdisj π hπ hclosed hsurj hr he ν N Γ hΓ p q hp hq hstart hend
    g hg (exclusionToll S m) D E
    (fun j => collar_level_exclusion_zero d π he m hm S (D j) (havoidD j))
    (fun j => collar_level_exclusion_zero d π he m hm S (E j) (havoidE j))
    hnestD hnestE hshrinkD hshrinkE hlevelD hlevelE hDE A hA hcostS w hw hpos hpoint hη
  have hfinite : interiorPhysicalTollCost d g (exclusionToll S m) ρ < ∞ :=
    hC.trans_lt (ENNReal.add_lt_top.mpr ⟨hA, ENNReal.ofReal_lt_top⟩)
  refine ⟨ρ, θ, hρ, hρ0, hρ1,
    (interiorPhysicalTollCost_mono_weight d g (le_exclusionToll S m) ρ).trans hC, ?_⟩
  apply avoids_of_finite_exclusionToll ρ.val _ S m
  exact (show timeToll ρ.val (Ioo (⊥ : PathTime) ⊤) (exclusionToll S m) ≤
    interiorPhysicalTollCost d g (exclusionToll S m) ρ from le_add_self).trans_lt hfinite

end CircleDomainRigidity

end

end OAI

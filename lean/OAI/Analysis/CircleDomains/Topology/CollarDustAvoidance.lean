import OAI.Analysis.CircleDomains.Sobolev.LocalEnergyTwoEndedSplicing
import OAI.Analysis.CircleDomains.Sobolev.LocalEnergyOneEndedSplicing
import OAI.Analysis.CircleDomains.Selection.ExclusionTolls

namespace OAI

/-! The collar constructions preserve avoidance of arbitrary dust sets.
Auxiliary infinite tolls enforce the condition only at non-omitted times. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)]

theorem exists_twoEnded_splicing_avoiding_dust
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ B)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (p q : Sphere) (hpB : p ∈ B) (hqB : q ∈ B)
    (hp : p ≠ π OnePoint.infty) (hq : q ≠ π OnePoint.infty)
    (hstart : Tendsto (fun n => (Γ n).1.val ⊥) atTop (𝓝 p))
    (hend : Tendsto (fun n => (Γ n).1.val ⊤) atTop (𝓝 q))
    (O P : Set Sphere) (hO : IsOpen O) (hP : IsOpen P) (hpO : p ∈ O) (hqP : q ∈ P)
    (hOP : Disjoint O P)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hgO : (∫⁻z in (fun z : ℂ => π (z : Sphere)) ⁻¹' O, g (z : Sphere) ^ 2) < ∞)
    (hgP : (∫⁻z in (fun z : ℂ => π (z : Sphere)) ⁻¹' P, g (z : Sphere) ^ 2) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (S : Set Sphere) (hS : Disjoint S d.quotientDomain)
    (havoid : ∀n t, (Γ n).1.val t ∉ S)
    (A : ℝ≥0∞) (hA : A < ∞)
    (hcost : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A))
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ = p ∧ ρ.val ⊤ = q ∧
      interiorPhysicalTollCost d g m ρ ≤ A + ENNReal.ofReal η ∧
      ∀t ∈ Ioo (⊥ : PathTime) ⊤, ρ.val t ∉ S := by
  have hmS (x : Sphere) (hx : x ∈ d.quotientDomain) : exclusionToll S m x = 0 := by
    rw [exclusionToll_eq S m (fun hs => Set.disjoint_left.mp hS hs hx)]
    exact hm x hx
  have hcostS : Tendsto (fun n => physicalTollCost d g (exclusionToll S m) (Γ n).1)
      atTop (𝓝 A) := by
    convert hcost using 1
    funext n
    exact physicalTollCost_exclusion d g m S (Γ n).1 (havoid n)
  obtain ⟨ρ, θ, hρ, hρ0, hρ1, hC⟩ := exists_twoEnded_splicing_of_local_energy
    hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad
    ν N Γ hΓ p q hpB hqB hp hq hstart hend O P hO hP hpO hqP hOP
    g hg hgO hgP (exclusionToll S m) hmS A hA hcostS w hw hpos hpoint hη
  have hfinite : interiorPhysicalTollCost d g (exclusionToll S m) ρ < ∞ :=
    hC.trans_lt (ENNReal.add_lt_top.mpr ⟨hA, ENNReal.ofReal_lt_top⟩)
  refine ⟨ρ, θ, hρ, hρ0, hρ1,
    (interiorPhysicalTollCost_mono_weight d g (le_exclusionToll S m) ρ).trans hC, ?_⟩
  apply avoids_of_finite_exclusionToll ρ.val _ S m
  exact (show timeToll ρ.val (Ioo (⊥ : PathTime) ⊤) (exclusionToll S m) ≤
    interiorPhysicalTollCost d g (exclusionToll S m) ρ from le_add_self).trans_lt hfinite

theorem exists_oneEnded_splicing_avoiding_dust
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ B)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (F : Set Sphere) (hF : F ⊆ d.quotientDomain) (hstart : ∀n, (Γ n).1.val ⊥ ∈ F)
    (p : Sphere) (hpB : p ∈ B) (hp : p ≠ π OnePoint.infty)
    (hend : Tendsto (fun n => (Γ n).1.val ⊤) atTop (𝓝 p))
    (O : Set Sphere) (hO : IsOpen O) (hpO : p ∈ O) (hFO : Disjoint F O)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hgO : (∫⁻z in (fun z : ℂ => π (z : Sphere)) ⁻¹' O, g (z : Sphere) ^ 2) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (S : Set Sphere) (hS : Disjoint S d.quotientDomain)
    (havoid : ∀n t, (Γ n).1.val t ∉ S)
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
  have hmS (x : Sphere) (hx : x ∈ d.quotientDomain) : exclusionToll S m x = 0 := by
    rw [exclusionToll_eq S m (fun hs => Set.disjoint_left.mp hS hs hx)]
    exact hm x hx
  have hcostS : Tendsto (fun n => physicalTollCost d g (exclusionToll S m) (Γ n).1)
      atTop (𝓝 A) := by
    convert hcost using 1
    funext n
    exact physicalTollCost_exclusion d g m S (Γ n).1 (havoid n)
  obtain ⟨ρ, θ, hρ, hρ0, hρ1, hC⟩ := exists_oneEnded_splicing_of_local_energy
    hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad
    ν N Γ hΓ F hF hstart p hpB hp hend O hO hpO hFO
    g hg hgO (exclusionToll S m) hmS A hA hcostS w hw hpos hpoint hη
  have hfinite : preterminalToll ρ.val (exclusionToll S m) < ∞ :=
    (show preterminalToll ρ.val (exclusionToll S m) ≤
      (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
      preterminalToll ρ.val (exclusionToll S m) from le_add_self).trans_lt
      (hC.trans_lt (ENNReal.add_lt_top.mpr ⟨hA, ENNReal.ofReal_lt_top⟩))
  refine ⟨ρ, θ, hρ, hρ0, hρ1,
    (add_le_add le_rfl (preterminalToll_mono ρ.val (le_exclusionToll S m))).trans hC, ?_⟩
  rw [preterminalToll_eq_timeToll] at hfinite
  exact avoids_of_finite_exclusionToll ρ.val _ S m hfinite

end CircleDomainRigidity

end

end OAI

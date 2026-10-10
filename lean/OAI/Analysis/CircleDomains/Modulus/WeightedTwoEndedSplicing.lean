import OAI.Analysis.CircleDomains.Selection.ActualTwoEndedSplicing
import OAI.Analysis.CircleDomains.Modulus.WeightedCollarArcs
import OAI.Analysis.CircleDomains.Topology.CollarEndpointSubsequence

namespace OAI

/-! Two-ended splicing for the actual weighted smooth collars. All short
joining arcs, path restrictions, and limiting budgets are constructed. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)]

theorem exists_weighted_twoEnded_splicing
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
    {B : Set Sphere}
    (D : ℕ → WeightedCollar d.physicalDomain π B p (fun z => g (z : Sphere)))
    (E : ℕ → WeightedCollar d.physicalDomain π B q (fun z => g (z : Sphere)))
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
      interiorPhysicalTollCost d g m ρ ≤ A + ENNReal.ofReal η := by
  have hD (j : ℕ) : IsOpen (D j).region := (D j).isOpen_region hπ hclosed hsurj hr
  have hE (j : ℕ) : IsOpen (E j).region := (E j).isOpen_region hπ hclosed hsurj hr
  obtain ⟨s, hs, hsends⟩ := exists_subsequence_in_nested_endpoint_neighborhoods
    (fun n => (Γ n).1.val ⊥) (fun n => (Γ n).1.val ⊤) hstart hend
    (fun j => (D j).region) (fun j => (E j).region)
    (fun j => (hD j).mem_nhds ((D j).point_mem_region hsurj hp))
    (fun j => (hE j).mem_nhds ((E j).point_mem_region hsurj hq))
  apply exists_actual_twoEnded_collar_splicing d hU hG ν N (fun n => Γ (s n))
    (fun n => hΓ (s n)) p q (fun j => (D j).region) (fun j => (E j).region)
    hD hE hnestD hnestE hshrinkD hshrinkE (fun n => (hsends n).1) (fun n => (hsends n).2)
    hDE g hg m
    (fun j z hz => hm z ((D j).frontier_region_subset_quotient d π hπ he (hD j) hz))
    (fun j z hz => hm z ((E j).frontier_region_subset_quotient d π hπ he (hE j) hz))
    A hA (hcost.comp hs.tendsto_atTop)
  · intro j z hz ε hε
    exact exists_small_weighted_collar_arcs d hU hdisj π hπ he ν N g hg m hm
      (D (j+1)) (hD (j+1)) (T := closure (D j).region)
      (fun z hz => (show π (z : Sphere) ∈ closure (D j).region from subset_closure (hlevelD j hz))) hz hε
  · intro j z hz ε hε
    exact exists_small_weighted_collar_arcs d hU hdisj π hπ he ν N g hg m hm
      (E (j+1)) (hE (j+1)) (T := closure (E j).region)
      (fun z hz => (show π (z : Sphere) ∈ closure (E j).region from subset_closure (hlevelE j hz))) hz hε
  · intro z hz ε hε
    exact exists_small_weighted_collar_arcs d hU hdisj π hπ he ν N g hg m hm
      (D 0) (hD 0) (T := univ) (fun _ _ => mem_univ _) hz hε
  · intro z hz ε hε
    exact exists_small_weighted_collar_arcs d hU hdisj π hπ he ν N g hg m hm
      (E 0) (hE 0) (T := univ) (fun _ _ => mem_univ _) hz hε
  · exact hw
  · exact hpos
  · exact hpoint
  · exact hη

end CircleDomainRigidity

end

end OAI

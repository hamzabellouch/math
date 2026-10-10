import OAI.Analysis.CircleDomains.Selection.ActualOneEndedSplicing
import OAI.Analysis.CircleDomains.Modulus.WeightedCollarLevelTolls
import OAI.Analysis.CircleDomains.Topology.CollarEndpointSubsequence

namespace OAI

/-! One-ended splicing using actual weighted smooth collars, retaining
an original initial point in the prescribed set. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)]

theorem exists_weighted_oneEnded_splicing_of_level_toll_zero
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (F : Set Sphere) (hstart : ∀n, (Γ n).1.val ⊥ ∈ F)
    (p : Sphere) (hp : p ≠ π OnePoint.infty)
    (hend : Tendsto (fun n => (Γ n).1.val ⊤) atTop (𝓝 p))
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (m : Sphere → ℝ≥0∞) (hzero : ∀n, m ((Γ n).1.val ⊥) = 0)
    {B : Set Sphere}
    (D : ℕ → WeightedCollar d.physicalDomain π B p (fun z => g (z : Sphere)))
    (hm : ∀j z, (D j).function z = (D j).level → m (π (z : Sphere)) = 0)
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
        preterminalToll ρ.val m ≤ A + ENNReal.ofReal η := by
  have hD (j : ℕ) : IsOpen (D j).region := (D j).isOpen_region hπ hclosed hsurj hr
  have hDn (j : ℕ) : (D j).region ∈ 𝓝 p :=
    (hD j).mem_nhds ((D j).point_mem_region hsurj hp)
  obtain ⟨s, hs, hsends⟩ := exists_subsequence_in_nested_endpoint_neighborhoods
    (fun n => (Γ n).1.val ⊤) (fun n => (Γ n).1.val ⊤) hend hend
    (fun j => (D j).region) (fun j => (D j).region) hDn hDn
  apply exists_actual_oneEnded_collar_splicing d hU hG ν N (fun n => Γ (s n))
    (fun n => hΓ (s n)) F (fun n => hstart (s n)) p (fun j => (D j).region)
    hD hnest hshrink
    (fun n hx => Set.disjoint_left.mp hDF (hstart (s n)) hx)
    (fun n => (hsends n).1) g hg m
    (fun j => (D j).frontier_toll_zero d π hπ (hD j) m (hm j))
    (fun n => hzero (s n)) A hA (hcost.comp hs.tendsto_atTop)
  · intro j z hz ε hε
    exact exists_small_weighted_collar_arcs_of_level_toll_zero d hU hdisj π hπ he ν N g hg m
      (D (j+1)) (hm (j+1)) (hD (j+1)) (T := closure (D j).region)
      (fun z hz => (show π (z : Sphere) ∈ closure (D j).region from subset_closure (hlevel j hz))) hz hε
  · intro z hz ε hε
    exact exists_small_weighted_collar_arcs_of_level_toll_zero d hU hdisj π hπ he ν N g hg m
      (D 0) (hm 0) (hD 0) (T := univ) (fun _ _ => mem_univ _) hz hε
  · exact hw
  · exact hpos
  · exact hpoint
  · exact hη

end CircleDomainRigidity

end

end OAI

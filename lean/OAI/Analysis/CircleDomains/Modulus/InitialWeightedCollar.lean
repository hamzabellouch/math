import OAI.Analysis.CircleDomains.Modulus.WeightedCollarArcs
import OAI.Analysis.CircleDomains.Topology.InitialCollarSplicing

namespace OAI

/-! Initial collar splicing for the actual smooth weighted collars.
The local joining arcs are constructed, rather than assumed. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)]

theorem exists_initial_weighted_collar_path
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    {B : Set Sphere} (p : Sphere)
    (D : ℕ → WeightedCollar d.physicalDomain π B p (fun z => g (z : Sphere)))
    (hnest : ∀j, closure (D (j+1)).region ⊆ (D j).region)
    (hshrink : ∀W ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, closure (D j).region ⊆ W)
    (hlevel : ∀j, {z | (D (j+1)).function z = (D (j+1)).level} ⊆
      (fun z : ℂ => π (z : Sphere)) ⁻¹' (D j).region)
    (hstart : ∀n, (Γ n).1.val ⊥ ∈ (D (n+1)).region)
    (hend : ∀n, (Γ n).1.val ⊤ ∉ (D 0).region)
    (A : ℝ≥0∞) (hA : A < ∞)
    (hcostlim : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A))
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀y ∈ d.physicalDomain, w ≤ g y)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    {η : ℝ} (hη : 0 < η) :
    ∃ (k : ℕ) (α : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (α.val, θ) ∧ α.val ⊥ = p ∧
      α.val ⊤ = (Γ k).1.val (firstExitTime (Γ k).1.val (D 0).region) ∧
      (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint α) +
        timeToll α.val (Ioo (⊥ : PathTime) ⊤) m ≤ A + ENNReal.ofReal η := by
  have hD (j : ℕ) : IsOpen (D j).region := (D j).isOpen_region hπ hclosed hsurj hr
  apply exists_initial_collar_path d hU hG ν N Γ hΓ p (fun j => (D j).region)
    hD hnest hshrink hstart hend g hg m
    (fun j x hx => hm x ((D j).frontier_region_subset_quotient d π hπ he (hD j) hx))
    A hA hcostlim
  · intro j x hx ε hε
    exact exists_small_weighted_collar_arcs d hU hdisj π hπ he ν N g hg m hm
      (D (j+1)) (hD (j+1)) (T := closure (D j).region)
      (fun z hz => (show π (z : Sphere) ∈ closure (D j).region from
        subset_closure (hlevel j hz))) hx hε
  · exact hw
  · exact hpos
  · exact hpoint
  · exact hη

end CircleDomainRigidity

end

end OAI

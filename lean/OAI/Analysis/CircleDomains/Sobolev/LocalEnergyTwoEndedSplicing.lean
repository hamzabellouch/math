import OAI.Analysis.CircleDomains.Modulus.WeightedTwoEndedSplicing
import OAI.Analysis.CircleDomains.Modulus.ShrinkingLocalWeightedCollars

namespace OAI

/-! The two-ended collar lemma with its collars constructed from the
published coarea, regular-value, one-manifold, and Schoenflies inputs. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)]

theorem exists_twoEnded_splicing_of_local_energy
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
    (A : ℝ≥0∞) (hA : A < ∞)
    (hcost : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A))
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ = p ∧ ρ.val ⊤ = q ∧
      interiorPhysicalTollCost d g m ρ ≤ A + ENNReal.ofReal η := by
  have hgc : Measurable (fun z : ℂ => g (z : Sphere)) :=
    hg.comp OnePoint.continuous_coe.measurable
  obtain ⟨D, hD0, hDn, hDl, hDs⟩ := exists_shrinking_local_weighted_collars
    hcoarea hsard hsch d.physicalDomain π hπ hclosed hsurj hr hB hTD hbad
    hpB hp hO hpO (fun z : ℂ => g (z : Sphere)) hgc hgO
  obtain ⟨E, hE0, hEn, hEl, hEs⟩ := exists_shrinking_local_weighted_collars
    hcoarea hsard hsch d.physicalDomain π hπ hclosed hsurj hr hB hTD hbad
    hqB hq hP hqP (fun z : ℂ => g (z : Sphere)) hgc hgP
  exact exists_weighted_twoEnded_splicing d hU hG hdisj π hπ hclosed hsurj hr he ν N
    Γ hΓ p q hp hq hstart hend g hg m hm D E hDn hEn hDs hEs hDl hEl
    (hOP.mono hD0 hE0) A hA hcost w hw hpos hpoint hη

end CircleDomainRigidity

end

end OAI

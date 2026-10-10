import OAI.Analysis.CircleDomains.Modulus.WeightedOneEndedSplicing
import OAI.Analysis.CircleDomains.Modulus.ShrinkingLocalWeightedCollars

namespace OAI

/-! The one-ended collar lemma with its collars constructed from the
published coarea, regular-value, one-manifold, and Schoenflies inputs. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)]

theorem exists_oneEnded_splicing_of_local_energy
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
    (A : ℝ≥0∞) (hA : A < ∞)
    (hcost : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A))
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∧ ρ.val ⊤ = p ∧
      (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
        preterminalToll ρ.val m ≤ A + ENNReal.ofReal η := by
  have hgc : Measurable (fun z : ℂ => g (z : Sphere)) :=
    hg.comp OnePoint.continuous_coe.measurable
  obtain ⟨D, hD0, hDn, hDl, hDs⟩ := exists_shrinking_local_weighted_collars
    hcoarea hsard hsch d.physicalDomain π hπ hclosed hsurj hr hB hTD hbad
    hpB hp hO hpO (fun z : ℂ => g (z : Sphere)) hgc hgO
  exact exists_weighted_oneEnded_splicing d hU hG hdisj π hπ hclosed hsurj hr he ν N
    Γ hΓ F hF hstart p hp hend g hg m hm D hDn hDs hDl
    (hFO.mono_right hD0) A hA hcost w hw hpos hpoint hη

end CircleDomainRigidity

end

end OAI

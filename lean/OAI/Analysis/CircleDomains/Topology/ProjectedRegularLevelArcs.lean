import OAI.Analysis.CircleDomains.Topology.SphereRegularLevelArcs
import OAI.Analysis.CircleDomains.Modulus.InterleavedCollarCost
import OAI.Analysis.CircleDomains.Probability.DomainPhysicalOccupation

namespace OAI

/-! Short physical regular-level arcs descend through the actual domain
homeomorphism. Their cost is unchanged and their dust toll vanishes. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)]

theorem exists_small_projected_regular_level_arcs
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (ν : Measure Sphere)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    {f : ℂ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) {t : ℝ}
    (hreg : IsPlanarRegularValue f t)
    (hgood : ∀z, f z = t → (z : Sphere) ∈ d.physicalDomain)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hfinite : (∫⁻z in {z | f z = t}, g (z : Sphere) ∂(μH[1] : Measure ℂ)) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    {z : ℂ} (hz : f z = t) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ W : Set Sphere, IsOpen W ∧ π (z : Sphere) ∈ W ∧
      ∀a ∈ W ∩ (π '' (((↑) : ℂ → Sphere) '' {z | f z = t})),
      ∀b ∈ W ∩ (π '' (((↑) : ℂ → Sphere) '' {z | f z = t})),
        ∃ρ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (ρ.1.val, ρ.2) ∧
          ρ.1.val ⊥ = a ∧ ρ.1.val ⊤ = b ∧
          range ρ.1.val ⊆ π '' (((↑) : ℂ → Sphere) '' {z | f z = t}) ∧
          physicalTollCost d g m ρ.1 < ε := by
  obtain ⟨V, hV, hzV, hsmall⟩ := exists_small_sphere_regular_level_arcs
    hf hreg g hg hfinite hz hε
  let W : Set Sphere := Subtype.val '' (d.domainEquiv '' (Subtype.val ⁻¹' V))
  have hW : IsOpen W := hU.isOpenMap_subtype_val _
    (d.domainEquiv.isOpenMap _ (hV.preimage continuous_subtype_val))
  have hzW : π (z : Sphere) ∈ W := by
    refine ⟨d.domainEquiv ⟨(z : Sphere), hgood z hz⟩, ?_, he _⟩
    exact ⟨⟨(z : Sphere), hgood z hz⟩, hzV, rfl⟩
  refine ⟨W, hW, hzW, ?_⟩
  intro a ha b hb
  obtain ⟨_, ⟨za, hza, rfl⟩, rfl⟩ := ha.2
  obtain ⟨_, ⟨zb, hzb, rfl⟩, rfl⟩ := hb.2
  have hpre : ∀w : ℂ, f w = t → π (w : Sphere) ∈ W → (w : Sphere) ∈ V := by
    intro w hw hWw
    obtain ⟨u, ⟨v, hv, rfl⟩, hval⟩ := hWw
    have heq : d.domainEquiv v = d.domainEquiv ⟨(w : Sphere), hgood w hw⟩ :=
      Subtype.ext (hval.trans (he ⟨(w : Sphere), hgood w hw⟩).symm)
    have hvw := congrArg Subtype.val (d.domainEquiv.injective heq)
    change (v : Sphere) = (w : Sphere) at hvw
    change (w : Sphere) ∈ V
    rw [← hvw]
    exact hv
  obtain ⟨α, hα0, hα1, hαrange, hαcost⟩ := hsmall (za : Sphere)
    ⟨hpre za hza ha.1, ⟨za, hza, rfl⟩⟩ (zb : Sphere)
    ⟨hpre zb hzb hb.1, ⟨zb, hzb, rfl⟩⟩
  have hα : ∀s, α.val s ∈ d.physicalDomain := by
    intro s
    obtain ⟨w, hw, heq⟩ := hαrange (mem_range_self s)
    exact heq ▸ hgood w hw
  let ρ := finiteProjectedPhysicalPath d.domainEquiv d.basePoint α hα
  have hρval (s : PathTime) : ρ.val s = π (α.val s) := he ⟨α.val s, hα s⟩
  have hzero : boundaryToll ρ.val m = 0 := by
    apply ENNReal.tsum_eq_zero.mpr
    intro s
    exact hm _ (projectDomainPath_mem d.domainEquiv α.val hα s)
  refine ⟨(ρ, fun _ => inactiveTag), projected_physical_path_allowed d hdisj ν N α hα,
    ?_, ?_, ?_, ?_⟩
  · exact (hρval ⊥).trans (congrArg π hα0)
  · exact (hρval ⊤).trans (congrArg π hα1)
  · rintro q ⟨s, rfl⟩
    exact ⟨α.val s, hαrange (mem_range_self s), (hρval s).symm⟩
  · change (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
      boundaryToll ρ.val m < ε
    rw [hzero, add_zero]
    change (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint
      (finiteProjectedPhysicalPath d.domainEquiv d.basePoint α hα)) < ε
    rwa [dyadicPhysicalOccupation_project]

end CircleDomainRigidity

end

end OAI

import OAI.Analysis.CircleDomains.Topology.CenteredJordanCoordinate
import OAI.Analysis.CircleDomains.Probability.CompactArcLaw
import OAI.Analysis.CircleDomains.Topology.MeanArcIndex

namespace OAI

/-! Transport of the constructed terminal arc law to centered disk coordinates.
The coordinate extension is only evaluated on the closed collar. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

lemma terminalArcSet_mapsTo_closure {V : Set Sphere} {b : Sphere}
    {γ : C(PathTime, Sphere)} (hγ : γ ∈ terminalArcSet V b) (hb : b ∈ V) :
    MapsTo γ univ (closure V) := by
  intro t _
  by_cases h0 : t = ⊥
  · exact h0 ▸ frontier_subset_closure hγ.2.1
  by_cases h1 : t = ⊤
  · exact h1 ▸ hγ.2.2.1.symm ▸ subset_closure hb
  exact subset_closure (hγ.2.2.2 ⟨lt_of_le_of_ne bot_le (Ne.symm h0),
    lt_of_le_of_ne le_top h1⟩)

def diskTerminalArcSet : Set C(PathTime, ℂ) :=
  {γ | Injective γ ∧ ‖γ 0‖ = 1 ∧ γ 1 = 0 ∧
    ∀ t ∈ Ioo (0 : PathTime) 1, ‖γ t‖ < 1}

theorem centeredJordanPath_mem (K : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior K)
    (F : C(Sphere, ℂ))
    (hF : EqOn F (centeredJordanCoordinate K b)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior K)))
    {γ : C(PathTime, Sphere)}
    (hγ : γ ∈ terminalArcSet (((↑) : ℂ → Sphere) '' jordanInterior K) b) :
    F.comp γ ∈ diskTerminalArcSet := by
  have hcl := terminalArcSet_mapsTo_closure hγ hb
  have he (t : PathTime) : (F.comp γ) t = centeredJordanCoordinate K b (γ t) :=
    hF (hcl (mem_univ t))
  refine ⟨fun s t h => hγ.1 ?_, ?_, ?_, ?_⟩
  · exact centeredJordanCoordinate_injOn K hb (hcl (mem_univ s))
      (hcl (mem_univ t)) ((he s).symm.trans (h.trans (he t)))
  · rw [he]
    exact centeredJordanCoordinate_norm_boundary K hb hγ.2.1
  · rw [he]
    change centeredJordanCoordinate K b (γ ⊤) = 0
    rw [hγ.2.2.1, centeredJordanCoordinate_self]
  · intro t ht
    rw [he]
    exact diskCentering_norm_lt (sphereJordanCoordinate_norm_lt K hb)
      (sphereJordanCoordinate_norm_lt K (hγ.2.2.2 ht))

variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

def centeredArcLaw (η : ProbabilityMeasure C(PathTime, Sphere)) (F : C(Sphere, ℂ)) :
    ProbabilityMeasure C(PathTime, ℂ) := η.map F.comp

theorem centeredArcLaw_hit (K : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior K)
    (F : C(Sphere, ℂ))
    (hF : EqOn F (centeredJordanCoordinate K b)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior K)))
    (η : ProbabilityMeasure C(PathTime, Sphere))
    (hη : ∀ᵐ γ ∂(η : Measure C(PathTime, Sphere)),
      γ ∈ terminalArcSet (((↑) : ℂ → Sphere) '' jordanInterior K) b)
    {x : Sphere} (hx : x ∈ closure (((↑) : ℂ → Sphere) '' jordanInterior K)) :
    pathHitProbability (centeredArcLaw η F) (centeredJordanCoordinate K b x) =
      pathHitProbability η x := by
  rw [pathHitProbability, centeredArcLaw, ProbabilityMeasure.map_apply' η
    F.continuous_postcomp.measurable.aemeasurable (isClosed_paths_hitting _).measurableSet]
  apply measure_congr
  filter_upwards [hη] with γ hγ
  apply propext
  change (∃ t, F (γ t) = centeredJordanCoordinate K b x) ↔ ∃ t, γ t = x
  constructor
  · rintro ⟨t, ht⟩
    have hcl := terminalArcSet_mapsTo_closure hγ hb (mem_univ t)
    exact ⟨t, centeredJordanCoordinate_injOn K hb hcl hx ((hF hcl).symm.trans ht)⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, hF (terminalArcSet_mapsTo_closure hγ hb (mem_univ t))⟩

theorem exists_centered_compact_arc_law (K : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior K)
    (A : Set C(PathTime, Sphere)) (hA : IsCompact A)
    (hAS : A ⊆ terminalArcSet (((↑) : ℂ → Sphere) '' jordanInterior K) b)
    (η : ProbabilityMeasure C(PathTime, Sphere))
    (hη : ∀ᵐ γ ∂(η : Measure C(PathTime, Sphere)), γ ∈ A) :
    ∃ (L : Set C(PathTime, ℂ)) (ν : ProbabilityMeasure C(PathTime, ℂ)),
      IsCompact L ∧ L ⊆ diskTerminalArcSet ∧
      (∀ᵐ γ ∂(ν : Measure C(PathTime, ℂ)), γ ∈ L) ∧
      ∀ x ∈ closure (((↑) : ℂ → Sphere) '' jordanInterior K),
        pathHitProbability ν (centeredJordanCoordinate K b x) = pathHitProbability η x := by
  obtain ⟨F, hF⟩ := exists_centeredJordanExtension K hb
  let L := F.comp '' A
  have hL : IsCompact L := hA.image F.continuous_postcomp
  refine ⟨L, centeredArcLaw η F, hL, ?_, ?_, ?_⟩
  · rintro _ ⟨γ, hγ, rfl⟩
    exact centeredJordanPath_mem K hb F hF (hAS hγ)
  · rw [centeredArcLaw, ProbabilityMeasure.toMeasure_map]
    apply (ae_map_iff F.continuous_postcomp.measurable.aemeasurable hL.measurableSet).mpr
    exact hη.mono fun γ hγ => mem_image_of_mem F.comp hγ
  · intro x hx
    exact centeredArcLaw_hit K hb F hF η (hη.mono fun _ h => hAS h) hx

end CircleDomainRigidity

end

end OAI

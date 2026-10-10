import OAI.Analysis.CircleDomains.Topology.MeanCircleCompatibility
import OAI.Analysis.CircleDomains.Topology.SubarcGenericLevels

namespace OAI

/-! Apply mean-circle compatibility to the actual compact subarc law.
Both finite counts and free avoidance are inherited from the original
endpoint law through its proved measurable selection witness. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [PolishSpace X]
  [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem subarc_mean_circle_compatibility
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hLusin : FiniteTorusAnalyticMeasurability)
    (π : Y → X) (hπ : Continuous π) (hsurj : Surjective π)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    {G : Set Y} (hG : IsOpen G) {B U Flags S : Set X}
    (hB : IsCompact B) (hTD : IsTotallyDisconnected B) (hdust : π '' Gᶜ ⊆ B)
    (hU : IsSigmaCompact U) (hFlags : Flags.Countable)
    (hdisj : Disjoint U Flags) (hS : IsOpen S)
    (harcs : ∀ C : Set X, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (μ ν : ProbabilityMeasure C(PathTime, X)) (hred : IsSubarcLawReduction μ ν)
    (hη : η.map Subtype.val = ν)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S)) (hinj : InjOn F S)
    (R : ℕ → Set (X × UnitAddCircle)) (hR : ∀ i, IsClosed (R i))
    (hlength : ∀ i, ∀ᵐ t : UnitAddCircle ∂volume,
      (μH[1] : Measure Y) (G ∩ π ⁻¹' {x | (x, t) ∈ R i}) < ∞)
    (hgeneric : ∀ i, ∀ᵐ t : UnitAddCircle ∂volume,
      (∫⁻ γ, pathImageCount {x | (x, t) ∈ R i} γ
        ∂(μ : Measure C(PathTime, X))) < ∞ ∧
      ∀ᵐ γ : C(PathTime, X) ∂(μ : Measure C(PathTime, X)),
        ¬ ∃ x ∈ range γ ∩ (Uᶜ \ Flags), (x, t) ∈ R i)
    (Rnew : Set (X × UnitAddCircle)) (hnew : IsClosed Rnew)
    (hnewlevel : ∀ x ∈ (Uᶜ \ Flags) ∩ S, ∀ t, (x, t) ∈ Rnew ↔
      diskMeanCircle hsch K hKS (η.map f) (F x) = t)
    (n : ℕ) (labels : Fin n → ℕ) :
    (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
      (freeComponentFailure ((Uᶜ \ Flags) ∩ S) Rnew R labels) = 0 := by
  have hUm : MeasurableSet U := by
    obtain ⟨Q, hQ, hcov⟩ := hU
    rw [← hcov]
    exact MeasurableSet.iUnion (fun n => (hQ n).measurableSet)
  apply mean_circle_compatibility_of_generic_levels hsch hsep hLusin π hπ hsurj hfiber
    hG hB hTD hdust (hUm.compl.diff hFlags.measurableSet) hS harcs
    A K hK hKS η F f hf hmap h0 h1 hF hinj R hR hlength _ Rnew hnew hnewlevel n labels
  intro i
  have hgood := hred.generic_levels ((hR i).preimage continuous_swap)
    U Flags hU hFlags hdisj (hgeneric i)
  filter_upwards [hgood] with t ht
  refine ⟨by simpa only [hη, mem_preimage, Prod.swap_prod_mk] using ht.1, ?_⟩
  have hm := ht.2
  rw [← hη, ProbabilityMeasure.toMeasure_map] at hm
  exact ae_of_ae_map measurable_subtype_coe.aemeasurable hm

end CircleDomainRigidity

end

end OAI

import OAI.Analysis.CircleDomains.Rigidity.MeanCircleLevelTrace
import OAI.Analysis.CircleDomains.Probability.FiniteTupleLevelLaws
import OAI.Analysis.CircleDomains.Modulus.FiniteLevelPayments

namespace OAI

/-! Ordered compatibility of the actual mean circle coordinate follows
from the generic intersection laws, finite physical prior lengths, and
its proved null traces. No compatibility of the new coordinate is assumed. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [PolishSpace X]
  [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem mean_circle_compatibility_of_generic_levels
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hLusin : FiniteTorusAnalyticMeasurability)
    (π : Y → X) (hπ : Continuous π) (hsurj : Surjective π)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    {G : Set Y} (hG : IsOpen G) {B Free S : Set X}
    (hB : IsCompact B) (hTD : IsTotallyDisconnected B) (hdust : π '' Gᶜ ⊆ B)
    (hFree : MeasurableSet Free) (hS : IsOpen S)
    (harcs : ∀ C : Set X, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S)) (hinj : InjOn F S)
    (R : ℕ → Set (X × UnitAddCircle)) (hR : ∀ i, IsClosed (R i))
    (hlength : ∀ i, ∀ᵐ t : UnitAddCircle ∂volume,
      (μH[1] : Measure Y) (G ∩ π ⁻¹' {x | (x, t) ∈ R i}) < ∞)
    (hgeneric : ∀ i, ∀ᵐ t : UnitAddCircle ∂volume,
      (∫⁻ γ, pathImageCount {x | (x, t) ∈ R i} γ
        ∂((η.map Subtype.val : ProbabilityMeasure C(PathTime, X)) : Measure _)) < ∞ ∧
      ∀ᵐ γ : A ∂(η : Measure A),
        ¬ ∃ x ∈ range γ.val ∩ Free, (x, t) ∈ R i)
    (Rnew : Set (X × UnitAddCircle)) (hnew : IsClosed Rnew)
    (hnewlevel : ∀ x ∈ Free ∩ S, ∀ t, (x, t) ∈ Rnew ↔
      diskMeanCircle hsch K hKS (η.map f) (F x) = t)
    (n : ℕ) (labels : Fin n → ℕ) :
    (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
      (freeComponentFailure (Free ∩ S) Rnew R labels) = 0 := by
  let H : (Fin n → UnitAddCircle) → Set X :=
    fun θ => {x | (x, θ) ∈ finiteLevelUnionGraph R labels}
  have hHunion (θ) : H θ = ⋃ j, {x | (x, θ j) ∈ R (labels j)} := by
    ext x
    simp [H, finiteLevelUnionGraph]
  have hcounts := ae_finite_tuple_level_law
    (fun j : Fin n => Prod.swap ⁻¹' R (labels j))
    (fun j => (hR (labels j)).preimage continuous_swap) Free η Subtype.val measurable_subtype_coe
    (fun j => (hgeneric (labels j)).mono fun t ht => by
      refine ⟨?_, ht.2⟩
      have hclosed : IsClosed {x | (x, t) ∈ R (labels j)} :=
        (hR (labels j)).preimage (continuous_id.prodMk continuous_const)
      have htfin := ht.1
      rw [ProbabilityMeasure.toMeasure_map,
        lintegral_map' (measurable_pathImageCount hclosed).aemeasurable
          measurable_subtype_coe.aemeasurable] at htfin
      exact htfin)
  have hlen := ae_finite_lintegral_level_union (μH[1] : Measure Y) volume
    (fun i t => G ∩ π ⁻¹' {x | (x, t) ∈ R i}) (fun _ => 1) labels
    (by simpa only [lintegral_one, Measure.restrict_apply_univ] using hlength)
  apply measure_freeComponentFailure_eq_zero hLusin n (hFree.inter hS.measurableSet)
    hnew hR labels (fun x => diskMeanCircle hsch K hKS (η.map f) (F x)) hnewlevel
  filter_upwards [hcounts, hlen] with θ hc hl
  have hcompact : IsCompact (H θ) :=
    ((isClosed_finiteLevelUnionGraph hR labels).preimage
      (continuous_id.prodMk continuous_const)).isCompact
  have hlengthH : (μH[1] : Measure Y) (π ⁻¹' H θ ∩ G) < ∞ := by
    have hset : (⋃ j, G ∩ π ⁻¹' {x | (x, θ j) ∈ R (labels j)}) = π ⁻¹' H θ ∩ G := by
      rw [hHunion, preimage_iUnion, inter_comm, inter_iUnion]
    simpa only [lintegral_one, Measure.restrict_apply_univ, hset] using hl
  have hfinite : (∫⁻ γ, pathImageCount (H θ) γ
      ∂((η.map Subtype.val : ProbabilityMeasure C(PathTime, X)) : Measure _)) < ∞ := by
    rw [ProbabilityMeasure.toMeasure_map, lintegral_map'
      (measurable_pathImageCount hcompact.isClosed).aemeasurable measurable_subtype_coe.aemeasurable]
    simpa only [hHunion, Prod.swap_prod_mk, mem_preimage] using hc.1
  have hmiss : ∀ᵐ γ : A ∂(η : Measure A), Disjoint (range γ.val ∩ H θ) Free := by
    filter_upwards [hc.2] with γ hγ
    apply disjoint_left.mpr
    rintro x ⟨hx, hxH⟩ hxF
    apply hγ
    refine ⟨x, ⟨hx, hxF⟩, ?_⟩
    simpa only [← hHunion, Prod.swap_prod_mk, mem_preimage] using hxH
  exact mean_circle_null_component_traces hsch hsep π hπ hsurj hfiber hG hB hTD hdust
    hcompact hlengthH hFree hS harcs A K hK hKS η F f hf hmap hmiss hfinite h0 h1 hF hinj

end CircleDomainRigidity

end

end OAI

import OAI.Analysis.CircleDomains.Rigidity.RawLevelNullTrace
import OAI.Analysis.CircleDomains.Modulus.FiniteLevelPayments
import OAI.Analysis.CircleDomains.Rigidity.TraceBandLevel

namespace OAI

/-! Compatibility for the actual raw path-cost barrier. Finite level
payments and square-summable point incidences give the null component
traces; the only descriptive-set input is the cited finite-torus form of
Kechris's analytic-measurability theorem. -/

open Set Function MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem freeComponentFailure_empty_labels
    {X T Λ : Type*} [TopologicalSpace X]
    (F : Set X) (Rnew : Set (X × T)) (R : Λ → Set (X × T)) (labels : Fin 0 → Λ) :
    freeComponentFailure F Rnew R labels = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro z ⟨⟨x, t, θ⟩, hx, _⟩
  have he : {y | (y, θ) ∈ finiteLevelUnionGraph R labels} = ∅ := by
    simp [finiteLevelUnionGraph]
  have hh := hx.2.2
  change (connectedComponentIn {y | (y, θ) ∈ finiteLevelUnionGraph R labels} x).Nontrivial at hh
  rw [he, connectedComponentIn_eq_empty (by simp)] at hh
  exact not_nontrivial_empty hh

theorem raw_barrier_compatibility_of_finite_level_payments
    {X Y : Type*} [MetricSpace X] [CompactSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    [MeasurableSpace C(PathTime, X)]
    (hLusin : FiniteTorusAnalyticMeasurability)
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Y → X) (hπ : Continuous π) (hsurj : Surjective π)
    (hfiber : ∀x, IsConnected (π ⁻¹' {x}))
    (he : ∀y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    {B F : Set X} (hB : IsCompact B) (hTD : IsTotallyDisconnected B)
    (hbad : π '' d.physicalDomainᶜ ⊆ B)
    (hBU : Bᶜ ⊆ d.quotientDomain) (hUB : Disjoint d.quotientDomain B)
    (hF : MeasurableSet F) (hFB : F ⊆ B) (hFU : F ⊆ closure d.quotientDomain)
    (harcs : ∀C : Set X, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (R : ℕ → Set (X × UnitAddCircle)) (hR : ∀i, IsClosed (R i))
    (hRlevels : ∀i x t, (x, t) ∈ R i ↔ (t, x) ∈ d.levels i)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (hlength : ∀i, ∀ᵐt ∂volume,
      (μH[1] : Measure Y) (d.physicalDomain ∩ π ⁻¹' {x | (x, t) ∈ R i}) < ∞)
    (hg : ∀i, ∀ᵐt ∂volume,
      (∫⁻y in d.physicalDomain ∩ π ⁻¹' {x | (x, t) ∈ R i}, g y
        ∂(μH[1] : Measure Y)) < ∞)
    (hm : (∑'x, m x ^ 2) ≠ ∞) (hmF : ∀x ∈ F, m x = 0)
    (hweights : ∀i, (∑'x, d.levelWeights i x ^ 2) ≠ ∞)
    (hincidence : ∀i x, volume {t | (x, t) ∈ R i} ≤ d.levelWeights i x)
    (ν : Measure X)
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (u v : X → ℝ) (hu : ∀x ∈ d.quotientDomain, |u x| ≤ 1)
    (hpay : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (htrace : ∀x ∈ F, Tendsto u (𝓝[d.quotientDomain] x) (𝓝 (v x)))
    (n : ℕ) (labels : Fin (n + 1) → ℕ)
    (hN : (Measure.pi (fun _ : Fin (n + 1) => (volume : Measure UnitAddCircle)))
      (N n labels) = 0) :
    (volume.prod (Measure.pi (fun _ : Fin (n + 1) => (volume : Measure UnitAddCircle))))
      (freeComponentFailure F (circleBandGraph d.quotientDomain u) R labels) = 0 := by
  let A : ℕ → UnitAddCircle → Set X := fun i t => {x | (x, t) ∈ R i}
  let H : (Fin (n + 1) → UnitAddCircle) → Set X :=
    fun θ => {x | (x, θ) ∈ finiteLevelUnionGraph R labels}
  have hHA (θ) : H θ = ⋃j, A (labels j) (θ j) := by
    ext x
    simp [H, A, finiteLevelUnionGraph]
  have hphysical (θ) : d.physicalDomain ∩ π ⁻¹' H θ =
      ⋃j, d.physicalDomain ∩ π ⁻¹' A (labels j) (θ j) := by
    rw [hHA, preimage_iUnion, inter_iUnion]
  have hlen := ae_finite_lintegral_level_union (μH[1] : Measure Y) volume
    (fun i t => d.physicalDomain ∩ π ⁻¹' A i t) (fun _ => 1) labels
    (by simpa only [lintegral_one, Measure.restrict_apply_univ] using hlength)
  have hweighted := ae_finite_lintegral_level_union (μH[1] : Measure Y) volume
    (fun i t => d.physicalDomain ∩ π ⁻¹' A i t) g labels hg
  have hatom (i : ℕ) : ∀ᵐt ∂volume, atomicBoundaryMeasure m (A i t) < ∞ := by
    apply ae_finite_atomic_level_payment volume (A i)
      (fun t => ((hR i).preimage (continuous_id.prodMk continuous_const)).measurableSet)
      (fun x => ((hR i).preimage (continuous_const.prodMk continuous_id)).measurableSet)
      m (d.levelWeights i) hm (hweights i) (hincidence i)
  have hatoms := ae_finite_lintegral_level_union (atomicBoundaryMeasure m) volume A
    (fun _ => 1) labels (by simpa only [lintegral_one, Measure.restrict_apply_univ] using hatom)
  have hgoodN : ∀ᵐθ ∂Measure.pi (fun _ : Fin (n + 1) => (volume : Measure UnitAddCircle)),
      θ ∉ N n labels := by simpa only [ae_iff, not_not, ofPred_mem_eq] using hN
  apply measure_freeComponentFailure_eq_zero hLusin (n + 1) hF
    (isCompact_circleBandGraph hu).isClosed hR labels (fun x => (v x : UnitAddCircle))
    (fun x hx _ => circleBandGraph_of_trace hu (hFU hx) (htrace x hx))
  filter_upwards [hlen, hweighted, hatoms, hgoodN] with θ hlenθ hgθ hmθ hNθ
  have hH : IsCompact (H θ) :=
    ((isClosed_finiteLevelUnionGraph hR labels).preimage
      (continuous_id.prodMk continuous_const)).isCompact
  have hlenH : (μH[1] : Measure Y) (π ⁻¹' H θ ∩ d.physicalDomain) < ∞ := by
    simpa only [lintegral_one, Measure.restrict_apply_univ, ← hphysical, inter_comm] using hlenθ
  have hgH : (∫⁻y in d.physicalDomain ∩ π ⁻¹' H θ, g y ∂(μH[1] : Measure Y)) < ∞ := by
    rwa [← hphysical] at hgθ
  have hmH : atomicBoundaryMeasure m (H θ) < ∞ := by
    simpa only [lintegral_one, Measure.restrict_apply_univ, ← hHA] using hmθ
  exact raw_barrier_null_component_traces d hU hG hdisj π hπ hsurj hfiber he hH hB hTD
    hbad hBU hUB hF hFB harcs hlenH g m hgH hmH hmF ν N u v hpay htrace n labels θ hNθ
    (by intro x hx; obtain ⟨j, hj⟩ := mem_iUnion.mp (hHA θ ▸ hx)
        exact ⟨j, (hRlevels _ _ _).mp hj⟩)

end CircleDomainRigidity

end

end OAI

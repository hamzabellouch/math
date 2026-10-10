import OAI.Analysis.CircleDomains.Modulus.LevelBarrierSlackExclusion
import OAI.Analysis.CircleDomains.Modulus.SelectedRealBandNorm
import OAI.Analysis.CircleDomains.Topology.MapDiskExclusion
import OAI.Analysis.CircleDomains.Uniformization.MixedLimitRealProjection

namespace OAI

/-! A real barrier test retains its actual presentation, band weight,
open map neighborhood, and the proved radius-dependent exclusion. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

structure RealExclusionWitness (base : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (C : MaskedCoordinateData base.physicalDomain base.quotientDomain π
      (fun x : base.dust => x.val)) where
  presentation : RealCoordinatePresentation base π C
  weight : Sphere → ℝ≥0∞
  weight_finite : (∑' x, weight x ^ 2) < ∞
  band_bound : ∀ x ∈ base.dust, ENNReal.ofReal
    (limsup presentation.coordinate.quotient (𝓝[base.quotientDomain] x) -
      liminf presentation.coordinate.quotient (𝓝[base.quotientDomain] x)) ≤ weight x
  radius : ℝ
  neighborhood : Set C(FiniteSource base.physicalDomain, ℂ)
  isOpen_neighborhood : IsOpen neighborhood
  excludes : ∀ {S : Type} {π' : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates base.physicalDomain π' σ}
    {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
    (M : RealModelExhaustion d O ε) (A : AssignedRealModelLimit M) (l : ℕ)
    (hG : IsOpen base.physicalDomain),
    Tendsto ε atTop (𝓝 0) → 3 * M.radius ≤ radius →
    d.physical l = presentation.coordinate.physical →
    Real.sqrt (∑' s, (d.upper l s - d.lower l s) ^ 2) ≤ (countingSquareNorm weight).toReal →
    finiteSourceMap A.function (A.plane_open_embedding hG).1 ∉ neighborhood

namespace RealExclusionWitness
variable {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {C : MaskedCoordinateData base.physicalDomain base.quotientDomain π
    (fun x : base.dust => x.val)}
  (W : RealExclusionWitness base π C)

 def sizedNeighborhood : Set (MapDiskData base.physicalDomain × ℝ) :=
    (W.neighborhood ×ˢ univ) ×ˢ Iio (W.radius / 3)

 theorem isOpen_sizedNeighborhood : IsOpen W.sizedNeighborhood :=
    (W.isOpen_neighborhood.prod isOpen_univ).prod isOpen_Iio

 theorem mem_sizedNeighborhood {F : C(FiniteSource base.physicalDomain, ℂ)}
    {c : ℂ} {r : ℝ≥0} {R : ℝ} (hF : F ∈ W.neighborhood) (hR : 3 * R < W.radius) :
    ((F, c, r), R) ∈ W.sizedNeighborhood :=
    ⟨⟨hF, mem_univ _⟩, by change R < W.radius / 3; linarith⟩
end RealExclusionWitness

namespace SelectedMixedModels
variable {hsch : PlanarSchoenflies} {base : PathCodeData Sphere Sphere}
  {hU : IsOpen base.quotientDomain} {hdense : Dense base.quotientDomain}
  {π : Sphere → Sphere}
  {he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val}
  {hB : base.dust = π '' base.physicalDomainᶜ}
  {I : Type*} [LinearOrder I] {D : I → SelectableMaskedCoordinate base π}
  {presentation : ∀ l, SelectedLevelPresentation hsch base π (D l).coordinate}
  {B₀ : Set base.dust}

 theorem excludes_retained_sized_real
    (F : SelectedMixedModels hsch base hU hdense π he hB D presentation B₀)
    (A : AssignedMixedModelLimit F.model) (hG : IsOpen base.physicalDomain)
    (l : I) (W : RealExclusionWitness base π (D l).coordinate)
    (hW : presentation l = Sum.inl W.presentation) (c : ℂ) (r : ℝ≥0) :
    ((finiteSourceMap A.function A.continuousOn, c, r), F.model.real.radius) ∉
      W.sizedNeighborhood := by
  intro hp
  obtain ⟨n, hphysical, hnorm⟩ := F.retains_real_band_norm l W.presentation hW
    W.weight W.weight_finite W.band_bound
  have hn := W.excludes F.model.real A.toReal n hG modelError_tendsto
    (show 3 * F.model.real.radius ≤ W.radius from by
      have h : F.model.real.radius < W.radius / 3 := hp.2
      linarith) hphysical hnorm
  exact hn hp.1.1

end SelectedMixedModels
end CircleDomainRigidity

end

end OAI

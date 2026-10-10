import OAI.Analysis.CircleDomains.Transfer.SelectedMixedModels
import OAI.Analysis.CircleDomains.Selection.SelectedRealSmallness

namespace OAI

/-! The real seed's collapse estimates survive the common mixed construction, even when
its real coordinates are enumerated differently and further marked points are retained. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

namespace SelectedMixedModels
variable {hsch : PlanarSchoenflies} {base : PathCodeData Sphere Sphere}
  {hU : IsOpen base.quotientDomain} {hdense : Dense base.quotientDomain}
  {π : Sphere → Sphere}
  {he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val}
  {hB : base.dust = π '' base.physicalDomainᶜ}
  {L : Type*} [LinearOrder L] {D : L → SelectableMaskedCoordinate base π}
  {presentation : ∀ l, SelectedLevelPresentation hsch base π (D l).coordinate}
  {B₀ : Set base.dust}

 def realCoordinates (F : SelectedMixedModels hsch base hU hdense π he hB D presentation B₀) :
    CountableRealCoordinates base.physicalDomain π (fun s : F.marks => s.val.val) :=
  realCoordinatesFromPresentations base hU hdense π he hB
    (fun l => (D l).coordinate) F.realLabels F.realPresentation F.marks F.support

 def withRadius (F : SelectedMixedModels hsch base hU hdense π he hB D presentation B₀)
    (R : ℝ) (hR : F.model.real.radius ≤ R) :
    SelectedMixedModels hsch base hU hdense π he hB D presentation B₀ :=
  { F with model := F.model.withRadius R hR }

 theorem retains_real_presentation
    (F : SelectedMixedModels hsch base hU hdense π he hB D presentation B₀)
    (l : L) (R : RealCoordinatePresentation base π (D l).coordinate)
    (hR : presentation l = Sum.inl R) :
    ∃ n, F.realLabels n = l ∧ F.realCoordinates.physical n = R.coordinate.physical ∧
      F.realCoordinates.coordinate n = R.coordinate.quotient :=
  F.real_cover l R hR

 theorem small_anchored_of_retained_tests
    (F : SelectedMixedModels hsch base hU hdense π he hB D presentation B₀)
    (EStar : Set Sphere) (A : Set (GradedRealTest base π EStar))
    (hpresentation : ∀ b ∈ A, ∃ (l : L)
      (R : RealCoordinatePresentation base π (D l).coordinate),
        presentation l = Sum.inl R ∧ R.coordinate = b.coordinate)
    (hcover : ∀ p ∈ base.dust \ (Subtype.val '' F.marks), ∀ k,
      ∃ b ∈ A, b.grade = k ∧ p ∈ b.region)
    (p : Sphere) (hp : p ∈ base.dust \ (Subtype.val '' F.marks)) :
    SmallAnchoredPlateaus F.realCoordinates EStar p := by
  intro δ hδ
  obtain ⟨k, hk⟩ := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (gt_mem_nhds hδ)).exists
  obtain ⟨b, hb, hbk, hpb⟩ := hcover p hp k
  obtain ⟨l, R, hR, hRb⟩ := hpresentation b hb
  obtain ⟨n, _, hphysical, hquotient⟩ := F.retains_real_presentation l R hR
  have hpq : F.realCoordinates.physical n = b.coordinate.physical := by
    rw [hphysical, hRb]
  have hqq : F.realCoordinates.coordinate n = b.coordinate.quotient := by
    rw [hquotient, hRb]
  refine ⟨n, b.region, b.region_open, hpb, ?_, ?_, ?_⟩
  · intro x hx
    rw [hqq]
    exact b.one x hx
  · intro x hx
    rw [hqq]
    exact b.zero x hx
  · have hn := b.toUngatedRealTest.ordinary_norm_le_size
      (by rw [hdense.closure_eq]; exact subset_univ _)
      (fun s : F.marks => s.val.val)
      (Subtype.val_injective.comp Subtype.val_injective)
      (by rintro _ ⟨s, rfl⟩; exact s.val.property)
    have hbsmall : b.toUngatedRealTest.size.toReal < 1 / ((k : ℝ) + 1) := by
      apply ENNReal.toReal_lt_of_lt_ofReal
      rw [← hbk]
      exact b.small
    apply lt_of_le_of_lt _ (hbsmall.trans hk)
    change Real.sqrt (∫ x in realChartDomain base.physicalDomain,
      gradientEnergy (F.realCoordinates.physical n)
        (fun z => sphericalMetricFactor z • 1) x) +
      Real.sqrt (∑' s : F.marks,
        (limsup (F.realPresentation n).coordinate.quotient (𝓝[base.quotientDomain] s.val.val) -
          liminf (F.realPresentation n).coordinate.quotient (𝓝[base.quotientDomain] s.val.val)) ^ 2) ≤ _
    change (F.realPresentation n).coordinate.quotient = b.coordinate.quotient at hqq
    simpa only [hpq, hqq] using hn

end SelectedMixedModels
end CircleDomainRigidity

end

end OAI

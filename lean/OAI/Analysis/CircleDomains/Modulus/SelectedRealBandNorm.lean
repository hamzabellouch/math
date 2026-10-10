import OAI.Analysis.CircleDomains.Selection.SelectedMixedSmallness
import OAI.Analysis.CircleDomains.Modulus.BandBudgetNorm

namespace OAI

/-! Exact retained quotient functions give the actual band-norm bound in
the common countable model, even after re-enumeration and added marks. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
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
  {I : Type*} [LinearOrder I] {D : I → SelectableMaskedCoordinate base π}
  {presentation : ∀ l, SelectedLevelPresentation hsch base π (D l).coordinate}
  {B₀ : Set base.dust}

 theorem retains_real_band_norm
    (F : SelectedMixedModels hsch base hU hdense π he hB D presentation B₀)
    (l : I) (P : RealCoordinatePresentation base π (D l).coordinate)
    (hP : presentation l = Sum.inl P)
    (w : Sphere → ℝ≥0∞) (hw : (∑' x, w x ^ 2) < ∞)
    (hband : ∀ x ∈ base.dust, ENNReal.ofReal
      (limsup P.coordinate.quotient (𝓝[base.quotientDomain] x) -
        liminf P.coordinate.quotient (𝓝[base.quotientDomain] x)) ≤ w x) :
    ∃ n, F.realCoordinates.physical n = P.coordinate.physical ∧
      Real.sqrt (∑' s, (F.realCoordinates.upper n s - F.realCoordinates.lower n s) ^ 2) ≤
        (countingSquareNorm w).toReal := by
  obtain ⟨n, _, hphysical, hquotient⟩ := F.retains_real_presentation l P hP
  refine ⟨n, hphysical, ?_⟩
  apply real_square_norm_le_counting _ w (fun s : F.marks => s.val.val)
    (Subtype.val_injective.comp Subtype.val_injective)
    (F.realCoordinates.width_nonneg n) _ hw
  intro s
  change ENNReal.ofReal
    (limsup (F.realPresentation n).coordinate.quotient (𝓝[base.quotientDomain] s.val.val) -
      liminf (F.realPresentation n).coordinate.quotient (𝓝[base.quotientDomain] s.val.val)) ≤ _
  change (F.realPresentation n).coordinate.quotient = P.coordinate.quotient at hquotient
  rw [hquotient]
  exact hband s.val.val s.val.property

end SelectedMixedModels
end CircleDomainRigidity

end

end OAI

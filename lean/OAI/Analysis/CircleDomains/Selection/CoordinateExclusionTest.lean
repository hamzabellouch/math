import OAI.Analysis.CircleDomains.Selection.RealExclusionWitness
import OAI.Analysis.CircleDomains.Selection.SelectedMixedSizedMeanExclusion

namespace OAI

/-! Real and mean tests use one common map--disk--radius space. The mark
index is kept discrete, so each selected test retains the component it excludes. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

structure MeanExclusionTest (hsch : PlanarSchoenflies) (base : PathCodeData Sphere Sphere)
    (π : Sphere → Sphere)
    (C : MaskedCoordinateData base.physicalDomain base.quotientDomain π
      (fun x : base.dust => x.val)) (p : base.dust) (B : ℝ) where
  presentation : MeanCoordinatePresentation hsch base π C
  function : ℂ → ℂ
  continuousOn : ContinuousOn function (((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain)
  center : ℂ
  radius : ℝ≥0
  budgetRadius : ℝ
  witness : MeanExclusionWitness C function continuousOn center radius budgetRadius
  singular : C.singular = p
  source_bound : ∀ z ∈ frontier (jordanInterior witness.disk), ‖z‖ ≤ 4 * B

structure CoordinateExclusionTest (hsch : PlanarSchoenflies) (base : PathCodeData Sphere Sphere)
    (π : Sphere → Sphere) (B₀ : Set base.dust) (B : ℝ) where
  mark : B₀
  coordinate : SelectableMaskedCoordinate base π
  witness : Sum (RealExclusionWitness base π coordinate.coordinate)
    (MeanExclusionTest hsch base π coordinate.coordinate mark.val B)

namespace CoordinateExclusionTest
variable {hsch : PlanarSchoenflies} {base : PathCodeData Sphere Sphere}
  {π : Sphere → Sphere} {B₀ : Set base.dust} {B : ℝ}
  (T : CoordinateExclusionTest hsch base π B₀ B)

 def presentation : SelectedLevelPresentation hsch base π T.coordinate.coordinate :=
  T.witness.elim (fun W => Sum.inl W.presentation) (fun W => Sum.inr W.presentation)

 def neighborhood : Set (B₀ × (MapDiskData base.physicalDomain × ℝ)) :=
    {T.mark} ×ˢ T.witness.elim (fun W => W.sizedNeighborhood)
      (fun W => W.witness.sizedNeighborhood B)

 theorem isOpen_neighborhood [TopologicalSpace B₀] [DiscreteTopology B₀] :
    IsOpen T.neighborhood := by
  change IsOpen ({T.mark} ×ˢ _)
  apply IsOpen.prod (isOpen_discrete _)
  cases h : T.witness with
  | inl W => exact W.isOpen_sizedNeighborhood
  | inr W => exact W.witness.isOpen_sizedNeighborhood B

 theorem excludes_retained
    {hU : IsOpen base.quotientDomain} {hdense : Dense base.quotientDomain}
    {he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val}
    {hB : base.dust = π '' base.physicalDomainᶜ}
    {I : Type*} [LinearOrder I] {D : I → SelectableMaskedCoordinate base π}
    {pres : ∀ l, SelectedLevelPresentation hsch base π (D l).coordinate}
    (F : SelectedMixedModels hsch base hU hdense π he hB D pres B₀)
    (A : AssignedMixedModelLimit F.model)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen base.physicalDomain) (hinf : OnePoint.infty ∈ base.physicalDomain)
    (hπ : Continuous π) (hclosed : IsClosedMap π)
    (l : I) (hD : D l = T.coordinate) (hpres : HEq (pres l) T.presentation) :
    (T.mark, (finiteSourceMap A.function A.continuousOn,
      A.center ⟨T.mark.val, F.mandatory T.mark.property⟩,
      (⟨A.radius ⟨T.mark.val, F.mandatory T.mark.property⟩,
        (A.bounds _).2.1⟩ : ℝ≥0)), F.model.real.radius) ∉ T.neighborhood := by
  rcases T with ⟨p, c, W⟩
  dsimp only at hD
  cases hD
  cases W with
  | inl W =>
    have hp : pres l = Sum.inl W.presentation := eq_of_heq hpres
    exact fun hx => F.excludes_retained_sized_real A hG l W hp _ _ hx.2
  | inr W =>
    have hs : (D l).coordinate.singular = p.val := W.singular
    have hidx : (⟨(D l).coordinate.singular, F.singular l⟩ : F.marks) =
        ⟨p.val, F.mandatory p.property⟩ := Subtype.ext hs
    have hn := F.excludes_retained_sized_mean hgreen harea A hG hinf hπ hclosed l
      W.witness B W.source_bound
    rw [hidx] at hn
    exact fun hx => hn hx.2

end CoordinateExclusionTest
end CircleDomainRigidity

end

end OAI

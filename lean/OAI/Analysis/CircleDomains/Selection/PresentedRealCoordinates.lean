import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Transfer.RealPresentationTransfer
import OAI.Analysis.CircleDomains.Topology.PresentedMixedExhaustion
import OAI.Analysis.CircleDomains.Selection.RestrictedCoordinateMarks

namespace OAI

/-! The analytic real family for a mixed model needs no artificial natural-number ordering.
Its actual band widths and functions are obtained from the selected presentations; finite
stages retain the inherited order of the whole mixed family. -/

open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

 def realCoordinatesFromPresentations
    (base : PathCodeData Sphere Sphere) (hU : IsOpen base.quotientDomain)
    (hdense : Dense base.quotientDomain) (π : Sphere → Sphere)
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hB : base.dust = π '' base.physicalDomainᶜ)
    {L : Type*} (C : L → MaskedCoordinateData base.physicalDomain base.quotientDomain π
      (fun x : base.dust => x.val)) (ι : ℕ → L)
    (R : ∀ n, RealCoordinatePresentation base π (C (ι n)))
    (A : Set base.dust)
    (hsupport : ∀ l s, (C l).upper s - (C l).lower s ≠ 0 → s ∈ A) :
    CountableRealCoordinates base.physicalDomain π (fun s : A => s.val.val) := by
  let lo (n : ℕ) (s : Sphere) := liminf (R n).coordinate.quotient (𝓝[base.quotientDomain] s)
  let hi (n : ℕ) (s : Sphere) := limsup (R n).coordinate.quotient (𝓝[base.quotientDomain] s)
  have hunit (n : ℕ) (x : Sphere) (_ : x ∈ base.quotientDomain) :
      |(R n).coordinate.quotient x| ≤ 1 := by
    rw [abs_of_nonneg ((R n).coordinate.quotient_unit x).1]
    exact ((R n).coordinate.quotient_unit x).2
  have hclosure (x : Sphere) : x ∈ closure base.quotientDomain := by
    rw [hdense.closure_eq]; trivial
  have hnn (n : ℕ) (s : Sphere) : 0 ≤ hi n s - lo n s :=
    boundary_width_nonneg (hunit n) (hclosure s)
  have hband (n : ℕ) (s : Sphere) :
      {t : ℝ | (s, t) ∈ intervalFiberHull
        (clusterGraph base.quotientDomain (R n).coordinate.quotient)} = Icc (lo n s) (hi n s) :=
    intervalFiberHull_clusterGraph_eq_boundary_band (hunit n) (hclosure s)
  refine {
    source := base.quotientDomain
    source_open := hU
    coordinate := fun n => (R n).coordinate.quotient
    coordinate_continuous := fun n => (R n).coordinate.quotient_continuous
    bound := fun _ => 1
    coordinate_bounded := hunit
    physical := fun n => (R n).coordinate.physical
    physical_measurable := fun n => (R n).coordinate.physical_measurable
    physical_smooth := fun n => (R n).coordinate.physical_smooth
    physical_energy := fun n => (R n).coordinate.physical_energy
    source_map := ?_
    pullback := fun n => (R n).coordinate.pullback
    labels_injective := Subtype.val_injective.comp Subtype.val_injective
    labels_dust := fun s => hB ▸ s.val.property
    labels_closure := fun s => hclosure s.val.val
    lower := fun n s => lo n s.val.val
    upper := fun n s => hi n s.val.val
    width_nonneg := fun n s => hnn n s.val.val
    width_summable := ?_
    band := fun n s => hband n s.val.val
    free_trace := ?_ }
  · intro z hz
    rw [← he ⟨(z : Sphere), hz⟩]
    exact (base.domainEquiv ⟨(z : Sphere), hz⟩).property
  · intro n
    apply ((C (ι n)).width_summable.subtype (· ∈ A)).congr
    intro s
    exact congrArg (fun t : ℝ => t ^ 2) ((R n).band_width s.val)
  · intro x hx hfree n
    have hxB : x ∈ base.dust := hB.symm ▸ hx
    have hnot : (⟨x, hxB⟩ : base.dust) ∉ A := by
      intro hxA
      exact hfree ⟨⟨⟨x, hxB⟩, hxA⟩, rfl⟩
    have hwidth : (C (ι n)).upper ⟨x, hxB⟩ - (C (ι n)).lower ⟨x, hxB⟩ = 0 := by
      by_contra hn
      exact hnot (hsupport _ _ hn)
    rw [(R n).band_width] at hwidth
    change hi n x - lo n x = 0 at hwidth
    refine ⟨lo n x, ?_⟩
    rw [hband, sub_eq_zero.mp hwidth, Icc_self]

 theorem exists_mixed_exhaustion_from_presentations
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcompact : SmoothCompactMetricSphereUniformization)
    (hfinite : FiniteJordanModelUniformization)
    (base : PathCodeData Sphere Sphere) (hU : IsOpen base.quotientDomain)
    (hG : IsOpen base.physicalDomain) (hconn : IsConnected base.physicalDomain)
    (hinfty : OnePoint.infty ∈ base.physicalDomain) (hdense : Dense base.quotientDomain)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hB : base.dust = π '' base.physicalDomainᶜ)
    (hTD : IsTotallyDisconnected base.dust) (hUB : Disjoint base.quotientDomain base.dust)
    {L : Type*} [LinearOrder L] [Countable L]
    (C : L → MaskedCoordinateData base.physicalDomain base.quotientDomain π
      (fun x : base.dust => x.val)) (ι : ℕ → L) (hinj : Injective ι)
    (R : ∀ n, RealCoordinatePresentation base π (C (ι n)))
    (A : Set base.dust) [Countable A] (hsing : ∀ l, (C l).singular ∈ A)
    (hsupport : ∀ l s, (C l).upper s - (C l).lower s ≠ 0 → s ∈ A)
    (hcompat : ∀ (l : L) (n : ℕ) (labels : Fin n → L), (∀ i, labels i < l) →
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure ((π '' base.physicalDomainᶜ) \ range (fun s : A => s.val.val))
          (C l).graph (fun k => (C k).graph) labels) = 0)
    (O : ℕ → A → Set Sphere) (hO : ∀ n s, O n s ∈ 𝓝 (s.val.val))
    (ε ρ : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hρ : ∀ n, 0 < ρ n) :
    Nonempty (MixedModelExhaustion
      (realCoordinatesFromPresentations base hU hdense π he hB C ι R A hsupport)
      (fun l => (C l).restrictMarks A (hsing l) (hsupport l)) ι O ε ρ) := by
  let d := realCoordinatesFromPresentations base hU hdense π he hB C ι R A hsupport
  let R' := (realSubfamily_of_presentations C ι R hdense).restrictMarks A hsing hsupport
  apply exists_mixed_model_exhaustion_of_real_subfamily hsard hsch hcompact hfinite
    hG hconn hinfty hπ hclosed hsurj hr (hB ▸ hTD) d
    (fun x hx hxb => Set.disjoint_left.mp hUB hx (hB.symm ▸ hxb))
    (fun l => (C l).restrictMarks A (hsing l) (hsupport l)) ι hinj R'
    (fun _ => rfl) ?_ hcompat O hO ε ρ hε hρ
  intro n s
  exact (R n).band_width s.val

end CircleDomainRigidity

end

end OAI

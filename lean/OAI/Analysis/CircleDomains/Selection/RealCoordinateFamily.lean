import OAI.Analysis.CircleDomains.Transfer.CountableRealTransfer
import OAI.Analysis.CircleDomains.Selection.PhysicalRealCoordinate
import OAI.Analysis.CircleDomains.Uniformization.BandLimits
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace OAI

/-! Assemble the actual bounded physical coordinates and their square-summable
band budgets into the coordinate family consumed by finite transfer. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

omit [MeasurableSpace C(PathTime, Sphere)] in
theorem boundary_width_nonneg {U : Set Sphere} {f : Sphere → ℝ}
    (hf : ∀ x ∈ U, |f x| ≤ 1) {x : Sphere} (hx : x ∈ closure U) :
    0 ≤ limsup f (𝓝[U] x) - liminf f (𝓝[U] x) := by
  obtain ⟨t, ht⟩ := clusterGraph_fiber_nonempty_of_mem_closure hf hx
  have hm := subset_intervalFiberHull (clusterGraph U f) ht
  have he := intervalFiberHull_clusterGraph_eq_boundary_band hf hx
  have hi : t ∈ Icc (liminf f (𝓝[U] x)) (limsup f (𝓝[U] x)) := by
    rw [← he]
    exact hm
  exact sub_nonneg.mpr (hi.1.trans hi.2)

def realCoordinateDataFamily
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hdense : Dense d.quotientDomain) (π : Sphere → Sphere)
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : d.dust = π '' d.physicalDomainᶜ)
    (Q : ℕ → PhysicalRealCoordinate d π)
    (M : Set Sphere) (hMB : M ⊆ d.dust)
    (w : ℕ → Sphere → ℝ≥0∞) (hw : ∀ i, (∑' x, w i x ^ 2) < ∞)
    (hsupport : ∀ i x, x ∈ d.dust → w i x ≠ 0 → x ∈ M)
    (hbudget : ∀ i x, x ∈ d.dust →
      ENNReal.ofReal (limsup (Q i).quotient (𝓝[d.quotientDomain] x) -
        liminf (Q i).quotient (𝓝[d.quotientDomain] x)) ≤ w i x)
 :
    FiniteTransfer.CountableRealCoordinates d.physicalDomain π (fun x : M => x.val) := by
  let lo (i : ℕ) (x : Sphere) := liminf (Q i).quotient (𝓝[d.quotientDomain] x)
  let hi (i : ℕ) (x : Sphere) := limsup (Q i).quotient (𝓝[d.quotientDomain] x)
  have hunit (i : ℕ) (x : Sphere) (_ : x ∈ d.quotientDomain) : |(Q i).quotient x| ≤ 1 := by
    rw [abs_of_nonneg ((Q i).quotient_unit x).1]
    exact ((Q i).quotient_unit x).2
  have hclosure (x : Sphere) : x ∈ closure d.quotientDomain := by
    rw [hdense.closure_eq]
    trivial
  have hnn (i : ℕ) (x : Sphere) : 0 ≤ hi i x - lo i x :=
    boundary_width_nonneg (hunit i) (hclosure x)
  have hband (i : ℕ) (x : Sphere) :
      {t : ℝ | (x, t) ∈ intervalFiberHull (clusterGraph d.quotientDomain (Q i).quotient)} =
        Icc (lo i x) (hi i x) :=
    intervalFiberHull_clusterGraph_eq_boundary_band (hunit i) (hclosure x)
  have hsum (i : ℕ) : Summable (fun x : M => (hi i x.val - lo i x.val) ^ 2) := by
    have hfinite : (∑' x : M, ENNReal.ofReal ((hi i x.val - lo i x.val) ^ 2)) < ∞ := by
      calc
        _ = ∑' x : M, (ENNReal.ofReal (hi i x.val - lo i x.val)) ^ 2 := by
          congr 1
          funext x
          exact ENNReal.ofReal_pow (hnn i x.val) 2
        _ ≤ ∑' x : M, w i x.val ^ 2 :=
          ENNReal.tsum_le_tsum (fun x => pow_le_pow_left' (hbudget i x.val (hMB x.property)) 2)
        _ ≤ ∑' x, w i x ^ 2 :=
          ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective (fun x => w i x ^ 2)
        _ < ∞ := hw i
    exact (ENNReal.summable_toReal hfinite.ne).congr
      (fun x => ENNReal.toReal_ofReal (sq_nonneg _))
  refine {
    source := d.quotientDomain
    source_open := hU
    coordinate := fun i => (Q i).quotient
    coordinate_continuous := fun i => (Q i).quotient_continuous
    bound := fun _ => 1
    coordinate_bounded := hunit
    physical := fun i => (Q i).physical
    physical_measurable := fun i => (Q i).physical_measurable
    physical_smooth := fun i => (Q i).physical_smooth
    physical_energy := fun i => (Q i).physical_energy
    source_map := ?_
    pullback := fun i => (Q i).pullback
    labels_injective := Subtype.val_injective
    labels_dust := fun x => hB ▸ hMB x.property
    labels_closure := fun x => hclosure x.val
    lower := fun i x => lo i x.val
    upper := fun i x => hi i x.val
    width_nonneg := fun i x => hnn i x.val
    width_summable := hsum
    band := fun i x => hband i x.val
    free_trace := ?_ }
  · intro z hz
    rw [← he ⟨(z : Sphere), hz⟩]
    exact (d.domainEquiv ⟨(z : Sphere), hz⟩).property
  · intro x hx hfree i
    have hxB : x ∈ d.dust := hB.symm ▸ hx
    have hxM : x ∉ M := by
      intro h
      exact hfree ⟨⟨x, h⟩, rfl⟩
    have hw0 : w i x = 0 := by
      by_contra h
      exact hxM (hsupport i x hxB h)
    have hzero : hi i x - lo i x = 0 := le_antisymm
      ((ENNReal.ofReal_eq_zero.mp (le_antisymm (by simpa only [hw0] using hbudget i x hxB)
        bot_le))) (hnn i x)
    refine ⟨lo i x, ?_⟩
    rw [hband, sub_eq_zero.mp hzero, Icc_self]

def realCoordinateFamily
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hdense : Dense d.quotientDomain) (π : Sphere → Sphere)
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : d.dust = π '' d.physicalDomainᶜ)
    (Q : ℕ → PhysicalRealCoordinate d π)
    (M : Set Sphere) (hMB : M ⊆ d.dust)
    (w : ℕ → Sphere → ℝ≥0∞) (hw : ∀ i, (∑' x, w i x ^ 2) < ∞)
    (hsupport : ∀ i x, x ∈ d.dust → w i x ≠ 0 → x ∈ M)
    (hbudget : ∀ i x, x ∈ d.dust →
      ENNReal.ofReal (limsup (Q i).quotient (𝓝[d.quotientDomain] x) -
        liminf (Q i).quotient (𝓝[d.quotientDomain] x)) ≤ w i x)
    (_hcompat : ∀ (j n : ℕ) (labels : Fin n → ℕ), (∀ i, labels i < j) →
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (d.dust \ M) (circleBandGraph d.quotientDomain (Q j).quotient)
          (fun i => circleBandGraph d.quotientDomain (Q i).quotient) labels) = 0) :
    FiniteTransfer.CountableRealCoordinates d.physicalDomain π (fun x : M => x.val) :=
  realCoordinateDataFamily d hU hdense π he hB Q M hMB w hw hsupport hbudget

theorem realCoordinateFamily_naturalCompatibility
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hdense : Dense d.quotientDomain) (π : Sphere → Sphere)
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : d.dust = π '' d.physicalDomainᶜ)
    (Q : ℕ → PhysicalRealCoordinate d π)
    (M : Set Sphere) (hMB : M ⊆ d.dust)
    (w : ℕ → Sphere → ℝ≥0∞) (hw : ∀ i, (∑' x, w i x ^ 2) < ∞)
    (hsupport : ∀ i x, x ∈ d.dust → w i x ≠ 0 → x ∈ M)
    (hbudget : ∀ i x, x ∈ d.dust →
      ENNReal.ofReal (limsup (Q i).quotient (𝓝[d.quotientDomain] x) -
        liminf (Q i).quotient (𝓝[d.quotientDomain] x)) ≤ w i x)
    (hcompat : ∀ (j n : ℕ) (labels : Fin n → ℕ), (∀ i, labels i < j) →
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (d.dust \ M) (circleBandGraph d.quotientDomain (Q j).quotient)
          (fun i => circleBandGraph d.quotientDomain (Q i).quotient) labels) = 0) :
    (realCoordinateFamily d hU hdense π he hB Q M hMB w hw hsupport hbudget hcompat).NaturalCompatibility := by
  intro j n labels hlt
  have hm : range (fun x : M => x.val) = M := Subtype.range_coe_subtype
  simpa only [realCoordinateFamily, realCoordinateDataFamily, ← hB, hm] using
    hcompat j n labels hlt

end CircleDomainRigidity

end

end OAI

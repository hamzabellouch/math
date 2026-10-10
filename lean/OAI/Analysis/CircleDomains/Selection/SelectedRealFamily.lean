import OAI.Analysis.CircleDomains.Selection.GradedRealSelection
import OAI.Analysis.CircleDomains.Selection.OrderedSelectionSlots

namespace OAI

/-! Convert the selected tests into a countable family in their original
selection order. Unused slots contain the zero coordinate. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

theorem exists_selected_real_family
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hdense : Dense d.quotientDomain) (π : Sphere → Sphere)
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : d.dust = π '' d.physicalDomainᶜ) (EStar : Set Sphere)
    (A : ℕ → Set (GradedRealTest d π EStar)) (hzero : A 0 = ∅) (hone : A 1 = ∅)
    (hmono : Monotone A) (hsingle : ∀ n, (A (n + 1) \ A n).Subsingleton)
    (hnew : ∀ n b, b ∈ A (n + 1) \ A n → GradedRealTest.Allowed (A n) b) :
    ∃ c : ℕ → UngatedRealTest d π EStar, ∃ M : Set Sphere,
      M.Countable ∧ M ⊆ d.dust ∧ c 0 = UngatedRealTest.zeroTest d π EStar ∧
      (∀ i, (c i).exclusions ∩ d.dust ⊆ M) ∧
      (∀ b ∈ ⋃ n, A n, ∃ k, c k = b.toUngatedRealTest) ∧
      ∃ F : FiniteTransfer.CountableRealCoordinates d.physicalDomain π (fun x : M => x.val),
        F.source = d.quotientDomain ∧ F.NaturalCompatibility ∧
        (∀ k, F.coordinate k = (c k).coordinate.quotient ∧
          F.physical k = (c k).coordinate.physical) ∧
        ∀ k (x : M),
          F.lower k x = liminf (c k).coordinate.quotient (𝓝[d.quotientDomain] x.val) ∧
          F.upper k x = limsup (c k).coordinate.quotient (𝓝[d.quotientDomain] x.val) := by
  classical
  obtain ⟨q, hq, hpref⟩ := exists_ordered_selection_slots A hzero hmono hsingle
  let c (n : ℕ) : UngatedRealTest d π EStar :=
    (q n).elim (UngatedRealTest.zeroTest d π EStar) GradedRealTest.toUngatedRealTest
  have hc0 : c 0 = UngatedRealTest.zeroTest d π EStar := by
    cases h : q 0 with
    | none => simp [c, h]
    | some b =>
        have hb : b ∈ A 1 := ((hq 0 b).mp h).1
        rw [hone] at hb
        exact hb.elim
  let M : Set Sphere := (⋃ n, (c n).exclusions) ∩ d.dust
  have hMc : M.Countable := (countable_iUnion fun n => (c n).exclusions_countable).mono
    inter_subset_left
  have hMB : M ⊆ d.dust := inter_subset_right
  have hsupp (n : ℕ) (x : Sphere) (hx : x ∈ d.dust) (hw : (c n).weight x ≠ 0) : x ∈ M :=
    ⟨mem_iUnion.mpr ⟨n, (c n).weight_support hw⟩, hx⟩
  have hcompat (j n : ℕ) (labels : Fin n → ℕ) (hlt : ∀ i, labels i < j) :
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (d.dust \ M)
          (circleBandGraph d.quotientDomain (c j).coordinate.quotient)
          (fun i => circleBandGraph d.quotientDomain (c i).coordinate.quotient) labels) = 0 := by
    cases hj : q j with
    | none =>
        simpa only [c, hj, Option.elim_none, UngatedRealTest.zeroTest,
          PhysicalRealCoordinate.zero] using
          zero_coordinate_compatibility d.quotientDomain (d.dust \ M)
            (fun i => circleBandGraph d.quotientDomain (c i).coordinate.quotient) n labels
    | some b =>
        have hcj : c j = b.toUngatedRealTest := by simp [c, hj]
        have hb := hnew j b ((hq j b).mp hj)
        change b.toUngatedRealTest.CompatibleWith
          (insert (UngatedRealTest.zeroTest d π EStar)
            (GradedRealTest.toUngatedRealTest '' A j)) at hb
        have hprev (i : Fin n) : c (labels i) ∈
            insert (UngatedRealTest.zeroTest d π EStar)
              (GradedRealTest.toUngatedRealTest '' A j) := by
          cases hi : q (labels i) with
          | none => simp [c, hi]
          | some e =>
              have heA : e ∈ A j := (hpref j e).mpr ⟨labels i, hlt i, hi⟩
              exact Or.inr ⟨e, heA, by simp [c, hi]⟩
        have hz := hb.2 n (fun i => c (labels i)) hprev
        rw [UngatedRealTest.freeComponentFailure_congr_selected
          (d.dust \ b.exclusions) (circleBandGraph d.quotientDomain b.coordinate.quotient)
          (fun i : Fin n => circleBandGraph d.quotientDomain (c (labels i)).coordinate.quotient)
          (fun i => circleBandGraph d.quotientDomain (c i).coordinate.quotient)
          id labels (fun _ => rfl)] at hz
        rw [hcj]
        apply measure_mono_null _ hz
        rintro _ ⟨⟨x, t, θ⟩, hx, rfl⟩
        refine ⟨(x, t, θ), ⟨⟨hx.1.1, ?_⟩, hx.2⟩, rfl⟩
        intro hxb
        apply hx.1.2
        exact ⟨mem_iUnion.mpr ⟨j, hcj.symm ▸ hxb⟩, hx.1.1⟩
  let F := realCoordinateFamily d hU hdense π he hB (fun n => (c n).coordinate) M hMB
    (fun n => (c n).weight) (fun n => (c n).weight_finite) hsupp
    (fun n => (c n).band_bound) hcompat
  have hFcompat : F.NaturalCompatibility := realCoordinateFamily_naturalCompatibility
    d hU hdense π he hB (fun n => (c n).coordinate) M hMB
      (fun n => (c n).weight) (fun n => (c n).weight_finite) hsupp
      (fun n => (c n).band_bound) hcompat
  refine ⟨c, M, hMc, hMB, hc0, ?_, ?_, F, rfl, hFcompat,
    (fun _ => ⟨rfl, rfl⟩), ?_⟩
  · intro i x hx
    exact ⟨mem_iUnion.mpr ⟨i, hx.1⟩, hx.2⟩
  · intro b hb
    obtain ⟨m, hm⟩ := mem_iUnion.mp hb
    obtain ⟨k, _, hk⟩ := (hpref m b).mp hm
    exact ⟨k, by simp [c, hk]⟩
  · intro k x
    exact ⟨rfl, rfl⟩

end CircleDomainRigidity

end

end OAI

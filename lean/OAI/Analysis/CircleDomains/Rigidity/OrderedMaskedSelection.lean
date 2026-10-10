import OAI.Analysis.CircleDomains.Rigidity.SelectableMaskedCoordinate
import OAI.Analysis.CircleDomains.Selection.OrderedSelectionSlots
import OAI.Analysis.CircleDomains.Selection.ZeroRealCoordinate
import Mathlib.Data.Sum.Order

namespace OAI

/-! A selected mixed family retains the complete seed before the new
coordinates. Empty selection steps use the seed zero coordinate. The
resulting order has type omega plus omega, not a rearranged natural order. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

 def orderedSelectedCoordinates {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    (seed : ℕ → SelectableMaskedCoordinate d π) {T : Type*}
    (data : T → SelectableMaskedCoordinate d π) (q : ℕ → Option T) :
    ℕ ⊕ₗ ℕ → SelectableMaskedCoordinate d π :=
  fun j => match ofLex j with
    | .inl n => seed n
    | .inr n => (q n).elim (seed 0) data

omit [MeasurableSpace C(PathTime, Sphere)] in
 theorem freeComponentFailure_mono_free {X T I J : Type*} [TopologicalSpace X]
    {F K : Set X} (hFK : F ⊆ K) (N : Set (X × T)) (R : I → Set (X × T)) (labels : J → I) :
    freeComponentFailure F N R labels ⊆ freeComponentFailure K N R labels := by
  rintro _ ⟨⟨x, t, θ⟩, h, rfl⟩
  exact ⟨(x, t, θ), ⟨hFK h.1, h.2⟩, rfl⟩

 theorem orderedSelectedCoordinates_compatibility
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    (seed : ℕ → SelectableMaskedCoordinate d π)
    (hzero : (seed 0).coordinate.graph = circleBandGraph d.quotientDomain (fun _ => 0))
    (hseed : ∀ (j n : ℕ) (labels : Fin n → ℕ), (∀ i, labels i < j) →
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (d.dust \ ⋃ k, (seed k).flags) (seed j).coordinate.graph
          (fun k => (seed k).coordinate.graph) labels) = 0)
    {T : Type*} (data : T → SelectableMaskedCoordinate d π)
    (A : ℕ → Set T) (q : ℕ → Option T)
    (hq : ∀ n c, q n = some c ↔ c ∈ A (n + 1) \ A n)
    (hpref : ∀ n c, c ∈ A n ↔ ∃ k < n, q k = some c)
    (hnew : ∀ n c, c ∈ A (n + 1) \ A n →
      (data c).CompatibleWith (range seed ∪ data '' A n)) :
    let D := orderedSelectedCoordinates seed data q
    ∀ (j : ℕ ⊕ₗ ℕ) (n : ℕ) (labels : Fin n → ℕ ⊕ₗ ℕ),
      (∀ i, labels i < j) →
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (d.dust \ ⋃ k, (D k).flags) (D j).coordinate.graph
          (fun k => (D k).coordinate.graph) labels) = 0 := by
  let D := orderedSelectedCoordinates seed data q
  have hseedflags : (⋃ k, (seed k).flags) ⊆ ⋃ k, (D k).flags := by
    intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨Sum.inlₗ k, hk⟩
  dsimp only
  intro j n labels hlt
  change (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
    (freeComponentFailure (d.dust \ ⋃ k, (D k).flags) (D j).coordinate.graph
      (fun k => (D k).coordinate.graph) labels) = 0
  induction j using Lex.rec with
  | h j =>
    cases j with
    | inl j =>
      let inds (i : Fin n) : ℕ := (ofLex (labels i)).elim id (fun _ => 0)
      have hind (i : Fin n) : inds i < j ∧ D (labels i) = seed (inds i) := by
        cases h : ofLex (labels i) with
        | inl k =>
          have hlabel : labels i = Sum.inlₗ k := by
            simpa only [toLex_ofLex] using congrArg toLex h
          have hk : k < j := Sum.Lex.inl_lt_inl_iff.mp (by simpa only [hlabel] using hlt i)
          exact ⟨by simpa only [inds, h, Sum.elim_inl, id_eq] using hk, by simp only [D, orderedSelectedCoordinates, inds, hlabel, ofLex_toLex, Sum.elim_inl, id_eq]⟩
        | inr k =>
          have hlabel : labels i = Sum.inrₗ k := by
            simpa only [toLex_ofLex] using congrArg toLex h
          exact (Sum.Lex.not_inr_lt_inl (by simpa only [hlabel] using hlt i)).elim
      have hz := hseed j n inds (fun i => (hind i).1)
      rw [UngatedRealTest.freeComponentFailure_congr_selected
        (d.dust \ ⋃ k, (seed k).flags) (seed j).coordinate.graph
        (fun k => (seed k).coordinate.graph) (fun k => (D k).coordinate.graph)
        inds labels (fun i => congrArg (fun c => c.coordinate.graph) (hind i).2.symm)] at hz
      exact measure_mono_null (freeComponentFailure_mono_free
        (show d.dust \ (⋃ k, (D k).flags) ⊆ d.dust \ (⋃ k, (seed k).flags) from
          fun _ hx => ⟨hx.1, fun hm => hx.2 (hseedflags hm)⟩) _ _ labels) hz
    | inr j =>
      cases hj : q j with
      | none =>
        change (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
          (freeComponentFailure (d.dust \ ⋃ k, (D k).flags)
            ((q j).elim (seed 0) data).coordinate.graph (fun k => (D k).coordinate.graph) labels) = 0
        rw [hj, Option.elim_none, hzero]
        exact zero_coordinate_compatibility _ _ _ n labels
      | some b =>
        have hb := hnew j b ((hq j b).mp hj)
        have hprev (i : Fin n) : D (labels i) ∈ range seed ∪ data '' A j := by
          cases hi : ofLex (labels i) with
          | inl k =>
            have hlabel : labels i = Sum.inlₗ k := by
              simpa only [toLex_ofLex] using congrArg toLex hi
            exact Or.inl ⟨k, by simp only [D, orderedSelectedCoordinates, hlabel, ofLex_toLex]⟩
          | inr k =>
            have hlabel : labels i = Sum.inrₗ k := by
              simpa only [toLex_ofLex] using congrArg toLex hi
            have hk : k < j := Sum.Lex.inr_lt_inr_iff.mp (by simpa only [hlabel] using hlt i)
            cases hqk : q k with
            | none =>
              apply Or.inl
              exact ⟨0, by simp only [D, orderedSelectedCoordinates, hlabel, ofLex_toLex,
                hqk, Option.elim_none]⟩
            | some a =>
              apply Or.inr
              refine ⟨a, (hpref j a).mpr ⟨k, hk, hqk⟩, ?_⟩
              simp only [D, orderedSelectedCoordinates, hlabel, ofLex_toLex, hqk, Option.elim_some]
        have hz := hb.2 n (fun i => D (labels i)) hprev
        have hbf : (data b).flags ⊆ ⋃ k, (D k).flags := by
          intro x hx
          apply mem_iUnion.mpr
          refine ⟨Sum.inrₗ j, ?_⟩
          simpa only [D, orderedSelectedCoordinates, ofLex_toLex, hj, Option.elim_some] using hx
        change (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
          (freeComponentFailure (d.dust \ ⋃ k, (D k).flags)
            ((q j).elim (seed 0) data).coordinate.graph (fun k => (D k).coordinate.graph) labels) = 0
        rw [hj, Option.elim_some]
        apply measure_mono_null (freeComponentFailure_mono_free
          (show d.dust \ (⋃ k, (D k).flags) ⊆ d.dust \ (data b).flags from
            fun _ hx => ⟨hx.1, fun hm => hx.2 (hbf hm)⟩) _ _ labels)
        exact hz

 def orderedSelectedCoordinates_realSubfamily
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    (seed : ℕ → SelectableMaskedCoordinate d π) {T : Type*}
    (data : T → SelectableMaskedCoordinate d π) (q : ℕ → Option T)
    (R : RealCoordinateSubfamily (fun i => (seed i).coordinate) id) :
    RealCoordinateSubfamily
      (fun j => (orderedSelectedCoordinates seed data q j).coordinate)
      (fun i : ℕ => (Sum.inlₗ i : ℕ ⊕ₗ ℕ)) where
  physical := R.physical
  quotient := R.quotient
  bound := R.bound
  bounded := R.bounded
  full_mask := R.full_mask
  smooth := R.smooth
  energy := R.energy
  pullback := R.pullback
  projection := R.projection
  width := R.width

end CircleDomainRigidity

end

end OAI

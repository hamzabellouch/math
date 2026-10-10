import OAI.Analysis.CircleDomains.Rigidity.SeededMaskedSelection
import OAI.Analysis.CircleDomains.Selection.ExactRealSelections

namespace OAI

/-! Carry the actual real or mean presentation through the ordered selection, including
unused slots filled by the original zero coordinate. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

 def orderedSelectedPresentations
    {hsch : PlanarSchoenflies} {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    (seed : ℕ → SelectableMaskedCoordinate d π)
    (seedPresentation : ∀ n, RealCoordinatePresentation d π (seed n).coordinate)
    {T : Type*} (data : T → SelectableMaskedCoordinate d π)
    (presentation : ∀ t, SelectedLevelPresentation hsch d π (data t).coordinate)
    (q : ℕ → Option T) : ∀ j : ℕ ⊕ₗ ℕ,
      SelectedLevelPresentation hsch d π (orderedSelectedCoordinates seed data q j).coordinate := by
  intro j
  induction j using Lex.rec with
  | h j =>
    cases j with
    | inl n => exact Sum.inl (seedPresentation n)
    | inr n =>
      change SelectedLevelPresentation hsch d π ((q n).elim (seed 0) data).coordinate
      exact match q n with
        | none => Sum.inl (seedPresentation 0)
        | some t => presentation t

 theorem orderedSelectedPresentations_some
    {hsch : PlanarSchoenflies} {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    (seed : ℕ → SelectableMaskedCoordinate d π)
    (seedPresentation : ∀ n, RealCoordinatePresentation d π (seed n).coordinate)
    {T : Type*} (data : T → SelectableMaskedCoordinate d π)
    (presentation : ∀ t, SelectedLevelPresentation hsch d π (data t).coordinate)
    (q : ℕ → Option T) (n : ℕ) (t : T) (h : q n = some t) :
    HEq (orderedSelectedPresentations seed seedPresentation data presentation q (Sum.inrₗ n))
      (presentation t) := by
  simp only [orderedSelectedPresentations, Lex.rec, ofLex_toLex, orderedSelectedCoordinates]
  generalize hopt : q n = opt at *
  cases opt with
  | none => cases h
  | some t' => cases Option.some.inj h; rfl

 theorem orderedSelectedPresentations_seed
    {hsch : PlanarSchoenflies} {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    (seed : ℕ → SelectableMaskedCoordinate d π)
    (seedPresentation : ∀ n, RealCoordinatePresentation d π (seed n).coordinate)
    {T : Type*} (data : T → SelectableMaskedCoordinate d π)
    (presentation : ∀ t, SelectedLevelPresentation hsch d π (data t).coordinate)
    (q : ℕ → Option T) (n : ℕ) :
    orderedSelectedPresentations seed seedPresentation data presentation q (Sum.inlₗ n) =
      Sum.inl (seedPresentation n) := rfl

 theorem orderedSelectedPresentations_infinite_real
    {hsch : PlanarSchoenflies} {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    (seed : ℕ → SelectableMaskedCoordinate d π)
    (seedPresentation : ∀ n, RealCoordinatePresentation d π (seed n).coordinate)
    {T : Type*} (data : T → SelectableMaskedCoordinate d π)
    (presentation : ∀ t, SelectedLevelPresentation hsch d π (data t).coordinate)
    (q : ℕ → Option T) :
    {j | ∃ r, orderedSelectedPresentations seed seedPresentation data presentation q j =
      Sum.inl r}.Infinite := by
  refine infinite_real_presentations_of_seed
    (fun j => (orderedSelectedCoordinates seed data q j).coordinate)
    (orderedSelectedPresentations seed seedPresentation data presentation q)
    (fun n => (Sum.inlₗ n : ℕ ⊕ₗ ℕ))
    (fun _ _ hij => Sum.inl.inj (congrArg ofLex hij)) ?_
  intro n
  exact ⟨seedPresentation n, rfl⟩

end CircleDomainRigidity

end

end OAI

import OAI.NumberTheory.Ostmann.Construction.InitialEtaCoordinates
import OAI.NumberTheory.Ostmann.Construction.InitialEtaStatePrior
import OAI.NumberTheory.Ostmann.Construction.OffDiagonalParent

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction.InitialEta
open InitialCoordinatesTemplate

variable {giant bulk spectator : PrimeSource} {b s k : ℕ}
  {aux : AuxiliaryIndex k → PrimeSource}

def jointOutside (x : JointSample giant bulk spectator aux b s) : List ℕ :=
  spectatorList spectator (sourceEquiv giant bulk spectator aux x).1

def jointState (x : JointSample giant bulk spectator aux b s) (freq : ℤ) : State :=
  outerState (initialSources bulk aux b) (Template.initial (2*b) k) giant
    (sourceEquiv giant bulk spectator aux x).2 freq

@[simp] theorem jointOutside_length (x : JointSample giant bulk spectator aux b s) :
    (jointOutside x).length = 2*s := by
  simp only [jointOutside,spectatorList,List.length_ofFn]

theorem jointState_matches (x : JointSample giant bulk spectator aux b s) (freq : ℤ) :
    Template.Matches (Template.initial (2*b) k) (jointState x freq).small :=
  Template.assignedSlots_matches _ _ _

@[simp] theorem jointState_plus (x : JointSample giant bulk spectator aux b s) (freq : ℤ) :
    (jointState x freq).giantPlus = (x.1.1:ℕ) := rfl

@[simp] theorem jointState_minus (x : JointSample giant bulk spectator aux b s) (freq : ℤ) :
    (jointState x freq).giantMinus = (x.2.1:ℕ) := rfl

theorem jointState_small_value (x : JointSample giant bulk spectator aux b s) (freq : ℤ)
    (q : SmallShape b k) :
    ((jointState x freq).small.get (stateIndex (jointState_matches x freq) q)).value =
      tupleValues x (smallPosition q) := by
  change ((List.ofFn (fun i : Fin (Template.initial (2*b) k).length =>
    ({role := (Template.initial (2*b) k)[i].role,
      value := ((sourceEquiv giant bulk spectator aux x).2.2.2 i : ℕ),
      origin := (Template.initial (2*b) k)[i].origin} : SmallSlot))).get _).value = _
  erw [List.get_ofFn]
  change ((sourceEquiv giant bulk spectator aux x).2.2.2 (smallIndex b k q):ℕ) = _
  exact sourceEquiv_small giant bulk spectator aux x q

theorem jointOutside_value (x : JointSample giant bulk spectator aux b s)
    (h : Bool) (i : Fin s) :
    (jointOutside x).get (outsideIndex (jointOutside_length x) (h,i)) =
      ((halfAt x h).2.2.1 i : ℕ) := by
  change (List.ofFn (fun i : Fin (2*s) =>
    ((sourceEquiv giant bulk spectator aux x).1 i:ℕ))).get _ = _
  erw [List.get_ofFn]
  change ((sourceEquiv giant bulk spectator aux x).1 (halfEquiv s (h,i)):ℕ) = _
  rw [sourceEquiv_spectator]

theorem initialCoordinates_ext {b s k : ℕ} {u v : InitialCoordinates b s k}
    (hg : u.giant = v.giant) (hb : u.bulk = v.bulk) (hs : u.spectator = v.spectator)
    (ht : u.top = v.top) (hc : u.compensation = v.compensation) : u=v := by
  cases u
  cases v
  simp_all

theorem jointState_coordinates (x : JointSample giant bulk spectator aux b s) (freq : ℤ) :
    coordinates (jointState_matches x freq) (jointOutside_length x)
      (jointState x freq).giantPlus (jointState x freq).giantMinus
      (fun i => (((jointState x freq).small.get i).value:ℝ))
      (fun i => ((jointOutside x).get i:ℝ)) = jointCoordinates x := by
  apply initialCoordinates_ext
  · funext h
    cases h <;> rfl
  · funext h i
    change (((jointState x freq).small.get (stateIndex (jointState_matches x freq) (.inl (h,i)))).value:ℝ) = _
    rw [jointState_small_value]
    rfl
  · funext h i
    change (((jointOutside x).get (outsideIndex (jointOutside_length x) (h,i))):ℝ) = _
    rw [jointOutside_value]
    rfl
  · funext h i
    change (((jointState x freq).small.get (stateIndex (jointState_matches x freq) (.inr (.inl (h,i))))).value:ℝ) = _
    rw [jointState_small_value]
    rfl
  · funext h j i
    change (((jointState x freq).small.get (stateIndex (jointState_matches x freq) (.inr (.inr (j,(h,i)))))).value:ℝ) = _
    rw [jointState_small_value]
    rfl

theorem jointState_bins (x : JointSample giant bulk spectator aux b s) (freq tb td : ℤ) :
    Arithmetic.sourceStateBins b s tb td (jointOutside x) (jointState x freq) = tupleBins tb td x := by
  rw [←coordinates_sourceStateBins (jointState_matches x freq) (jointOutside_length x)
    (jointState x freq).giantPlus (jointState x freq).giantMinus]
  rw [jointState_coordinates,jointCoordinates_bins]

theorem jointState_prime (x : JointSample giant bulk spectator aux b s) (freq : ℤ) :
    ∀q∈(jointState x freq).values ++ jointOutside x, q.Prime := by
  intro q hq
  simp only [State.values,List.mem_append,List.mem_cons,List.mem_map] at hq
  rcases hq with (rfl | rfl | ⟨v,hv,rfl⟩) | hq
  · exact giant.prime _ x.1.1.property
  · exact giant.prime _ x.2.1.property
  · exact assignedSlots_prime _ _ _ v hv
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    exact spectator.prime _ ((sourceEquiv giant bulk spectator aux x).1 i).property

end Ostmann.Construction.InitialEta

end

end OAI

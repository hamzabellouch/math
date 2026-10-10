import OAI.NumberTheory.Ostmann.Construction.InitialCoordinatesTemplateState
import OAI.NumberTheory.Ostmann.Construction.InitialEtaPhysical

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction.InitialEta

variable {giant bulk spectator : PrimeSource} {b s k : ℕ}
  {aux : AuxiliaryIndex k → PrimeSource}

def jointCoordinates (x : JointSample giant bulk spectator aux b s) : InitialCoordinates b s k where
  giant h := ((halfAt x h).1 : ℕ)
  bulk h i := ((halfAt x h).2.1 i : ℕ)
  spectator h i := ((halfAt x h).2.2.1 i : ℕ)
  top h i := ((halfAt x h).2.2.2 (.inl i) : ℕ)
  compensation h j i := ((halfAt x h).2.2.2 (.inr (j,i)) : ℕ)

def tuplePeriod (x : JointSample giant bulk spectator aux b s) : ℕ := ∏i,tupleValues x i

theorem tuplePeriod_pos (x : JointSample giant bulk spectator aux b s) : 0 < tuplePeriod x :=
  Finset.prod_pos (fun i _ => (tupleValues_prime x i).pos)

theorem jointCoordinates_product (x : JointSample giant bulk spectator aux b s) :
    (jointCoordinates x).product = (tuplePeriod x : ℝ) := by
  simp only [jointCoordinates,InitialCoordinates.product,tuplePeriod,
    tupleValues,tupleSample,tupleSource,halfSource,halfSample,halfAt,
    Fintype.prod_prod_type,Fintype.prod_bool,Fintype.prod_sum_type,Fintype.prod_unique,
    Bool.false_eq_true,ite_true,ite_false]
  push_cast
  ring

theorem jointCoordinates_positive (x : JointSample giant bulk spectator aux b s) :
    (jointCoordinates x).Positive := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro h
    dsimp only [jointCoordinates]
    exact_mod_cast (giant.prime _ (halfAt x h).1.property).pos
  · intro h i
    dsimp only [jointCoordinates]
    exact_mod_cast (bulk.prime _ ((halfAt x h).2.1 i).property).pos
  · intro h i
    dsimp only [jointCoordinates]
    exact_mod_cast (spectator.prime _ ((halfAt x h).2.2.1 i).property).pos
  · intro h i
    dsimp only [jointCoordinates]
    exact_mod_cast ((aux (.inl i)).prime _ ((halfAt x h).2.2.2 (.inl i)).property).pos
  · intro h j i
    dsimp only [jointCoordinates]
    exact_mod_cast ((aux (.inr (j,i))).prime _ ((halfAt x h).2.2.2 (.inr (j,i))).property).pos

theorem jointCoordinates_bins (x : JointSample giant bulk spectator aux b s) (tb td : ℤ) :
    Arithmetic.realLeafBins (jointCoordinates x) tb td = tupleBins tb td x := by
  simp only [Arithmetic.realLeafBins,jointCoordinates,tupleBins,halfBins,primeGroupLog,
    Fintype.prod_bool,halfAt,Bool.false_eq_true,ite_true,ite_false]
  ring

end Ostmann.Construction.InitialEta

end

end OAI

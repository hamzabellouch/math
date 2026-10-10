import OAI.Combinatorics.EditApproximation.AlmostLinear
import OAI.Combinatorics.EditApproximation.Specification.Footprint
import OAI.Combinatorics.EditApproximation.Definitions

/-! Concrete allocation traces preserve the cells in the certified Heap
construction while keeping its allocation-bound certificates separate. -/

namespace OAI.EditApproximation
open BitQuery
attribute [local instance] queryArityNeZero queryRoundsNeZero









def queryLocalRefinementFootprint.{u_1, u_2}
    {ι : Type u_1}
    {α : Type u_2}
    (source target : List α)
    {M : ℕ}
    (parent : TargetInterval source.length)
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (tau a eta kappa delta : BinaryFraction)
    (t : ℕ)
    (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (R : ℕ)
    (hc : ∀ (i : Fin M) (r : TargetInterval target.length), (child i r).2 ≤ R)
    (hi : ∀ (i : Fin M) (r : TargetInterval target.length), (initial i r).2 ≤ R)
    (draw : CountedCellGroupDraws M F Q)
    (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
    (parentAllocation : TargetInterval target.length → ℕ)
    (childAllocation initialAllocation : Fin M → TargetInterval target.length → ℕ)
    (drawAllocation : CountedCellGroupAllocations M F Q)
    (integerAllocation : ℕ → TargetInterval target.length → ℕ)
    (q : TargetInterval target.length)
    (readEarlier : Fin M × ℕ × TargetInterval target.length →
  BitQuery ι BinaryFraction)
    (readCurrent : Fin M × TargetInterval target.length →
  BitQuery ι BinaryFraction)
    (he : (key : Fin M × ℕ × TargetInterval target.length) → (readEarlier key).Footprint)
    (hr : (key : Fin M × TargetInterval target.length) → (readCurrent key).Footprint) : (queryLocalRefinement source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa delta
    t parentInitial child initial R hc hi draw integer q readEarlier readCurrent).Footprint :=
(BitQuery.Footprint.computeOf
      (BinaryFraction.queryEarlierInputsWithWork M parent N P F exponent t hP a parentInitial q)
      (BinaryFraction.queryEarlierInputsAllocation M parent N P F exponent t hP a parentInitial
        parentAllocation q)).bind
  (fun (earlierKeys : List (Fin M × ℕ × TargetInterval target.length)) =>
    BitQuery.collect readEarlier earlierKeys
      fun (earlierWords : List BinaryFraction) =>
      (BitQuery.compute
            (BinaryFraction.queryOnlineSelectWithWork source target parent N P F exponent H hP tau
              a eta kappa parentInitial child initial R hc hi t integer earlierKeys earlierWords q)).bind
        fun
          (onlineActions :
            List
              (BinaryBellmanAction (TargetInterval target.length)
                (Fin M × TargetInterval target.length) M)) =>
        have word : BinaryFraction × ℕ := parentInitial q;
        BitQuery.charge word.2
          ((BitQuery.compute
                (BinaryFraction.querySharedInputsWithWork M N F Q exponent eM eF hM hF parent a
                  word.1 q draw)).bind
            fun (sharedKeys : List (Fin M × TargetInterval target.length)) =>
            BitQuery.collect readCurrent sharedKeys
              fun (sharedWords : List BinaryFraction) =>
              (BitQuery.compute
                    (BinaryFraction.queryGroupSelectWithWork source target parent N P F exponent Q
                      eM eF hP hM hF tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q)).bind
                fun
                  (selectedActions :
                    List
                      (BinaryBellmanAction (TargetInterval target.length)
                        (Fin M × TargetInterval target.length) M)) =>
                (BitQuery.compute
                      (queryNeededInputsWithWork selectedActions onlineActions)).bind
                  fun (currentKeys : List (Fin M × TargetInterval target.length)) =>
                  BitQuery.collect readCurrent currentKeys
                    fun (currentWords : List BinaryFraction) =>
                    BitQuery.compute
                      (BinaryFraction.queryRefinementFinishWithWork parent N P F a delta
                        parentInitial t earlierKeys earlierWords selectedActions onlineActions currentKeys currentWords
                        q)))
  fun (earlierKeys : List (Fin M × ℕ × TargetInterval target.length)) =>
  BitQuery.Footprint.collect readEarlier he earlierKeys
    (fun (earlierWords : List BinaryFraction) =>
      (BitQuery.compute
            (BinaryFraction.queryOnlineSelectWithWork source target parent N P F exponent H hP tau
              a eta kappa parentInitial child initial R hc hi t integer earlierKeys earlierWords q)).bind
        fun
          (onlineActions :
            List
              (BinaryBellmanAction (TargetInterval target.length)
                (Fin M × TargetInterval target.length) M)) =>
        have word : BinaryFraction × ℕ := parentInitial q;
        BitQuery.charge word.2
          ((BitQuery.compute
                (BinaryFraction.querySharedInputsWithWork M N F Q exponent eM eF hM hF parent a
                  word.1 q draw)).bind
            fun (sharedKeys : List (Fin M × TargetInterval target.length)) =>
            BitQuery.collect readCurrent sharedKeys
              fun (sharedWords : List BinaryFraction) =>
              (BitQuery.compute
                    (BinaryFraction.queryGroupSelectWithWork source target parent N P F exponent Q
                      eM eF hP hM hF tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q)).bind
                fun
                  (selectedActions :
                    List
                      (BinaryBellmanAction (TargetInterval target.length)
                        (Fin M × TargetInterval target.length) M)) =>
                (BitQuery.compute
                      (queryNeededInputsWithWork selectedActions onlineActions)).bind
                  fun (currentKeys : List (Fin M × TargetInterval target.length)) =>
                  BitQuery.collect readCurrent currentKeys
                    fun (currentWords : List BinaryFraction) =>
                    BitQuery.compute
                      (BinaryFraction.queryRefinementFinishWithWork parent N P F a delta
                        parentInitial t earlierKeys earlierWords selectedActions onlineActions currentKeys currentWords
                        q)))
    fun (earlierWords : List BinaryFraction) =>
    (BitQuery.Footprint.compute
          (BinaryFraction.queryOnlineSelectWithWork source target parent N P F exponent H hP tau a
            eta kappa parentInitial child initial R hc hi t integer earlierKeys earlierWords q)
          (BinaryFraction.queryOnlineSelectAllocation source target parent N P F exponent H hP tau
            a eta kappa parentInitial child initial R hc hi parentAllocation childAllocation initialAllocation t integer
            integerAllocation earlierKeys earlierWords q)).bind
      (fun
          (onlineActions :
            List
              (BinaryBellmanAction (TargetInterval target.length)
                (Fin M × TargetInterval target.length) M)) =>
        have word : BinaryFraction × ℕ := parentInitial q;
        BitQuery.charge word.2
          ((BitQuery.compute
                (BinaryFraction.querySharedInputsWithWork M N F Q exponent eM eF hM hF parent a
                  word.1 q draw)).bind
            fun (sharedKeys : List (Fin M × TargetInterval target.length)) =>
            BitQuery.collect readCurrent sharedKeys
              fun (sharedWords : List BinaryFraction) =>
              (BitQuery.compute
                    (BinaryFraction.queryGroupSelectWithWork source target parent N P F exponent Q
                      eM eF hP hM hF tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q)).bind
                fun
                  (selectedActions :
                    List
                      (BinaryBellmanAction (TargetInterval target.length)
                        (Fin M × TargetInterval target.length) M)) =>
                (BitQuery.compute
                      (queryNeededInputsWithWork selectedActions onlineActions)).bind
                  fun (currentKeys : List (Fin M × TargetInterval target.length)) =>
                  BitQuery.collect readCurrent currentKeys
                    fun (currentWords : List BinaryFraction) =>
                    BitQuery.compute
                      (BinaryFraction.queryRefinementFinishWithWork parent N P F a delta
                        parentInitial t earlierKeys earlierWords selectedActions onlineActions currentKeys currentWords
                        q)))
      fun
        (online :
          List
            (BinaryBellmanAction (TargetInterval target.length)
              (Fin M × TargetInterval target.length) M)) =>
      BitQuery.Footprint.chargeOf (parentAllocation q)
        ((BitQuery.Footprint.computeOf
              (BinaryFraction.querySharedInputsWithWork M N F Q exponent eM eF hM hF parent a
                (parentInitial q).1 q draw)
              (BinaryFraction.querySharedInputsAllocation M N F Q exponent eM eF hM hF parent a
                (parentInitial q).1 q draw drawAllocation)).bind
          (fun (sharedKeys : List (Fin M × TargetInterval target.length)) =>
            BitQuery.collect readCurrent sharedKeys
              fun (sharedWords : List BinaryFraction) =>
              (BitQuery.compute
                    (BinaryFraction.queryGroupSelectWithWork source target parent N P F exponent Q
                      eM eF hP hM hF tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q)).bind
                fun
                  (selectedActions :
                    List
                      (BinaryBellmanAction (TargetInterval target.length)
                        (Fin M × TargetInterval target.length) M)) =>
                (BitQuery.compute
                      (queryNeededInputsWithWork selectedActions online)).bind
                  fun (currentKeys : List (Fin M × TargetInterval target.length)) =>
                  BitQuery.collect readCurrent currentKeys
                    fun (currentWords : List BinaryFraction) =>
                    BitQuery.compute
                      (BinaryFraction.queryRefinementFinishWithWork parent N P F a delta
                        parentInitial t earlierKeys earlierWords selectedActions online currentKeys currentWords q))
          fun (sharedKeys : List (Fin M × TargetInterval target.length)) =>
          BitQuery.Footprint.collect readCurrent hr sharedKeys
            (fun (sharedWords : List BinaryFraction) =>
              (BitQuery.compute
                    (BinaryFraction.queryGroupSelectWithWork source target parent N P F exponent Q
                      eM eF hP hM hF tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q)).bind
                fun
                  (selectedActions :
                    List
                      (BinaryBellmanAction (TargetInterval target.length)
                        (Fin M × TargetInterval target.length) M)) =>
                (BitQuery.compute
                      (queryNeededInputsWithWork selectedActions online)).bind
                  fun (currentKeys : List (Fin M × TargetInterval target.length)) =>
                  BitQuery.collect readCurrent currentKeys
                    fun (currentWords : List BinaryFraction) =>
                    BitQuery.compute
                      (BinaryFraction.queryRefinementFinishWithWork parent N P F a delta
                        parentInitial t earlierKeys earlierWords selectedActions online currentKeys currentWords q))
            fun (sharedWords : List BinaryFraction) =>
            (BitQuery.Footprint.computeOf
                  (BinaryFraction.queryGroupSelectWithWork source target parent N P F exponent Q
                    eM eF hP hM hF tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q)
                  (BinaryFraction.queryGroupSelectAllocation source target parent N P F exponent Q
                    eM eF hP hM hF tau a parentInitial child initial R hc hi parentAllocation childAllocation
                    initialAllocation draw drawAllocation sharedKeys sharedWords q)).bind
              (fun
                  (selectedActions :
                    List
                      (BinaryBellmanAction (TargetInterval target.length)
                        (Fin M × TargetInterval target.length) M)) =>
                (BitQuery.compute
                      (queryNeededInputsWithWork selectedActions online)).bind
                  fun (currentKeys : List (Fin M × TargetInterval target.length)) =>
                  BitQuery.collect readCurrent currentKeys
                    fun (currentWords : List BinaryFraction) =>
                    BitQuery.compute
                      (BinaryFraction.queryRefinementFinishWithWork parent N P F a delta
                        parentInitial t earlierKeys earlierWords selectedActions online currentKeys currentWords q))
              fun
                (groups :
                  List
                    (BinaryBellmanAction (TargetInterval target.length)
                      (Fin M × TargetInterval target.length) M)) =>
              (BitQuery.Footprint.computeOf
                    (queryNeededInputsWithWork groups online)
                    (queryNeededInputsAllocation groups online)).bind
                (fun (currentKeys : List (Fin M × TargetInterval target.length)) =>
                  BitQuery.collect readCurrent currentKeys
                    fun (currentWords : List BinaryFraction) =>
                    BitQuery.compute
                      (BinaryFraction.queryRefinementFinishWithWork parent N P F a delta
                        parentInitial t earlierKeys earlierWords groups online currentKeys currentWords q))
                fun (currentKeys : List (Fin M × TargetInterval target.length)) =>
                BitQuery.Footprint.collect readCurrent hr currentKeys
                  (fun (currentWords : List BinaryFraction) =>
                    BitQuery.compute
                      (BinaryFraction.queryRefinementFinishWithWork parent N P F a delta
                        parentInitial t earlierKeys earlierWords groups online currentKeys currentWords q))
                  fun (currentWords : List BinaryFraction) =>
                  BitQuery.Footprint.computeOf
                    (BinaryFraction.queryRefinementFinishWithWork parent N P F a delta
                      parentInitial t earlierKeys earlierWords groups online currentKeys currentWords q)
                    (BinaryFraction.queryRefinementFinishAllocation parent N P F a delta
                      parentInitial parentAllocation t earlierKeys earlierWords groups online currentKeys currentWords
                      q))

def queryLocalRandomSourcesFootprint.{u_1, u_2}
    {ι : Type u_1}
    {α : Type u_2}
    (source target : List α)
    {M : ℕ}
    [NeZero M]
    (parent : TargetInterval source.length)
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (tau a eta kappa delta : BinaryFraction)
    (t : ℕ)
    (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (R : ℕ)
    (hc : ∀ (i : Fin M) (r : TargetInterval target.length), (child i r).2 ≤ R)
    (hi : ∀ (i : Fin M) (r : TargetInterval target.length), (initial i r).2 ≤ R)
    (parentAllocation : TargetInterval target.length → ℕ)
    (childAllocation initialAllocation : Fin M → TargetInterval target.length → ℕ)
    (q : TargetInterval target.length)
    (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
    (readInteger : ℕ × TargetInterval target.length →
  ℕ → BitQuery ι BinaryFraction)
    (readEarlier : Fin M × ℕ × TargetInterval target.length →
  BitQuery ι BinaryFraction)
    (readCurrent : Fin M × TargetInterval target.length →
  BitQuery ι BinaryFraction)
    (hg : (key : GroupScalarKey M F Q) → (readGroup key).Footprint)
    (hz : (key : ℕ × TargetInterval target.length) → (range : ℕ) → (readInteger key range).Footprint)
    (he : (key : Fin M × ℕ × TargetInterval target.length) → (readEarlier key).Footprint)
    (hr : (key : Fin M × TargetInterval target.length) → (readCurrent key).Footprint) : (queryLocalRandomSources source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa
    delta t parentInitial child initial R hc hi q readGroup readInteger readEarlier readCurrent).Footprint :=
queryGroupSourceGatherFootprint M N F Q exponent eM eF hM hF a parentInitial parentAllocation q
  readGroup hg
  (fun (groupKeys : List (GroupScalarKey M F Q))
      (groupWords : List BinaryFraction) =>
    queryOnlineSourceGather parent N P F exponent H hP tau a parentInitial child q readInteger
      fun (onlineKeys : List (ℕ × TargetInterval target.length))
        (onlineWords : List BinaryFraction) =>
      queryLocalRefinement source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa
        delta t parentInitial child initial R hc hi
        (BinaryFraction.queryGroupDrawReadWithWork groupKeys groupWords)
        (BinaryFraction.queryOnlineIntegerReadWithWork onlineKeys onlineWords) q readEarlier
        readCurrent)
  fun (groupKeys : List (GroupScalarKey M F Q))
    (groupWords : List BinaryFraction) =>
  queryOnlineSourceGatherFootprint parent N P F exponent H hP tau a parentInitial parentAllocation
    child childAllocation q readInteger hz
    (fun (onlineKeys : List (ℕ × TargetInterval target.length))
        (onlineWords : List BinaryFraction) =>
      queryLocalRefinement source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa
        delta t parentInitial child initial R hc hi
        (BinaryFraction.queryGroupDrawReadWithWork groupKeys groupWords)
        (BinaryFraction.queryOnlineIntegerReadWithWork onlineKeys onlineWords) q readEarlier
        readCurrent)
    fun (onlineKeys : List (ℕ × TargetInterval target.length))
      (onlineWords : List BinaryFraction) =>
    queryLocalRefinementFootprint source target parent N P F exponent H Q eM eF hP hM hF tau a eta
      kappa delta t parentInitial child initial R hc hi
      (BinaryFraction.queryGroupDrawReadWithWork groupKeys groupWords)
      (BinaryFraction.queryOnlineIntegerReadWithWork onlineKeys onlineWords) parentAllocation
      childAllocation initialAllocation
      (BinaryFraction.queryGroupDrawReadAllocation groupKeys groupWords)
      (BinaryFraction.queryOnlineIntegerReadAllocation onlineKeys onlineWords) q readEarlier
      readCurrent he hr

def queryLocalBandFootprint.{u_1, u_2}
    {ι : Type u_1}
    {α : Type u_2}
    (source target : List α)
    {M : ℕ}
    [NeZero M]
    (parent : TargetInterval source.length)
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (tau a eta kappa delta : BinaryFraction)
    (t : ℕ)
    (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
    (parentAllocation : TargetInterval target.length → ℕ)
    (readMass readInitial : Fin M × TargetInterval target.length →
  BitQuery ι BinaryFraction)
    (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
    (readInteger : ℕ × TargetInterval target.length →
  ℕ → BitQuery ι BinaryFraction)
    (q : TargetInterval target.length)
    (readEarlier : Fin M × ℕ × TargetInterval target.length →
  BitQuery ι BinaryFraction)
    (readCurrent : Fin M × TargetInterval target.length →
  BitQuery ι BinaryFraction)
    (hm : (key : Fin M × TargetInterval target.length) → (readMass key).Footprint)
    (hi : (key : Fin M × TargetInterval target.length) → (readInitial key).Footprint)
    (hg : (key : GroupScalarKey M F Q) → (readGroup key).Footprint)
    (hz : (key : ℕ × TargetInterval target.length) → (range : ℕ) → (readInteger key range).Footprint)
    (he : (key : Fin M × ℕ × TargetInterval target.length) → (readEarlier key).Footprint)
    (hr : (key : Fin M × TargetInterval target.length) → (readCurrent key).Footprint) : (queryLocalBand source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa delta t
    parentInitial readMass readInitial readGroup readInteger q readEarlier readCurrent).Footprint :=
queryBandGatherFootprint M parent N P F exponent hP a parentInitial parentAllocation q readMass
  readInitial hm hi
  (fun (keys : List (Fin M × TargetInterval target.length))
      (massWords initialWords : List BinaryFraction) =>
    queryLocalRandomSources source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa
      delta t parentInitial (BinaryFraction.queryChildReadWithWork keys massWords)
      (BinaryFraction.queryChildReadWithWork keys initialWords)
      (BinaryFraction.queryDataReadBudget M target.length keys) (BinaryFraction.queryChildReadWithWork_budget keys massWords) (BinaryFraction.queryChildReadWithWork_budget keys initialWords) q readGroup
      readInteger readEarlier readCurrent)
  fun (keys : List (Fin M × TargetInterval target.length))
    (massWords initialWords : List BinaryFraction) =>
  queryLocalRandomSourcesFootprint source target parent N P F exponent H Q eM eF hP hM hF tau a
    eta kappa delta t parentInitial (BinaryFraction.queryChildReadWithWork keys massWords)
    (BinaryFraction.queryChildReadWithWork keys initialWords)
    (BinaryFraction.queryDataReadBudget M target.length keys) (BinaryFraction.queryChildReadWithWork_budget keys massWords) (BinaryFraction.queryChildReadWithWork_budget keys initialWords)
    parentAllocation (BinaryFraction.queryChildReadAllocation keys massWords)
    (BinaryFraction.queryChildReadAllocation keys initialWords) q readGroup readInteger
    readEarlier readCurrent hg hz he hr

def queryLocalProgramFootprint.{u_1, u_2}
    {ι : Type u_1}
    {α : Type u_2}
    (source target : List α)
    {M : ℕ}
    [NeZero M]
    (parent : TargetInterval source.length)
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (tau a eta kappa delta : BinaryFraction)
    (t : ℕ)
    (readParent : TargetInterval target.length →
  BitQuery ι BinaryFraction)
    (readMass readInitial : Fin M × TargetInterval target.length →
  BitQuery ι BinaryFraction)
    (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
    (readInteger : ℕ × TargetInterval target.length →
  ℕ → BitQuery ι BinaryFraction)
    (q : TargetInterval target.length)
    (readEarlier : Fin M × ℕ × TargetInterval target.length →
  BitQuery ι BinaryFraction)
    (readCurrent : Fin M × TargetInterval target.length →
  BitQuery ι BinaryFraction)
    (hp : (key : TargetInterval target.length) → (readParent key).Footprint)
    (hm : (key : Fin M × TargetInterval target.length) → (readMass key).Footprint)
    (hi : (key : Fin M × TargetInterval target.length) → (readInitial key).Footprint)
    (hg : (key : GroupScalarKey M F Q) → (readGroup key).Footprint)
    (hz : (key : ℕ × TargetInterval target.length) → (range : ℕ) → (readInteger key range).Footprint)
    (he : (key : Fin M × ℕ × TargetInterval target.length) → (readEarlier key).Footprint)
    (hr : (key : Fin M × TargetInterval target.length) → (readCurrent key).Footprint) : (queryLocalProgram source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa delta t
    readParent readMass readInitial readGroup readInteger q readEarlier readCurrent).Footprint :=
queryInitialGatherFootprint N P F exponent hP a q readParent hp
  (fun (keys : List (TargetInterval target.length))
      (words : List BinaryFraction) =>
    queryLocalBand source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa delta t
      (BinaryFraction.queryParentReadWithWork keys words) readMass readInitial readGroup
      readInteger q readEarlier readCurrent)
  fun (keys : List (TargetInterval target.length))
    (words : List BinaryFraction) =>
  queryLocalBandFootprint source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa
    delta t (BinaryFraction.queryParentReadWithWork keys words)
    (BinaryFraction.queryParentReadAllocation keys words) readMass readInitial readGroup
    readInteger q readEarlier readCurrent hm hi hg hz he hr








def queryPhysicalRandomDataRequestFootprint.{u_1, u_2}
    {σ : Type u_1}
    {α : Type u_2}
    (source target : List α)
    {M J : ℕ}
    [NeZero M]
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (tau a eta kappa delta : BinaryFraction)
    (copies pass copy T S t : ℕ)
    (ht : 0 < t)
    (node : PhysicalNode M J)
    (hbelow : ↑node.fst < J)
    (readGroup : GroupScalarKey M F Q → BitQuery σ BinaryFraction)
    (readInteger : ℕ × TargetInterval target.length →
  ℕ → BitQuery σ BinaryFraction)
    (q : TargetInterval target.length)
    (hg : (key : GroupScalarKey M F Q) → (readGroup key).Footprint)
    (hz : (key : ℕ × TargetInterval target.length) → (range : ℕ) → (readInteger key range).Footprint) : (queryPhysicalRandomDataRequest source target N P F exponent H Q eM eF hP hM hF tau a eta kappa
    delta copies pass copy T S t ht node hbelow readGroup readInteger q).Footprint := by
  unfold queryPhysicalRandomDataRequest
  apply queryLocalProgramFootprint
  · intro r
    exact (queryPhysicalTableReadFootprint copies T S _ _).mapKeysWithWork _ (fun _ => 1)
  · intro input
    apply Footprint.mapKeysWithWork _ (fun _ => 1)
    apply queryMeanReadFootprint
    intro j
    exact queryPhysicalTableReadFootprint copies T S _ _
  · intro input
    exact (queryPhysicalTableReadFootprint copies T S _ _).mapKeysWithWork _ (fun _ => 1)
  · intro key
    exact (hg key).mapKeysWithWork _ (fun _ => 1)
  · intro key range
    exact (hz key range).mapKeysWithWork _ (fun _ => 1)
  · intro input
    exact (queryPhysicalEarlierReadFootprint copies pass copy T S t node hbelow q input).mapKeysWithWork _
      (fun _ => 1)
  · intro input
    exact (queryPhysicalTableReadFootprint copies T S _ _).mapKeysWithWork _ (fun _ => 1)
















def queryFamilyRefinementFootprint.{u_1}
    {α : Type u_1}
    {M J R : ℕ}
    [NeZero M]
    (source target : List α)
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (tau a eta kappa delta : BinaryFraction)
    (passes copies pass copy T S t : ℕ)
    (ht : 0 < t)
    (node : PhysicalNode M J)
    (hbelow : ↑node.fst < J)
    (time : Fin R)
    (q : TargetInterval target.length) : (queryFamilyRefinement source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta
    passes copies pass copy T S t ht node hbelow time q).Footprint :=
queryPhysicalRandomDataRequestFootprint source target N P F exponent H Q eM eF hP hM hF tau a eta
  kappa delta copies pass copy T S t ht node hbelow
  (queryFamilyGroupRead target N P F exponent H Q passes copies pass copy ⟨node, hbelow⟩ time)
  (queryFamilyOnlineRead target N P F exponent H Q passes copies pass copy ⟨node, hbelow⟩ time) q
  (queryFamilyGroupReadFootprint target N P F exponent H Q passes copies pass copy ⟨node, hbelow⟩
    time)
  (queryFamilyOnlineReadFootprint target N P F exponent H Q passes copies pass copy ⟨node, hbelow⟩
    time)

def queryFamilyActiveFootprint.{u_1}
    {α : Type u_1}
    {M J R : ℕ}
    [NeZero M]
    [NeZero R]
    (source target : List α)
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (tau a eta kappa delta : BinaryFraction)
    (T S passes copies : ℕ)
    (request : PhysicalTableRequest M J target.length)
    (hindex : T < request.index)
    (hbelow : ↑request.node.fst < J) : (queryFamilyActive (R := R) source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta T S
    passes copies request hindex hbelow).Footprint :=
  (queryFamilyRefinementFootprint source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta
    passes copies request.pass request.copy T S (request.index - T) (Nat.sub_pos_of_lt hindex)
    request.node hbelow (Fin.ofNat R (request.index - T - 1)) request.state).mapKeysWithWork _ (fun _ => 1)

def queryFamilyBoundedActiveFootprint.{u_1}
    {α : Type u_1}
    {M J R : ℕ}
    [NeZero M]
    [NeZero R]
    (source target : List α)
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (tau a eta kappa delta : BinaryFraction)
    (T S passes copies : ℕ)
    (parent : { r : PhysicalTableRequest M J target.length //
  PhysicalTableRequest.Bounded (passes + 1) copies T S r })
    (hindex : T < parent.val.index)
    (hbelow : ↑parent.val.node.fst < J) : (queryFamilyBoundedActive (R := R) source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta T
    S passes copies parent hindex hbelow).Footprint :=
  queryRestrictPhysicalBodyFootprint (passes + 1) copies T S parent _
    (queryFamilyActiveFootprint (R := R) source target N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta T S passes copies parent.val hindex hbelow)
















def queryChargedFamilyTableFootprint
    {M J R passes copies T S : ℕ}
    [NeZero M]
    [NeZero R]
    (source target : List ℕ)
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (A a : ℕ → BinaryFraction)
    (tau eta kappa delta : BinaryFraction)
    (multiplier : ℕ → ℕ)
    (occurrence : BinaryMemo PositionCounts)
    (symbolBits positionBits : ℕ)
    (parent : { r : PhysicalTableRequest M J target.length //
  PhysicalTableRequest.Bounded (passes + 1) copies T S r }) : (queryChargedFamilyTable (R := R) source target N P F exponent H Q eM eF hP hM hF A a tau eta kappa delta
    multiplier occurrence symbolBits positionBits parent).Footprint := by
  have hinit := queryPhysicalInitialFootprint source target N P F (A parent.val.pass) (a parent.val.pass)
    multiplier parent occurrence symbolBits positionBits parent.val.state
  unfold queryChargedFamilyTable
  refine BitQuery.Footprint.chargeOf (naturalWordLEAllocation parent.val.index.bits T.bits) ?_
  split
  · exact (queryChargedWarmupFootprint source target N P F (A parent.val.pass) (a parent.val.pass)
      multiplier parent occurrence symbolBits positionBits).mapKeysWithWork _ (fun _ => 1)
  · refine BitQuery.Footprint.chargeOf (parent.val.node.1.val.bits.length + J.bits.length) ?_
    split
    · let interval := physicalSourceInterval source.length parent.val.node
      refine BitQuery.Footprint.chargeOf (saturatingSubtractAllocation interval.hi interval.lo +
        naturalWordLEAllocation (saturatingSubtractWithWork interval.hi interval.lo).1 [true]) ?_
      split
      · exact hinit.mapKeysWithWork _ (fun _ => 1)
      · exact (queryFamilyBoundedActiveFootprint (R := R) source target N P F exponent H Q eM eF hP hM hF
          tau (a parent.val.pass) eta kappa delta T S passes copies parent _ _).mapKeysWithWork _
          (fun _ => 1)
    · exact hinit.mapKeysWithWork _ (fun _ => 1)


def queryChargedFamilyGlobalFootprint
    {M J R passes copies T S : ℕ}
    [NeZero M]
    [NeZero R]
    (source target : List ℕ)
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (A a : ℕ → BinaryFraction)
    (tau eta kappa delta : BinaryFraction)
    (multiplier : ℕ → ℕ)
    (occurrence : BinaryMemo PositionCounts)
    (symbolBits positionBits : ℕ)
    (coarse : PhysicalEntry M J target.length → BinaryFraction × ℕ)
    (allocation : PhysicalEntry M J target.length → ℕ)
    (request : ChargedPhysicalRequest M J target.length (passes + 1) copies T S) : (queryChargedFamilyGlobal (R := R) source target N P F exponent H Q eM eF hP hM hF A a tau eta kappa delta
    multiplier occurrence symbolBits positionBits coarse request).Footprint := by
  cases request with
  | inl entry => exact Footprint.compute (coarse entry) (allocation entry)
  | inr parent =>
    exact queryChargedFamilyTableFootprint (R := R) source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits parent

def queryFamilyMemoRawFootprint
    {M J R passes copies T S : ℕ}
    [NeZero M]
    [NeZero R]
    (source target : List ℕ)
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (A a : ℕ → BinaryFraction)
    (tau eta kappa delta : BinaryFraction)
    (multiplier : ℕ → ℕ)
    (occurrence : BinaryMemo PositionCounts)
    (symbolBits positionBits : ℕ)
    (coarse : PhysicalEntry M J target.length → BinaryFraction × ℕ)
    (allocation : PhysicalEntry M J target.length → ℕ)
    (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R) target N P F exponent H Q passes copies)
    (key : QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q) : (queryFamilyMemoRaw (R := R) source target N P F exponent H Q eM eF hP hM hF A a tau eta kappa delta
    multiplier occurrence symbolBits positionBits coarse draw key).Footprint := by
  cases key with
  | inl scalar =>
    exact Footprint.computeOf (queryFamilySourceWordWithWork target N P F exponent H Q draw scalar)
      (Nat.size (draw scalar).val + 2)
  | inr request =>
    exact (queryChargedFamilyGlobalFootprint source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse allocation request).mapKeysWithWork
        _ (fun _ => 1)

def computedQueryMemoRawFootprint
    (source target : List ℕ)
    (N : ℕ)
    (occurrence : BinaryMemo PositionCounts)
    (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N)
    (key : ComputedFamilyMemoKey source target N) : (computedQueryMemoRaw source target N occurrence symbolBits positionBits input key).Footprint :=
  queryFamilyMemoRawFootprint source target N (integerParameters N).P (inputSmallLog N)
    (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
    (heightExponent N / 20) (smallLogExponent N) (computedParameterP_pos N) rfl rfl
    (fun pass => (scheduledSeedWordWithWork N pass).1)
    (fun pass => (computedQueryParameters N pass).factor)
    (computedQueryParameters N 0).tau (computedQueryParameters N 0).eta
    (computedQueryParameters N 0).kappa (computedQueryParameters N 0).delta
    (scheduledSeedMultiplier N) occurrence symbolBits positionBits
    (fun entry => (BinaryFraction.nat (clampedSeedNat input.1 entry), 0))
    (fun _ => 0) input.2 key

def computedQueryMemoFootprint
    (source target : List ℕ)
    (N : ℕ)
    (occurrence : BinaryMemo PositionCounts)
    (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N)
    (key : ComputedFamilyMemoKey source target N) : (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input
    key).Footprint :=
(computedQueryMemoRawFootprint source target N occurrence symbolBits positionBits input
      key).normalize
  (computedQueryBase N) (computedQueryBase_pos N)
  (queryFamilyMemoRemaining target N (integerParameters N).P
    (inputSmallLog N) (40 * smallLogExponent N)
    (inputHeight N) (inputSmallLog N ^ 80) key)

end OAI.EditApproximation

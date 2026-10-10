import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeColex
import OAI.Combinatorics.MatchingCount.Machines.TreeFiniteCollections

namespace OAI

open MatchingFPRAS.TreeTyped

macro "tree_cost" : tactic => `(tactic|
  (with_reducible repeat' (first
    | assumption
    | exact polynomial_identity
    | exact polynomial_first
    | exact polynomial_second
    | exact polynomial_boolAnd
    | exact polynomial_boolOr
    | exact polynomial_boolNot
    | exact polynomial_add
    | exact polynomial_subtract
    | exact polynomial_multiply
    | exact polynomial_less
    | exact polynomial_leNat
    | exact polynomial_natEqual
    | exact polynomial_finsetList
    | exact polynomial_finsetCard
    | exact polynomial_finsetSingleton
    | exact polynomial_listCons
    | exact polynomial_listLength
    | exact polynomial_append
    | exact polynomial_reverse
    | exact polynomial_flatten
    | apply polynomial_recode
    | apply polynomial_composition
    | apply polynomial_pair
    | apply polynomial_choose
    | apply polynomial_constant
    | apply polynomial_fst
    | apply polynomial_snd
    | apply polynomial_map
    | apply polynomial_mapWith
    | apply polynomial_flatMapPoly
    | apply polynomial_filter
    | apply polynomial_filterWith
    | apply polynomial_finsetBiUnion
    | apply polynomial_finsetFilter
    | apply polynomial_finsetFilterWith
    | apply polynomial_finsetImage
    | apply polynomial_finsetUnion
    | apply polynomial_finsetSDiff
    | apply polynomial_finsetInter
    | apply polynomial_finsetErase
    | apply polynomial_finsetInsert
    | apply polynomial_finsetEqual
    | apply polynomial_finsetSubset
    | apply polynomial_finsetMember
    | apply polynomial_finsetAny
    | apply polynomial_finsetAll
    | apply polynomial_pairEqual
    | apply polynomial_lexLe
    | apply polynomial_colexLe
    | apply polynomial_congr)))

end OAI

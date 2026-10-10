import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic135
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources86

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2160 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2160 (mixedVector B) = 0 := by
  have h2165 : mixedVector B (Sum.inr 2165) = Sparse.eval nodeValue2165 (mixedVector B) := by
    change mixedMoment B node2165 node2165Labels = _
    exact sound2165 B hB hF
  have h2186 : mixedVector B (Sum.inr 2186) = Sparse.eval nodeValue2186 (mixedVector B) := by
    change mixedMoment B node2186 node2186Labels = _
    exact sound2186 B hB hF
  have h3420 : mixedVector B (Sum.inr 3420) = Sparse.eval nodeValue3420 (mixedVector B) := by
    change mixedMoment B node3420 node3420Labels = _
    exact sound3420 B hB hF
  have h3457 : mixedVector B (Sum.inr 3457) = Sparse.eval nodeValue3457 (mixedVector B) := by
    change mixedMoment B node3457 node3457Labels = _
    exact sound3457 B hB hF
  have h3510 : mixedVector B (Sum.inr 3510) = Sparse.eval nodeValue3510 (mixedVector B) := by
    change mixedMoment B node3510 node3510Labels = _
    exact sound3510 B hB hF
  have h4074 : mixedVector B (Sum.inr 4074) = Sparse.eval nodeValue4074 (mixedVector B) := by
    change mixedMoment B node4074 node4074Labels = _
    exact sound4074 B hB hF
  simpa only [sourceForm2748, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2165, h2186, h3420, h3457, h3510, h4074, reducedSource2160] using sourceEq2748 B hB

theorem rowSound2160 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2160 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2160, numericCheck2160, reducedZero2160 B hB hF, mul_zero]

theorem reducedZero2161 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2161 (mixedVector B) = 0 := by
  have h2144 : mixedVector B (Sum.inr 2144) = Sparse.eval nodeValue2144 (mixedVector B) := by
    change mixedMoment B node2144 node2144Labels = _
    exact sound2144 B hB hF
  have h2146 : mixedVector B (Sum.inr 2146) = Sparse.eval nodeValue2146 (mixedVector B) := by
    change mixedMoment B node2146 node2146Labels = _
    exact sound2146 B hB hF
  have h2152 : mixedVector B (Sum.inr 2152) = Sparse.eval nodeValue2152 (mixedVector B) := by
    change mixedMoment B node2152 node2152Labels = _
    exact sound2152 B hB hF
  have h2157 : mixedVector B (Sum.inr 2157) = Sparse.eval nodeValue2157 (mixedVector B) := by
    change mixedMoment B node2157 node2157Labels = _
    exact sound2157 B hB hF
  have h2249 : mixedVector B (Sum.inr 2249) = Sparse.eval nodeValue2249 (mixedVector B) := by
    change mixedMoment B node2249 node2249Labels = _
    exact sound2249 B hB hF
  have h3591 : mixedVector B (Sum.inr 3591) = Sparse.eval nodeValue3591 (mixedVector B) := by
    change mixedMoment B node3591 node3591Labels = _
    exact sound3591 B hB hF
  have h4075 : mixedVector B (Sum.inr 4075) = Sparse.eval nodeValue4075 (mixedVector B) := by
    change mixedMoment B node4075 node4075Labels = _
    exact sound4075 B hB hF
  simpa only [sourceForm2756, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2144, h2146, h2152, h2157, h2249, h3591, h4075, reducedSource2161] using sourceEq2756 B hB

theorem rowSound2161 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2161 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2161, numericCheck2161, reducedZero2161 B hB hF, mul_zero]

theorem reducedZero2162 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2162 (mixedVector B) = 0 := by
  have h2154 : mixedVector B (Sum.inr 2154) = Sparse.eval nodeValue2154 (mixedVector B) := by
    change mixedMoment B node2154 node2154Labels = _
    exact sound2154 B hB hF
  have h2157 : mixedVector B (Sum.inr 2157) = Sparse.eval nodeValue2157 (mixedVector B) := by
    change mixedMoment B node2157 node2157Labels = _
    exact sound2157 B hB hF
  have h2158 : mixedVector B (Sum.inr 2158) = Sparse.eval nodeValue2158 (mixedVector B) := by
    change mixedMoment B node2158 node2158Labels = _
    exact sound2158 B hB hF
  have h2166 : mixedVector B (Sum.inr 2166) = Sparse.eval nodeValue2166 (mixedVector B) := by
    change mixedMoment B node2166 node2166Labels = _
    exact sound2166 B hB hF
  have h2272 : mixedVector B (Sum.inr 2272) = Sparse.eval nodeValue2272 (mixedVector B) := by
    change mixedMoment B node2272 node2272Labels = _
    exact sound2272 B hB hF
  have h3595 : mixedVector B (Sum.inr 3595) = Sparse.eval nodeValue3595 (mixedVector B) := by
    change mixedMoment B node3595 node3595Labels = _
    exact sound3595 B hB hF
  have h4075 : mixedVector B (Sum.inr 4075) = Sparse.eval nodeValue4075 (mixedVector B) := by
    change mixedMoment B node4075 node4075Labels = _
    exact sound4075 B hB hF
  simpa only [sourceForm2757, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2154, h2157, h2158, h2166, h2272, h3595, h4075, reducedSource2162] using sourceEq2757 B hB

theorem rowSound2162 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2162 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2162, numericCheck2162, reducedZero2162 B hB hF, mul_zero]

theorem reducedZero2163 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2163 (mixedVector B) = 0 := by
  have h2148 : mixedVector B (Sum.inr 2148) = Sparse.eval nodeValue2148 (mixedVector B) := by
    change mixedMoment B node2148 node2148Labels = _
    exact sound2148 B hB hF
  have h2152 : mixedVector B (Sum.inr 2152) = Sparse.eval nodeValue2152 (mixedVector B) := by
    change mixedMoment B node2152 node2152Labels = _
    exact sound2152 B hB hF
  have h2166 : mixedVector B (Sum.inr 2166) = Sparse.eval nodeValue2166 (mixedVector B) := by
    change mixedMoment B node2166 node2166Labels = _
    exact sound2166 B hB hF
  have h2257 : mixedVector B (Sum.inr 2257) = Sparse.eval nodeValue2257 (mixedVector B) := by
    change mixedMoment B node2257 node2257Labels = _
    exact sound2257 B hB hF
  have h3592 : mixedVector B (Sum.inr 3592) = Sparse.eval nodeValue3592 (mixedVector B) := by
    change mixedMoment B node3592 node3592Labels = _
    exact sound3592 B hB hF
  have h4075 : mixedVector B (Sum.inr 4075) = Sparse.eval nodeValue4075 (mixedVector B) := by
    change mixedMoment B node4075 node4075Labels = _
    exact sound4075 B hB hF
  simpa only [sourceForm2758, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2148, h2152, h2166, h2257, h3592, h4075, reducedSource2163] using sourceEq2758 B hB

theorem rowSound2163 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2163 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2163, numericCheck2163, reducedZero2163 B hB hF, mul_zero]

theorem reducedZero2164 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2164 (mixedVector B) = 0 := by
  have h2658 : mixedVector B (Sum.inr 2658) = Sparse.eval nodeValue2658 (mixedVector B) := by
    change mixedMoment B node2658 node2658Labels = _
    exact sound2658 B hB hF
  have h3406 : mixedVector B (Sum.inr 3406) = Sparse.eval nodeValue3406 (mixedVector B) := by
    change mixedMoment B node3406 node3406Labels = _
    exact sound3406 B hB hF
  have h3412 : mixedVector B (Sum.inr 3412) = Sparse.eval nodeValue3412 (mixedVector B) := by
    change mixedMoment B node3412 node3412Labels = _
    exact sound3412 B hB hF
  have h3417 : mixedVector B (Sum.inr 3417) = Sparse.eval nodeValue3417 (mixedVector B) := by
    change mixedMoment B node3417 node3417Labels = _
    exact sound3417 B hB hF
  have h3591 : mixedVector B (Sum.inr 3591) = Sparse.eval nodeValue3591 (mixedVector B) := by
    change mixedMoment B node3591 node3591Labels = _
    exact sound3591 B hB hF
  have h4075 : mixedVector B (Sum.inr 4075) = Sparse.eval nodeValue4075 (mixedVector B) := by
    change mixedMoment B node4075 node4075Labels = _
    exact sound4075 B hB hF
  simpa only [sourceForm2759, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2658, h3406, h3412, h3417, h3591, h4075, reducedSource2164] using sourceEq2759 B hB

theorem rowSound2164 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2164 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2164, numericCheck2164, reducedZero2164 B hB hF, mul_zero]

theorem reducedZero2165 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2165 (mixedVector B) = 0 := by
  have h2182 : mixedVector B (Sum.inr 2182) = Sparse.eval nodeValue2182 (mixedVector B) := by
    change mixedMoment B node2182 node2182Labels = _
    exact sound2182 B hB hF
  have h3455 : mixedVector B (Sum.inr 3455) = Sparse.eval nodeValue3455 (mixedVector B) := by
    change mixedMoment B node3455 node3455Labels = _
    exact sound3455 B hB hF
  have h4077 : mixedVector B (Sum.inr 4077) = Sparse.eval nodeValue4077 (mixedVector B) := by
    change mixedMoment B node4077 node4077Labels = _
    exact sound4077 B hB hF
  simpa only [sourceForm2766, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2182, h3455, h4077, reducedSource2165] using sourceEq2766 B hB

theorem rowSound2165 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2165 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2165, numericCheck2165, reducedZero2165 B hB hF, mul_zero]

theorem rowSound2166 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2166 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, Integer.Sparse.eval_perm reindexCheck2166, Integer.Sparse.eval_reindex]
  exact pair_row_zero B hB PairSemantics.boundaryRow0 (fun _ hH => PairSemantics.boundarySound0 hH)

theorem rowSound2167 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2167 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, Integer.Sparse.eval_perm reindexCheck2167, Integer.Sparse.eval_reindex]
  exact pair_row_zero B hB PairSemantics.boundaryRow1 (fun _ hH => PairSemantics.boundarySound1 hH)

theorem rowSound2168 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2168 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, Integer.Sparse.eval_perm reindexCheck2168, Integer.Sparse.eval_reindex]
  exact pair_row_zero B hB PairSemantics.boundaryRow2 (fun _ hH => PairSemantics.boundarySound2 hH)

theorem rowSound2169 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2169 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, Integer.Sparse.eval_perm reindexCheck2169, Integer.Sparse.eval_reindex]
  exact pair_row_zero B hB PairSemantics.boundaryRow3 (fun _ hH => PairSemantics.boundarySound3 hH)

theorem rowSound2170 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2170 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, Integer.Sparse.eval_perm reindexCheck2170, Integer.Sparse.eval_reindex]
  exact pair_row_zero B hB PairSemantics.boundaryRow4 (fun _ hH => PairSemantics.boundarySound4 hH)

theorem rowSound2171 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2171 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, Integer.Sparse.eval_perm reindexCheck2171, Integer.Sparse.eval_reindex]
  exact pair_row_zero B hB PairSemantics.boundaryRow5 (fun _ hH => PairSemantics.boundarySound5 hH)

theorem rowSound2172 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2172 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, Integer.Sparse.eval_perm reindexCheck2172, Integer.Sparse.eval_reindex]
  exact pair_row_zero B hB PairSemantics.boundaryRow6 (fun _ hH => PairSemantics.boundarySound6 hH)

theorem rowSound2173 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2173 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, Integer.Sparse.eval_perm reindexCheck2173, Integer.Sparse.eval_reindex]
  exact pair_row_zero B hB PairSemantics.boundaryRow7 (fun _ hH => PairSemantics.boundarySound7 hH)

theorem rowSound2174 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2174 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, Integer.Sparse.eval_perm reindexCheck2174, Integer.Sparse.eval_reindex]
  exact pair_row_zero B hB PairSemantics.boundaryRow8 (fun _ hH => PairSemantics.boundarySound8 hH)

theorem rowSound2175 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2175 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, Integer.Sparse.eval_perm reindexCheck2175, Integer.Sparse.eval_reindex]
  exact pair_row_zero B hB PairSemantics.boundaryRow9 (fun _ hH => PairSemantics.boundarySound9 hH)

theorem sourceRowsAt2160 : MixedData.sourceRows (2160 : Fin 2425) =
    MixedData.row2160 := by decide +kernel

theorem sourceRowsAt2161 : MixedData.sourceRows (2161 : Fin 2425) =
    MixedData.row2161 := by decide +kernel

theorem sourceRowsAt2162 : MixedData.sourceRows (2162 : Fin 2425) =
    MixedData.row2162 := by decide +kernel

theorem sourceRowsAt2163 : MixedData.sourceRows (2163 : Fin 2425) =
    MixedData.row2163 := by decide +kernel

theorem sourceRowsAt2164 : MixedData.sourceRows (2164 : Fin 2425) =
    MixedData.row2164 := by decide +kernel

theorem sourceRowsAt2165 : MixedData.sourceRows (2165 : Fin 2425) =
    MixedData.row2165 := by decide +kernel

theorem sourceRowsAt2166 : MixedData.sourceRows (2166 : Fin 2425) =
    MixedData.row2166 := by decide +kernel

theorem sourceRowsAt2167 : MixedData.sourceRows (2167 : Fin 2425) =
    MixedData.row2167 := by decide +kernel

theorem sourceRowsAt2168 : MixedData.sourceRows (2168 : Fin 2425) =
    MixedData.row2168 := by decide +kernel

theorem sourceRowsAt2169 : MixedData.sourceRows (2169 : Fin 2425) =
    MixedData.row2169 := by decide +kernel

theorem sourceRowsAt2170 : MixedData.sourceRows (2170 : Fin 2425) =
    MixedData.row2170 := by decide +kernel

theorem sourceRowsAt2171 : MixedData.sourceRows (2171 : Fin 2425) =
    MixedData.row2171 := by decide +kernel

theorem sourceRowsAt2172 : MixedData.sourceRows (2172 : Fin 2425) =
    MixedData.row2172 := by decide +kernel

theorem sourceRowsAt2173 : MixedData.sourceRows (2173 : Fin 2425) =
    MixedData.row2173 := by decide +kernel

theorem sourceRowsAt2174 : MixedData.sourceRows (2174 : Fin 2425) =
    MixedData.row2174 := by decide +kernel

theorem sourceRowsAt2175 : MixedData.sourceRows (2175 : Fin 2425) =
    MixedData.row2175 := by decide +kernel

theorem chunkSound135 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 135) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 2160 ∨ k.val = 2161 ∨ k.val = 2162 ∨ k.val = 2163 ∨ k.val = 2164 ∨ k.val = 2165 ∨ k.val = 2166 ∨ k.val = 2167 ∨ k.val = 2168 ∨ k.val = 2169 ∨ k.val = 2170 ∨ k.val = 2171 ∨ k.val = 2172 ∨ k.val = 2173 ∨ k.val = 2174 ∨ k.val = 2175 := by omega
  rcases heq with h2160 | h2161 | h2162 | h2163 | h2164 | h2165 | h2166 | h2167 | h2168 | h2169 | h2170 | h2171 | h2172 | h2173 | h2174 | h2175
  · have he : k = (2160 : Fin 2425) := Fin.ext h2160
    subst k
    rw [sourceRowsAt2160]
    exact rowSound2160 B hB hF
  · have he : k = (2161 : Fin 2425) := Fin.ext h2161
    subst k
    rw [sourceRowsAt2161]
    exact rowSound2161 B hB hF
  · have he : k = (2162 : Fin 2425) := Fin.ext h2162
    subst k
    rw [sourceRowsAt2162]
    exact rowSound2162 B hB hF
  · have he : k = (2163 : Fin 2425) := Fin.ext h2163
    subst k
    rw [sourceRowsAt2163]
    exact rowSound2163 B hB hF
  · have he : k = (2164 : Fin 2425) := Fin.ext h2164
    subst k
    rw [sourceRowsAt2164]
    exact rowSound2164 B hB hF
  · have he : k = (2165 : Fin 2425) := Fin.ext h2165
    subst k
    rw [sourceRowsAt2165]
    exact rowSound2165 B hB hF
  · have he : k = (2166 : Fin 2425) := Fin.ext h2166
    subst k
    rw [sourceRowsAt2166]
    exact rowSound2166 B hB hF
  · have he : k = (2167 : Fin 2425) := Fin.ext h2167
    subst k
    rw [sourceRowsAt2167]
    exact rowSound2167 B hB hF
  · have he : k = (2168 : Fin 2425) := Fin.ext h2168
    subst k
    rw [sourceRowsAt2168]
    exact rowSound2168 B hB hF
  · have he : k = (2169 : Fin 2425) := Fin.ext h2169
    subst k
    rw [sourceRowsAt2169]
    exact rowSound2169 B hB hF
  · have he : k = (2170 : Fin 2425) := Fin.ext h2170
    subst k
    rw [sourceRowsAt2170]
    exact rowSound2170 B hB hF
  · have he : k = (2171 : Fin 2425) := Fin.ext h2171
    subst k
    rw [sourceRowsAt2171]
    exact rowSound2171 B hB hF
  · have he : k = (2172 : Fin 2425) := Fin.ext h2172
    subst k
    rw [sourceRowsAt2172]
    exact rowSound2172 B hB hF
  · have he : k = (2173 : Fin 2425) := Fin.ext h2173
    subst k
    rw [sourceRowsAt2173]
    exact rowSound2173 B hB hF
  · have he : k = (2174 : Fin 2425) := Fin.ext h2174
    subst k
    rw [sourceRowsAt2174]
    exact rowSound2174 B hB hF
  · have he : k = (2175 : Fin 2425) := Fin.ext h2175
    subst k
    rw [sourceRowsAt2175]
    exact rowSound2175 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI

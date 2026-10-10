import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic151

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem rowSound2416 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2416 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, Integer.Sparse.eval_perm reindexCheck2416, Integer.Sparse.eval_reindex]
  exact pair_row_zero B hB PairSemantics.boundaryRow444 (fun _ hH => PairSemantics.boundarySound444 hH)

theorem rowSound2417 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2417 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, Integer.Sparse.eval_perm reindexCheck2417, Integer.Sparse.eval_reindex]
  exact pair_row_zero B hB PairSemantics.boundaryRow445 (fun _ hH => PairSemantics.boundarySound445 hH)

theorem rowSound2418 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2418 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, Integer.Sparse.eval_perm reindexCheck2418, Integer.Sparse.eval_reindex]
  exact pair_row_zero B hB PairSemantics.boundaryRow446 (fun _ hH => PairSemantics.boundarySound446 hH)

theorem rowSound2419 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2419 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, Integer.Sparse.eval_perm reindexCheck2419, Integer.Sparse.eval_reindex]
  exact pair_row_zero B hB PairSemantics.boundaryRow447 (fun _ hH => PairSemantics.boundarySound447 hH)

theorem rowSound2420 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2420 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, Integer.Sparse.eval_perm reindexCheck2420, Integer.Sparse.eval_reindex]
  exact pair_row_zero B hB PairSemantics.boundaryRow448 (fun _ hH => PairSemantics.boundarySound448 hH)

theorem rowSound2421 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2421 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, Integer.Sparse.eval_perm reindexCheck2421, Integer.Sparse.eval_reindex]
  exact pair_row_zero B hB PairSemantics.boundaryRow454 (fun _ hH => PairSemantics.boundarySound454 hH)

theorem rowSound2422 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2422 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, Integer.Sparse.eval_perm reindexCheck2422, Integer.Sparse.eval_reindex]
  exact pair_row_zero B hB PairSemantics.boundaryRow455 (fun _ hH => PairSemantics.boundarySound455 hH)

theorem rowSound2423 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2423 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, Integer.Sparse.eval_perm reindexCheck2423, Integer.Sparse.eval_reindex]
  exact pair_row_zero B hB PairSemantics.boundaryRow460 (fun _ hH => PairSemantics.boundarySound460 hH)

theorem rowSound2424 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2424 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, Integer.Sparse.eval_perm reindexCheck2424, Integer.Sparse.eval_reindex]
  exact pair_row_zero B hB PairSemantics.boundaryRow461 (fun _ hH => PairSemantics.boundarySound461 hH)

theorem sourceRowsAt2416 : MixedData.sourceRows (2416 : Fin 2425) =
    MixedData.row2416 := by decide +kernel

theorem sourceRowsAt2417 : MixedData.sourceRows (2417 : Fin 2425) =
    MixedData.row2417 := by decide +kernel

theorem sourceRowsAt2418 : MixedData.sourceRows (2418 : Fin 2425) =
    MixedData.row2418 := by decide +kernel

theorem sourceRowsAt2419 : MixedData.sourceRows (2419 : Fin 2425) =
    MixedData.row2419 := by decide +kernel

theorem sourceRowsAt2420 : MixedData.sourceRows (2420 : Fin 2425) =
    MixedData.row2420 := by decide +kernel

theorem sourceRowsAt2421 : MixedData.sourceRows (2421 : Fin 2425) =
    MixedData.row2421 := by decide +kernel

theorem sourceRowsAt2422 : MixedData.sourceRows (2422 : Fin 2425) =
    MixedData.row2422 := by decide +kernel

theorem sourceRowsAt2423 : MixedData.sourceRows (2423 : Fin 2425) =
    MixedData.row2423 := by decide +kernel

theorem sourceRowsAt2424 : MixedData.sourceRows (2424 : Fin 2425) =
    MixedData.row2424 := by decide +kernel

theorem chunkSound151 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 151) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 2416 ∨ k.val = 2417 ∨ k.val = 2418 ∨ k.val = 2419 ∨ k.val = 2420 ∨ k.val = 2421 ∨ k.val = 2422 ∨ k.val = 2423 ∨ k.val = 2424 := by omega
  rcases heq with h2416 | h2417 | h2418 | h2419 | h2420 | h2421 | h2422 | h2423 | h2424
  · have he : k = (2416 : Fin 2425) := Fin.ext h2416
    subst k
    rw [sourceRowsAt2416]
    exact rowSound2416 B hB hF
  · have he : k = (2417 : Fin 2425) := Fin.ext h2417
    subst k
    rw [sourceRowsAt2417]
    exact rowSound2417 B hB hF
  · have he : k = (2418 : Fin 2425) := Fin.ext h2418
    subst k
    rw [sourceRowsAt2418]
    exact rowSound2418 B hB hF
  · have he : k = (2419 : Fin 2425) := Fin.ext h2419
    subst k
    rw [sourceRowsAt2419]
    exact rowSound2419 B hB hF
  · have he : k = (2420 : Fin 2425) := Fin.ext h2420
    subst k
    rw [sourceRowsAt2420]
    exact rowSound2420 B hB hF
  · have he : k = (2421 : Fin 2425) := Fin.ext h2421
    subst k
    rw [sourceRowsAt2421]
    exact rowSound2421 B hB hF
  · have he : k = (2422 : Fin 2425) := Fin.ext h2422
    subst k
    rw [sourceRowsAt2422]
    exact rowSound2422 B hB hF
  · have he : k = (2423 : Fin 2425) := Fin.ext h2423
    subst k
    rw [sourceRowsAt2423]
    exact rowSound2423 B hB hF
  · have he : k = (2424 : Fin 2425) := Fin.ext h2424
    subst k
    rw [sourceRowsAt2424]
    exact rowSound2424 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI

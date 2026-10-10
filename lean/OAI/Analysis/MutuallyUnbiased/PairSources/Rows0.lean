import OAI.Analysis.MutuallyUnbiased.PairSources.Data
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Boundary0

namespace OAI

namespace MUB6.Certificate.PairSourceBridge

theorem rowCheck0 : Integer.Sparse.reindex coordinateMap (PairData.rows 0) =
    PairSemantics.boundaryRow0 := by decide +kernel

theorem rowSound0 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 0) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck0]
  exact PairSemantics.boundarySound0 hH

theorem rowCheck1 : Integer.Sparse.reindex coordinateMap (PairData.rows 1) =
    PairSemantics.boundaryRow1 := by decide +kernel

theorem rowSound1 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 1) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck1]
  exact PairSemantics.boundarySound1 hH

theorem rowCheck2 : Integer.Sparse.reindex coordinateMap (PairData.rows 2) =
    PairSemantics.boundaryRow2 := by decide +kernel

theorem rowSound2 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 2) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck2]
  exact PairSemantics.boundarySound2 hH

theorem rowCheck3 : Integer.Sparse.reindex coordinateMap (PairData.rows 3) =
    PairSemantics.boundaryRow3 := by decide +kernel

theorem rowSound3 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 3) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck3]
  exact PairSemantics.boundarySound3 hH

theorem rowCheck4 : Integer.Sparse.reindex coordinateMap (PairData.rows 4) =
    PairSemantics.boundaryRow4 := by decide +kernel

theorem rowSound4 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 4) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck4]
  exact PairSemantics.boundarySound4 hH

theorem rowCheck5 : Integer.Sparse.reindex coordinateMap (PairData.rows 5) =
    PairSemantics.boundaryRow5 := by decide +kernel

theorem rowSound5 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 5) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck5]
  exact PairSemantics.boundarySound5 hH

theorem rowCheck6 : Integer.Sparse.reindex coordinateMap (PairData.rows 6) =
    PairSemantics.boundaryRow6 := by decide +kernel

theorem rowSound6 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 6) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck6]
  exact PairSemantics.boundarySound6 hH

theorem rowCheck7 : Integer.Sparse.reindex coordinateMap (PairData.rows 7) =
    PairSemantics.boundaryRow7 := by decide +kernel

theorem rowSound7 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 7) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck7]
  exact PairSemantics.boundarySound7 hH

theorem rowCheck8 : Integer.Sparse.reindex coordinateMap (PairData.rows 8) =
    PairSemantics.boundaryRow8 := by decide +kernel

theorem rowSound8 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 8) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck8]
  exact PairSemantics.boundarySound8 hH

theorem rowCheck9 : Integer.Sparse.reindex coordinateMap (PairData.rows 9) =
    PairSemantics.boundaryRow9 := by decide +kernel

theorem rowSound9 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 9) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck9]
  exact PairSemantics.boundarySound9 hH

theorem rowCheck10 : Integer.Sparse.reindex coordinateMap (PairData.rows 10) =
    PairSemantics.boundaryRow10 := by decide +kernel

theorem rowSound10 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 10) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck10]
  exact PairSemantics.boundarySound10 hH

theorem rowCheck11 : Integer.Sparse.reindex coordinateMap (PairData.rows 11) =
    PairSemantics.boundaryRow11 := by decide +kernel

theorem rowSound11 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 11) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck11]
  exact PairSemantics.boundarySound11 hH

theorem rowCheck12 : Integer.Sparse.reindex coordinateMap (PairData.rows 12) =
    PairSemantics.boundaryRow12 := by decide +kernel

theorem rowSound12 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 12) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck12]
  exact PairSemantics.boundarySound12 hH

theorem rowCheck13 : Integer.Sparse.reindex coordinateMap (PairData.rows 13) =
    PairSemantics.boundaryRow13 := by decide +kernel

theorem rowSound13 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 13) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck13]
  exact PairSemantics.boundarySound13 hH

theorem rowCheck14 : Integer.Sparse.reindex coordinateMap (PairData.rows 14) =
    PairSemantics.boundaryRow14 := by decide +kernel

theorem rowSound14 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 14) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck14]
  exact PairSemantics.boundarySound14 hH

theorem rowCheck15 : Integer.Sparse.reindex coordinateMap (PairData.rows 15) =
    PairSemantics.boundaryRow16 := by decide +kernel

theorem rowSound15 {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval (PairData.rows 15) (momentVector H) = 0 := by
  unfold momentVector
  rw [← Integer.Sparse.eval_reindex]
  rw [rowCheck15]
  exact PairSemantics.boundarySound16 hH

end MUB6.Certificate.PairSourceBridge

end OAI

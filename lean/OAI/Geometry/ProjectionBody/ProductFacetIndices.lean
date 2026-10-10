import Mathlib.Data.Fin.Tuple.Basic

namespace OAI

namespace ProjectionCounterexample

lemma first_succAbove_first (i : Fin 10) (j : Fin 9) :
    (i.castAdd 10).succAbove (j.castAdd 10) = (i.succAbove j).castAdd 10 := by
  ext
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_castAdd]
  split_ifs <;> rfl

lemma first_succAbove_second (i : Fin 10) (j : Fin 10) :
    (i.castAdd 10).succAbove (j.natAdd 9) = j.natAdd 10 := by
  ext
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_castAdd, Fin.val_natAdd]
  split_ifs with h
  · omega
  · simp only [Fin.val_succ, Fin.val_natAdd]
    omega

lemma second_succAbove_first (i : Fin 10) (j : Fin 10) :
    (i.natAdd 10).succAbove (j.castAdd 9) = j.castAdd 10 := by
  ext
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_castAdd, Fin.val_natAdd]
  split_ifs with h
  · rfl
  · omega

lemma second_succAbove_second (i : Fin 10) (j : Fin 9) :
    (i.natAdd 10).succAbove (j.natAdd 10) = (i.succAbove j).natAdd 10 := by
  ext
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_natAdd]
  split_ifs <;> simp_all only [Fin.val_castSucc, Fin.val_succ, Fin.val_natAdd] <;> omega

end ProjectionCounterexample

end OAI

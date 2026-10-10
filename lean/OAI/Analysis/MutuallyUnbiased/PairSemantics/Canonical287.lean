import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9184 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 1, -1, 1], ![0, 1, 3, -4]]

def raw9184step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, 1, -2], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![1, -1, 1, -1], ![0, -1, -3, 4]]

def raw9184step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9184 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9184 = injectiveMoment H node3411 := by
  calc
    injectiveMoment H raw9184 = injectiveMoment H raw9184step0 := by
      have heq : raw9184step0 = -raw9184 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9184).symm
    injectiveMoment H raw9184step0 = injectiveMoment H raw9184step1 := by
      have heq : raw9184step1 = (fun i j => raw9184step0 (permutation395 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9184step0 permutation395 permutation15
    _ = injectiveMoment H node3411 := by rfl

def raw9185 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, -1, 2], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 1, 1], ![0, 2, 2, -4]]

def raw9185step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, 1, -2], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, -1, -1], ![0, -2, -2, 4]]

def raw9185step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical9185 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9185 = injectiveMoment H node3112 := by
  calc
    injectiveMoment H raw9185 = injectiveMoment H raw9185step0 := by
      have heq : raw9185step0 = -raw9185 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9185).symm
    injectiveMoment H raw9185step0 = injectiveMoment H raw9185step1 := by
      have heq : raw9185step1 = (fun i j => raw9185step0 (permutation373 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9185step0 permutation373 permutation15
    _ = injectiveMoment H node3112 := by rfl

def raw9186 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def raw9186step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical9186 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9186 = injectiveMoment H node2749 := by
  calc
    injectiveMoment H raw9186 = injectiveMoment H raw9186step0 := by
      have heq : raw9186step0 = (fun i j => raw9186 (permutation57 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9186 permutation57 permutation11
    _ = injectiveMoment H node2749 := by rfl

def raw9187 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 0, 1], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def raw9187step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![-1, 0, 1, 0], ![1, 1, -3, 1]]

def raw9187step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -2, 2], ![1, 0, -1, 0], ![-1, -1, 3, -1]]

def raw9187step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical9187 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9187 = injectiveMoment H node974 := by
  calc
    injectiveMoment H raw9187 = injectiveMoment H raw9187step0 := by
      have heq : raw9187step0 = raw9187.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9187).symm
    injectiveMoment H raw9187step0 = injectiveMoment H raw9187step1 := by
      have heq : raw9187step1 = -raw9187step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9187step0).symm
    injectiveMoment H raw9187step1 = injectiveMoment H raw9187step2 := by
      have heq : raw9187step2 = (fun i j => raw9187step1 (permutation29 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9187step1 permutation29 permutation10
    _ = injectiveMoment H node974 := by rfl

def raw9188 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 0, 1], ![0, 2, 2, -4], ![1, -2, -1, 2]]

def raw9188step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 2, -2], ![-1, 0, 2, -1], ![1, 1, -4, 2]]

def raw9188step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 0, -2, 2], ![1, 0, -2, 1], ![-1, -1, 4, -2]]

def raw9188step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical9188 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9188 = injectiveMoment H node914 := by
  calc
    injectiveMoment H raw9188 = injectiveMoment H raw9188step0 := by
      have heq : raw9188step0 = raw9188.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9188).symm
    injectiveMoment H raw9188step0 = injectiveMoment H raw9188step1 := by
      have heq : raw9188step1 = -raw9188step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9188step0).symm
    injectiveMoment H raw9188step1 = injectiveMoment H raw9188step2 := by
      have heq : raw9188step2 = (fun i j => raw9188step1 (permutation29 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9188step1 permutation29 permutation10
    _ = injectiveMoment H node914 := by rfl

def raw9189 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw9189step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical9189 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9189 = injectiveMoment H node2756 := by
  calc
    injectiveMoment H raw9189 = injectiveMoment H raw9189step0 := by
      have heq : raw9189step0 = (fun i j => raw9189 (permutation89 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9189 permutation89 permutation27
    _ = injectiveMoment H node2756 := by rfl

def raw9190 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def raw9190step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical9190 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9190 = injectiveMoment H node1118 := by
  calc
    injectiveMoment H raw9190 = injectiveMoment H raw9190step0 := by
      have heq : raw9190step0 = (fun i j => raw9190 (permutation29 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9190 permutation29 permutation19
    _ = injectiveMoment H node1118 := by rfl

def raw9191 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw9191step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical9191 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9191 = injectiveMoment H node1048 := by
  calc
    injectiveMoment H raw9191 = injectiveMoment H raw9191step0 := by
      have heq : raw9191step0 = (fun i j => raw9191 (permutation18 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9191 permutation18 permutation27
    _ = injectiveMoment H node1048 := by rfl

def raw9192 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, -2, -1, 2]]

def raw9192step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -2, -1, 2]]

theorem canonical9192 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9192 = injectiveMoment H node1316 := by
  calc
    injectiveMoment H raw9192 = injectiveMoment H raw9192step0 := by
      have heq : raw9192step0 = (fun i j => raw9192 (permutation15 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9192 permutation15 permutation9
    _ = injectiveMoment H node1316 := by rfl

def raw9193 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def raw9193step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

theorem canonical9193 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9193 = injectiveMoment H node2420 := by
  calc
    injectiveMoment H raw9193 = injectiveMoment H raw9193step0 := by
      have heq : raw9193step0 = (fun i j => raw9193 (permutation64 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9193 permutation64 permutation13
    _ = injectiveMoment H node2420 := by rfl

def raw9194 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def raw9194step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

theorem canonical9194 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9194 = injectiveMoment H node2843 := by
  calc
    injectiveMoment H raw9194 = injectiveMoment H raw9194step0 := by
      have heq : raw9194step0 = (fun i j => raw9194 (permutation57 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9194 permutation57 permutation9
    _ = injectiveMoment H node2843 := by rfl

def raw9195 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def raw9195step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem canonical9195 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9195 = injectiveMoment H node2844 := by
  calc
    injectiveMoment H raw9195 = injectiveMoment H raw9195step0 := by
      have heq : raw9195step0 = (fun i j => raw9195 (permutation57 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9195 permutation57 permutation9
    _ = injectiveMoment H node2844 := by rfl

def raw9196 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def raw9196step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem canonical9196 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9196 = injectiveMoment H node2845 := by
  calc
    injectiveMoment H raw9196 = injectiveMoment H raw9196step0 := by
      have heq : raw9196step0 = (fun i j => raw9196 (permutation57 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9196 permutation57 permutation9
    _ = injectiveMoment H node2845 := by rfl

def raw9197 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-1, -1, 0, 2], ![1, 0, 3, -4]]

def raw9197step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem canonical9197 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9197 = injectiveMoment H node3378 := by
  calc
    injectiveMoment H raw9197 = injectiveMoment H raw9197step0 := by
      have heq : raw9197step0 = (fun i j => raw9197 (permutation277 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9197 permutation277 permutation9
    _ = injectiveMoment H node3378 := by rfl

def raw9198 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 1, 3, -4], ![1, -2, -1, 2]]

def raw9198step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 1, 1, -2], ![-1, -1, 3, -1], ![1, 1, -4, 2]]

def raw9198step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, -1, -1, 2], ![1, 1, -3, 1], ![-1, -1, 4, -2]]

def raw9198step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, 1, -3]]

theorem canonical9198 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9198 = injectiveMoment H node893 := by
  calc
    injectiveMoment H raw9198 = injectiveMoment H raw9198step0 := by
      have heq : raw9198step0 = raw9198.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw9198).symm
    injectiveMoment H raw9198step0 = injectiveMoment H raw9198step1 := by
      have heq : raw9198step1 = -raw9198step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9198step0).symm
    injectiveMoment H raw9198step1 = injectiveMoment H raw9198step2 := by
      have heq : raw9198step2 = (fun i j => raw9198step1 (permutation29 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9198step1 permutation29 permutation10
    _ = injectiveMoment H node893 := by rfl

def raw9199 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, -1, 2], ![0, 1, 3, -4]]

def raw9199step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, -1, 1, -1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![1, 0, 1, -2], ![0, -1, -3, 4]]

def raw9199step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9199 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9199 = injectiveMoment H node3411 := by
  calc
    injectiveMoment H raw9199 = injectiveMoment H raw9199step0 := by
      have heq : raw9199step0 = -raw9199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9199).symm
    injectiveMoment H raw9199step0 = injectiveMoment H raw9199step1 := by
      have heq : raw9199step1 = (fun i j => raw9199step0 (permutation335 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9199step0 permutation335 permutation15
    _ = injectiveMoment H node3411 := by rfl

def raw9200 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![0, 1, 3, -4]]

def raw9200step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical9200 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9200 = injectiveMoment H node3381 := by
  calc
    injectiveMoment H raw9200 = injectiveMoment H raw9200step0 := by
      have heq : raw9200step0 = (fun i j => raw9200 (permutation279 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9200 permutation279 permutation9
    _ = injectiveMoment H node3381 := by rfl

def raw9201 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -2, -1, 2]]

def raw9201step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

theorem canonical9201 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9201 = injectiveMoment H node1362 := by
  calc
    injectiveMoment H raw9201 = injectiveMoment H raw9201step0 := by
      have heq : raw9201step0 = (fun i j => raw9201 (permutation15 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9201 permutation15 permutation11
    _ = injectiveMoment H node1362 := by rfl

def raw9202 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![0, 1, 2, -3], ![1, -2, -2, 3]]

def raw9202step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, -2, 3]]

theorem canonical9202 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9202 = injectiveMoment H node1367 := by
  calc
    injectiveMoment H raw9202 = injectiveMoment H raw9202step0 := by
      have heq : raw9202step0 = (fun i j => raw9202 (permutation15 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9202 permutation15 permutation9
    _ = injectiveMoment H node1367 := by rfl

def raw9203 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 2, -2], ![0, 1, 1, -2], ![1, -2, -2, 3]]

def raw9203step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -2, -2, 3]]

theorem canonical9203 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9203 = injectiveMoment H node1371 := by
  calc
    injectiveMoment H raw9203 = injectiveMoment H raw9203step0 := by
      have heq : raw9203step0 = (fun i j => raw9203 (permutation15 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9203 permutation15 permutation9
    _ = injectiveMoment H node1371 := by rfl

def raw9204 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, -2, 3], ![0, 1, 3, -4]]

def raw9204step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 2, -3], ![0, -1, -3, 4]]

def raw9204step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 1, -1], ![1, 2, -3], ![-1, -3, 4]]

def raw9204step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![1, 2, -3]]

theorem canonical9204 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9204 = injectiveMoment H node51 := by
  calc
    injectiveMoment H raw9204 = injectiveMoment H raw9204step0 := by
      have heq : raw9204step0 = -raw9204 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9204).symm
    injectiveMoment H raw9204step0 = injectiveMoment H raw9204step1 := by
      have hz : ∀ i, raw9204step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9204step1 = (fun i j => raw9204step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9204step0 permutation9 hz
    injectiveMoment H raw9204step1 = injectiveMoment H raw9204step2 := by
      have heq : raw9204step2 = (fun i j => raw9204step1 (permutation7 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9204step1 permutation7 permutation3
    _ = injectiveMoment H node51 := by rfl

def raw9205 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 0, 2, 0], ![1, 2, 1, -4]]

def raw9205step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 1, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![2, 0, -2, 0], ![-1, -2, -1, 4]]

def raw9205step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical9205 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9205 = injectiveMoment H node2931 := by
  calc
    injectiveMoment H raw9205 = injectiveMoment H raw9205step0 := by
      have heq : raw9205step0 = -raw9205 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9205).symm
    injectiveMoment H raw9205step0 = injectiveMoment H raw9205step1 := by
      have heq : raw9205step1 = (fun i j => raw9205step0 (permutation319 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9205step0 permutation319 permutation15
    _ = injectiveMoment H node2931 := by rfl

def raw9206 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 1, 1, 0], ![1, 1, 2, -4]]

def raw9206step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

theorem canonical9206 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9206 = injectiveMoment H node3300 := by
  calc
    injectiveMoment H raw9206 = injectiveMoment H raw9206step0 := by
      have heq : raw9206step0 = (fun i j => raw9206 (permutation277 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9206 permutation277 permutation9
    _ = injectiveMoment H node3300 := by rfl

def raw9207 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![1, 0, 3, -4]]

def raw9207step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 1, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![2, -2, 0, 0], ![-1, 0, -3, 4]]

def raw9207step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical9207 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9207 = injectiveMoment H node3324 := by
  calc
    injectiveMoment H raw9207 = injectiveMoment H raw9207step0 := by
      have heq : raw9207step0 = -raw9207 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9207).symm
    injectiveMoment H raw9207step0 = injectiveMoment H raw9207step1 := by
      have heq : raw9207step1 = (fun i j => raw9207step0 (permutation297 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9207step0 permutation297 permutation15
    _ = injectiveMoment H node3324 := by rfl

def raw9208 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, -1, 1, 2], ![2, 1, 0, -3]]

def raw9208step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 1, -2], ![0, 0, -1, 1], ![0, -1, 0, 1], ![2, 1, -1, -2], ![-2, -1, 0, 3]]

def raw9208step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

theorem canonical9208 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9208 = injectiveMoment H node2940 := by
  calc
    injectiveMoment H raw9208 = injectiveMoment H raw9208step0 := by
      have heq : raw9208step0 = -raw9208 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9208).symm
    injectiveMoment H raw9208step0 = injectiveMoment H raw9208step1 := by
      have heq : raw9208step1 = (fun i j => raw9208step0 (permutation383 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9208step0 permutation383 permutation9
    _ = injectiveMoment H node2940 := by rfl

def raw9209 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -1, 1, -2]]

def raw9209step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 1, -2], ![0, 0, -1, 1], ![0, -1, 0, 1], ![2, -1, 0, -1], ![-2, 1, -1, 2]]

def raw9209step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

theorem canonical9209 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9209 = injectiveMoment H node3023 := by
  calc
    injectiveMoment H raw9209 = injectiveMoment H raw9209step0 := by
      have heq : raw9209step0 = -raw9209 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9209).symm
    injectiveMoment H raw9209step0 = injectiveMoment H raw9209step1 := by
      have heq : raw9209step1 = (fun i j => raw9209step0 (permutation363 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9209step0 permutation363 permutation11
    _ = injectiveMoment H node3023 := by rfl

def raw9210 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 2, 1, -1]]

def raw9210step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 1, -2], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, -2, -1, 1]]

def raw9210step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem canonical9210 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9210 = injectiveMoment H node3093 := by
  calc
    injectiveMoment H raw9210 = injectiveMoment H raw9210step0 := by
      have heq : raw9210step0 = -raw9210 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9210).symm
    injectiveMoment H raw9210step0 = injectiveMoment H raw9210step1 := by
      have heq : raw9210step1 = (fun i j => raw9210step0 (permutation369 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9210step0 permutation369 permutation17
    _ = injectiveMoment H node3093 := by rfl

def raw9211 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1], ![1, 1, 2, -4]]

def raw9211step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

theorem canonical9211 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9211 = injectiveMoment H node3195 := by
  calc
    injectiveMoment H raw9211 = injectiveMoment H raw9211step0 := by
      have heq : raw9211step0 = (fun i j => raw9211 (permutation277 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9211 permutation277 permutation9
    _ = injectiveMoment H node3195 := by rfl

def raw9212 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![1, 0, 3, -4]]

def raw9212step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem canonical9212 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9212 = injectiveMoment H node3272 := by
  calc
    injectiveMoment H raw9212 = injectiveMoment H raw9212step0 := by
      have heq : raw9212step0 = (fun i j => raw9212 (permutation277 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9212 permutation277 permutation9
    _ = injectiveMoment H node3272 := by rfl

def raw9213 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 3, -2]]

def raw9213step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical9213 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9213 = injectiveMoment H node3234 := by
  calc
    injectiveMoment H raw9213 = injectiveMoment H raw9213step0 := by
      have heq : raw9213step0 = (fun i j => raw9213 (permutation331 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9213 permutation331 permutation10
    _ = injectiveMoment H node3234 := by rfl

def raw9214 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 2, -1]]

def raw9214step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 1, -2], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, -1, -2, 1]]

def raw9214step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem canonical9214 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9214 = injectiveMoment H node3091 := by
  calc
    injectiveMoment H raw9214 = injectiveMoment H raw9214step0 := by
      have heq : raw9214step0 = -raw9214 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9214).symm
    injectiveMoment H raw9214step0 = injectiveMoment H raw9214step1 := by
      have heq : raw9214step1 = (fun i j => raw9214step0 (permutation371 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9214step0 permutation371 permutation23
    _ = injectiveMoment H node3091 := by rfl

def raw9215 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, -1, -1, 2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![1, -1, 2, -2]]

def raw9215step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 1, -1], ![0, 1, 1, -2], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![2, -1, 0, -1], ![-1, 1, -2, 2]]

def raw9215step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical9215 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9215 = injectiveMoment H node3027 := by
  calc
    injectiveMoment H raw9215 = injectiveMoment H raw9215step0 := by
      have heq : raw9215step0 = -raw9215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9215).symm
    injectiveMoment H raw9215step0 = injectiveMoment H raw9215step1 := by
      have heq : raw9215step1 = (fun i j => raw9215step0 (permutation387 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9215step0 permutation387 permutation21
    _ = injectiveMoment H node3027 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

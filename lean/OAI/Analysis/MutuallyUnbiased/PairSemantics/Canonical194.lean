import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes39

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6208 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![0, 1, 1, -2]]

def raw6208step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical6208 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6208 = injectiveMoment H node2534 := by
  calc
    injectiveMoment H raw6208 = injectiveMoment H raw6208step0 := by
      have heq : raw6208step0 = (fun i j => raw6208 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6208 permutation34 permutation9
    _ = injectiveMoment H node2534 := by rfl

def raw6209 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 0, 1, -1], ![1, 1, -1, -1]]

def raw6209step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

theorem canonical6209 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6209 = injectiveMoment H node2531 := by
  calc
    injectiveMoment H raw6209 = injectiveMoment H raw6209step0 := by
      have heq : raw6209step0 = (fun i j => raw6209 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6209 permutation35 permutation9
    _ = injectiveMoment H node2531 := by rfl

def raw6210 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![0, 1, 0, -1]]

def raw6210step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical6210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6210 = injectiveMoment H node2551 := by
  calc
    injectiveMoment H raw6210 = injectiveMoment H raw6210step0 := by
      have heq : raw6210step0 = (fun i j => raw6210 (permutation43 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6210 permutation43 permutation11
    _ = injectiveMoment H node2551 := by rfl

def raw6211 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def raw6211step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical6211 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6211 = injectiveMoment H node969 := by
  calc
    injectiveMoment H raw6211 = injectiveMoment H raw6211step0 := by
      have heq : raw6211step0 = (fun i j => raw6211 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6211 permutation11 permutation11
    _ = injectiveMoment H node969 := by rfl

def raw6212 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw6212step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, -1, 2, 0], ![-1, 1, 1, -1], ![3, 0, -3, 0]]

def raw6212step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1]]

theorem canonical6212 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6212 = injectiveMoment H node1268 := by
  calc
    injectiveMoment H raw6212 = injectiveMoment H raw6212step0 := by
      have heq : raw6212step0 = raw6212.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6212).symm
    injectiveMoment H raw6212step0 = injectiveMoment H raw6212step1 := by
      have heq : raw6212step1 = (fun i j => raw6212step0 (permutation19 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6212step0 permutation19 permutation19
    _ = injectiveMoment H node1268 := by rfl

def raw6213 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![1, 1, -1, -1], ![0, 1, 1, -2]]

def raw6213step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical6213 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6213 = injectiveMoment H node936 := by
  calc
    injectiveMoment H raw6213 = injectiveMoment H raw6213step0 := by
      have heq : raw6213step0 = (fun i j => raw6213 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6213 permutation10 permutation9
    _ = injectiveMoment H node936 := by rfl

def raw6214 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

theorem canonical6214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6214 = injectiveMoment H node2537 := by
  rfl

def raw6215 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical6215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6215 = injectiveMoment H node2538 := by
  rfl

def raw6216 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical6216 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6216 = injectiveMoment H node2539 := by
  rfl

def raw6217 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw6217step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical6217 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6217 = injectiveMoment H node2532 := by
  calc
    injectiveMoment H raw6217 = injectiveMoment H raw6217step0 := by
      have heq : raw6217step0 = (fun i j => raw6217 (permutation41 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6217 permutation41 permutation11
    _ = injectiveMoment H node2532 := by rfl

def raw6218 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def raw6218step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical6218 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6218 = injectiveMoment H node939 := by
  calc
    injectiveMoment H raw6218 = injectiveMoment H raw6218step0 := by
      have heq : raw6218step0 = (fun i j => raw6218 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6218 permutation11 permutation11
    _ = injectiveMoment H node939 := by rfl

def raw6219 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical6219 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6219 = injectiveMoment H node2542 := by
  rfl

def raw6220 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

theorem canonical6220 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6220 = injectiveMoment H node942 := by
  rfl

def raw6221 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical6221 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6221 = injectiveMoment H node943 := by
  rfl

def raw6222 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem canonical6222 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6222 = injectiveMoment H node944 := by
  rfl

def raw6223 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical6223 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6223 = injectiveMoment H node945 := by
  rfl

def raw6224 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical6224 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6224 = injectiveMoment H node946 := by
  rfl

def raw6225 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![1, 2, -1, -2]]

def raw6225step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 2, -1], ![3, -1, -2]]

def raw6225step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![1, -2, 1], ![-3, 1, 2]]

def raw6225step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical6225 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6225 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw6225 = injectiveMoment H raw6225step0 := by
      have heq : raw6225step0 = raw6225.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6225).symm
    injectiveMoment H raw6225step0 = injectiveMoment H raw6225step1 := by
      have heq : raw6225step1 = -raw6225step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6225step0).symm
    injectiveMoment H raw6225step1 = injectiveMoment H raw6225step2 := by
      have heq : raw6225step2 = (fun i j => raw6225step1 (permutation21 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6225step1 permutation21 permutation6
    _ = injectiveMoment H node229 := by rfl

def raw6226 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem canonical6226 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6226 = injectiveMoment H node948 := by
  rfl

def raw6227 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, 1, -1, -1]]

theorem canonical6227 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6227 = injectiveMoment H node949 := by
  rfl

def raw6228 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 1, -2, 0]]

theorem canonical6228 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6228 = injectiveMoment H node950 := by
  rfl

def raw6229 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical6229 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6229 = injectiveMoment H node951 := by
  rfl

def raw6230 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical6230 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6230 = injectiveMoment H node952 := by
  rfl

def raw6231 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical6231 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6231 = injectiveMoment H node953 := by
  rfl

def raw6232 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![1, 2, -2, -1]]

def raw6232step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 3, -2], ![3, -2, -1]]

def raw6232step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 1, -2], ![1, -3, 2], ![-3, 2, 1]]

def raw6232step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

theorem canonical6232 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6232 = injectiveMoment H node109 := by
  calc
    injectiveMoment H raw6232 = injectiveMoment H raw6232step0 := by
      have heq : raw6232step0 = raw6232.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6232).symm
    injectiveMoment H raw6232step0 = injectiveMoment H raw6232step1 := by
      have heq : raw6232step1 = -raw6232step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6232step0).symm
    injectiveMoment H raw6232step1 = injectiveMoment H raw6232step2 := by
      have heq : raw6232step2 = (fun i j => raw6232step1 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6232step1 permutation21 permutation5
    _ = injectiveMoment H node109 := by rfl

def raw6233 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![-1, 2, -1, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw6233step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![0, 0, 1, -1], ![1, -2, 1, 0], ![-1, 1, -3, 3], ![-1, 0, 0, 1]]

def raw6233step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 0, 1], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 1, 1, -3]]

theorem canonical6233 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6233 = injectiveMoment H node2319 := by
  calc
    injectiveMoment H raw6233 = injectiveMoment H raw6233step0 := by
      have heq : raw6233step0 = -raw6233 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6233).symm
    injectiveMoment H raw6233step0 = injectiveMoment H raw6233step1 := by
      have heq : raw6233step1 = (fun i j => raw6233step0 (permutation101 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6233step0 permutation101 permutation15
    _ = injectiveMoment H node2319 := by rfl

def raw6234 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![-1, 2, 0, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw6234step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 1, 1, -3], ![0, 0, 1, -1], ![1, -2, 0, 1], ![-1, 1, -3, 3], ![-1, 0, 1, 0]]

def raw6234step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 1, 1, -3]]

theorem canonical6234 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6234 = injectiveMoment H node2257 := by
  calc
    injectiveMoment H raw6234 = injectiveMoment H raw6234step0 := by
      have heq : raw6234step0 = -raw6234 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6234).symm
    injectiveMoment H raw6234step0 = injectiveMoment H raw6234step1 := by
      have heq : raw6234step1 = (fun i j => raw6234step0 (permutation101 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6234step0 permutation101 permutation15
    _ = injectiveMoment H node2257 := by rfl

def raw6235 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, 3, -3], ![1, 0, 0, -1]]

def raw6235step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical6235 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6235 = injectiveMoment H node2547 := by
  calc
    injectiveMoment H raw6235 = injectiveMoment H raw6235step0 := by
      have heq : raw6235step0 = (fun i j => raw6235 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6235 permutation35 permutation9
    _ = injectiveMoment H node2547 := by rfl

def raw6236 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem canonical6236 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6236 = injectiveMoment H node2549 := by
  rfl

def raw6237 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![0, 1, 0, -1]]

def raw6237step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 3, -3]]

theorem canonical6237 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6237 = injectiveMoment H node2548 := by
  calc
    injectiveMoment H raw6237 = injectiveMoment H raw6237step0 := by
      have heq : raw6237step0 = (fun i j => raw6237 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6237 permutation34 permutation9
    _ = injectiveMoment H node2548 := by rfl

def raw6238 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 3, -4]]

theorem canonical6238 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6238 = injectiveMoment H node962 := by
  rfl

def raw6239 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 0, 3, -3], ![1, 0, -1, 0]]

def raw6239step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical6239 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6239 = injectiveMoment H node2547 := by
  calc
    injectiveMoment H raw6239 = injectiveMoment H raw6239step0 := by
      have heq : raw6239step0 = (fun i j => raw6239 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6239 permutation36 permutation15
    _ = injectiveMoment H node2547 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

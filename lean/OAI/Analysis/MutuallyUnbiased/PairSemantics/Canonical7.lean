import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw224 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]

theorem canonical224 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw224 = injectiveMoment H node70 := by
  rfl

def raw225 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

theorem canonical225 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw225 = injectiveMoment H node301 := by
  rfl

def raw226 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]

theorem canonical226 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw226 = injectiveMoment H node302 := by
  rfl

def raw227 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]

theorem canonical227 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw227 = injectiveMoment H node71 := by
  rfl

def raw228 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]

def raw228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical228 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw228 = injectiveMoment H node387 := by
  calc
    injectiveMoment H raw228 = injectiveMoment H raw228step0 := by
      have heq : raw228step0 = (fun i j => raw228 (permutation41 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw228 permutation41 permutation5
    _ = injectiveMoment H node387 := by rfl

def raw229 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]

def raw229step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical229 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw229 = injectiveMoment H node123 := by
  calc
    injectiveMoment H raw229 = injectiveMoment H raw229step0 := by
      have heq : raw229step0 = (fun i j => raw229 (permutation11 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw229 permutation11 permutation5
    _ = injectiveMoment H node123 := by rfl

def raw230 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]

def raw230step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical230 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw230 = injectiveMoment H node127 := by
  calc
    injectiveMoment H raw230 = injectiveMoment H raw230step0 := by
      have heq : raw230step0 = (fun i j => raw230 (permutation13 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw230 permutation13 permutation5
    _ = injectiveMoment H node127 := by rfl

def raw231 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

theorem canonical231 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw231 = injectiveMoment H node72 := by
  rfl

def raw232 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

theorem canonical232 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw232 = injectiveMoment H node299 := by
  calc
    injectiveMoment H raw232 = injectiveMoment H raw232step0 := by
      have heq : raw232step0 = (fun i j => raw232 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw232 permutation39 permutation3
    _ = injectiveMoment H node299 := by rfl

def raw233 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

theorem canonical233 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw233 = injectiveMoment H node300 := by
  calc
    injectiveMoment H raw233 = injectiveMoment H raw233step0 := by
      have heq : raw233step0 = (fun i j => raw233 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw233 permutation39 permutation3
    _ = injectiveMoment H node300 := by rfl

def raw234 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

theorem canonical234 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw234 = injectiveMoment H node303 := by
  rfl

def raw235 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]

def raw235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

theorem canonical235 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw235 = injectiveMoment H node303 := by
  calc
    injectiveMoment H raw235 = injectiveMoment H raw235step0 := by
      have heq : raw235step0 = (fun i j => raw235 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw235 permutation34 permutation3
    _ = injectiveMoment H node303 := by rfl

def raw236 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]

theorem canonical236 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw236 = injectiveMoment H node73 := by
  rfl

def raw237 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]

def raw237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical237 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw237 = injectiveMoment H node384 := by
  calc
    injectiveMoment H raw237 = injectiveMoment H raw237step0 := by
      have heq : raw237step0 = (fun i j => raw237 (permutation42 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw237 permutation42 permutation5
    _ = injectiveMoment H node384 := by rfl

def raw238 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]

def raw238step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical238 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw238 = injectiveMoment H node120 := by
  calc
    injectiveMoment H raw238 = injectiveMoment H raw238step0 := by
      have heq : raw238step0 = (fun i j => raw238 (permutation12 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw238 permutation12 permutation5
    _ = injectiveMoment H node120 := by rfl

def raw239 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

theorem canonical239 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw239 = injectiveMoment H node74 := by
  rfl

def raw240 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![2, -1, -1], ![1, 1, -2]]

def raw240step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

theorem canonical240 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw240 = injectiveMoment H node74 := by
  calc
    injectiveMoment H raw240 = injectiveMoment H raw240step0 := by
      have heq : raw240step0 = (fun i j => raw240 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw240 permutation10 permutation3
    _ = injectiveMoment H node74 := by rfl

def raw241 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![3, 0, -3]]

def raw241step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![2, 0, -2]]

theorem canonical241 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw241 = injectiveMoment H node28 := by
  calc
    injectiveMoment H raw241 = injectiveMoment H raw241step0 := by
      have heq : raw241step0 = (fun i j => raw241 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw241 permutation4 permutation5
    _ = injectiveMoment H node28 := by rfl

def raw242 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

theorem canonical242 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw242 = injectiveMoment H node304 := by
  rfl

def raw243 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]

theorem canonical243 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw243 = injectiveMoment H node75 := by
  rfl

def raw244 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]

theorem canonical244 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw244 = injectiveMoment H node76 := by
  rfl

def raw245 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![2, -1, -1], ![1, 0, -1]]

def raw245step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]

theorem canonical245 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw245 = injectiveMoment H node76 := by
  calc
    injectiveMoment H raw245 = injectiveMoment H raw245step0 := by
      have heq : raw245step0 = (fun i j => raw245 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw245 permutation10 permutation3
    _ = injectiveMoment H node76 := by rfl

def raw246 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![3, -1, -2]]

theorem canonical246 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw246 = injectiveMoment H node17 := by
  rfl

def raw247 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]

theorem canonical247 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw247 = injectiveMoment H node77 := by
  rfl

def raw248 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]

theorem canonical248 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw248 = injectiveMoment H node78 := by
  rfl

def raw249 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 2, -3], ![1, 1, -2]]

def raw249step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]

theorem canonical249 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw249 = injectiveMoment H node78 := by
  calc
    injectiveMoment H raw249 = injectiveMoment H raw249step0 := by
      have heq : raw249step0 = (fun i j => raw249 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw249 permutation10 permutation3
    _ = injectiveMoment H node78 := by rfl

def raw250 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![2, 3, -5]]

def raw250step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, -1, 3], ![5, 0, -5]]

def raw250step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 5, -5], ![1, -3, 2]]

theorem canonical250 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw250 = injectiveMoment H node60 := by
  calc
    injectiveMoment H raw250 = injectiveMoment H raw250step0 := by
      have heq : raw250step0 = raw250.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw250).symm
    injectiveMoment H raw250step0 = injectiveMoment H raw250step1 := by
      have heq : raw250step1 = (fun i j => raw250step0 (permutation6 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw250step0 permutation6 permutation5
    _ = injectiveMoment H node60 := by rfl

def raw251 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]

def raw251step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

theorem canonical251 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw251 = injectiveMoment H node119 := by
  calc
    injectiveMoment H raw251 = injectiveMoment H raw251step0 := by
      have heq : raw251step0 = (fun i j => raw251 (permutation9 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw251 permutation9 permutation5
    _ = injectiveMoment H node119 := by rfl

def raw252 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]

def raw252step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical252 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw252 = injectiveMoment H node124 := by
  calc
    injectiveMoment H raw252 = injectiveMoment H raw252step0 := by
      have heq : raw252step0 = (fun i j => raw252 (permutation9 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw252 permutation9 permutation5
    _ = injectiveMoment H node124 := by rfl

def raw253 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![2, 2, -4]]

def raw253step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![5, -1, -4]]

def raw253step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 2, -2], ![1, 2, -3]]

theorem canonical253 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw253 = injectiveMoment H node48 := by
  calc
    injectiveMoment H raw253 = injectiveMoment H raw253step0 := by
      have heq : raw253step0 = raw253.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw253).symm
    injectiveMoment H raw253step0 = injectiveMoment H raw253step1 := by
      have heq : raw253step1 = (fun i j => raw253step0 (permutation8 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw253step0 permutation8 permutation6
    _ = injectiveMoment H node48 := by rfl

def raw254 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 1, -2], ![1, 0, -1], ![1, 1, -2]]

def raw254step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical254 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw254 = injectiveMoment H node124 := by
  calc
    injectiveMoment H raw254 = injectiveMoment H raw254step0 := by
      have heq : raw254step0 = (fun i j => raw254 (permutation11 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw254 permutation11 permutation5
    _ = injectiveMoment H node124 := by rfl

def raw255 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 1, -2], ![2, 1, -3]]

def raw255step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![1, 1, -2], ![1, 2, -3]]

theorem canonical255 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw255 = injectiveMoment H node30 := by
  calc
    injectiveMoment H raw255 = injectiveMoment H raw255step0 := by
      have heq : raw255step0 = (fun i j => raw255 (permutation3 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw255 permutation3 permutation5
    _ = injectiveMoment H node30 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes52

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8320 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![1, 0, 3, -4]]

def raw8320step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![2, -2, 0, 0], ![-1, 0, -3, 4]]

def raw8320step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical8320 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8320 = injectiveMoment H node3324 := by
  calc
    injectiveMoment H raw8320 = injectiveMoment H raw8320step0 := by
      have heq : raw8320step0 = -raw8320 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8320).symm
    injectiveMoment H raw8320step0 = injectiveMoment H raw8320step1 := by
      have heq : raw8320step1 = (fun i j => raw8320step0 (permutation300 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8320step0 permutation300 permutation15
    _ = injectiveMoment H node3324 := by rfl

def raw8321 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, -1, 1, 2], ![2, 1, 0, -3]]

def raw8321step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, 1, -1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![2, 1, -1, -2], ![-2, -1, 0, 3]]

def raw8321step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

theorem canonical8321 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8321 = injectiveMoment H node2940 := by
  calc
    injectiveMoment H raw8321 = injectiveMoment H raw8321step0 := by
      have heq : raw8321step0 = -raw8321 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8321).symm
    injectiveMoment H raw8321step0 = injectiveMoment H raw8321step1 := by
      have heq : raw8321step1 = (fun i j => raw8321step0 (permutation385 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8321step0 permutation385 permutation9
    _ = injectiveMoment H node2940 := by rfl

def raw8322 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -1, 1, -2]]

def raw8322step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, 1, -1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![2, -1, 0, -1], ![-2, 1, -1, 2]]

def raw8322step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

theorem canonical8322 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8322 = injectiveMoment H node3023 := by
  calc
    injectiveMoment H raw8322 = injectiveMoment H raw8322step0 := by
      have heq : raw8322step0 = -raw8322 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8322).symm
    injectiveMoment H raw8322step0 = injectiveMoment H raw8322step1 := by
      have heq : raw8322step1 = (fun i j => raw8322step0 (permutation364 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8322step0 permutation364 permutation11
    _ = injectiveMoment H node3023 := by rfl

def raw8323 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 2, 1, -1]]

def raw8323step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, 1, -1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, -2, -1, 1]]

def raw8323step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem canonical8323 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8323 = injectiveMoment H node3093 := by
  calc
    injectiveMoment H raw8323 = injectiveMoment H raw8323step0 := by
      have heq : raw8323step0 = -raw8323 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8323).symm
    injectiveMoment H raw8323step0 = injectiveMoment H raw8323step1 := by
      have heq : raw8323step1 = (fun i j => raw8323step0 (permutation370 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8323step0 permutation370 permutation17
    _ = injectiveMoment H node3093 := by rfl

def raw8324 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1], ![1, 1, 2, -4]]

def raw8324step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

theorem canonical8324 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8324 = injectiveMoment H node3195 := by
  calc
    injectiveMoment H raw8324 = injectiveMoment H raw8324step0 := by
      have heq : raw8324step0 = (fun i j => raw8324 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8324 permutation258 permutation9
    _ = injectiveMoment H node3195 := by rfl

def raw8325 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![1, 0, 3, -4]]

def raw8325step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem canonical8325 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8325 = injectiveMoment H node3272 := by
  calc
    injectiveMoment H raw8325 = injectiveMoment H raw8325step0 := by
      have heq : raw8325step0 = (fun i j => raw8325 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8325 permutation258 permutation9
    _ = injectiveMoment H node3272 := by rfl

def raw8326 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 3, -2]]

def raw8326step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical8326 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8326 = injectiveMoment H node3234 := by
  calc
    injectiveMoment H raw8326 = injectiveMoment H raw8326step0 := by
      have heq : raw8326step0 = (fun i j => raw8326 (permutation308 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8326 permutation308 permutation10
    _ = injectiveMoment H node3234 := by rfl

def raw8327 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 2, -1]]

def raw8327step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, -1, -2, 1]]

def raw8327step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem canonical8327 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8327 = injectiveMoment H node3091 := by
  calc
    injectiveMoment H raw8327 = injectiveMoment H raw8327step0 := by
      have heq : raw8327step0 = -raw8327 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8327).symm
    injectiveMoment H raw8327step0 = injectiveMoment H raw8327step1 := by
      have heq : raw8327step1 = (fun i j => raw8327step0 (permutation372 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8327step0 permutation372 permutation23
    _ = injectiveMoment H node3091 := by rfl

def raw8328 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![1, -1, 2, -2]]

def raw8328step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, 1, -1], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![2, -1, 0, -1], ![-1, 1, -2, 2]]

def raw8328step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical8328 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8328 = injectiveMoment H node3027 := by
  calc
    injectiveMoment H raw8328 = injectiveMoment H raw8328step0 := by
      have heq : raw8328step0 = -raw8328 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8328).symm
    injectiveMoment H raw8328step0 = injectiveMoment H raw8328step1 := by
      have heq : raw8328step1 = (fun i j => raw8328step0 (permutation388 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8328step0 permutation388 permutation21
    _ = injectiveMoment H node3027 := by rfl

def raw8329 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def raw8329step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![0, -2, -2, 4]]

def raw8329step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical8329 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8329 = injectiveMoment H node3113 := by
  calc
    injectiveMoment H raw8329 = injectiveMoment H raw8329step0 := by
      have heq : raw8329step0 = -raw8329 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8329).symm
    injectiveMoment H raw8329step0 = injectiveMoment H raw8329step1 := by
      have heq : raw8329step1 = (fun i j => raw8329step0 (permutation382 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8329step0 permutation382 permutation15
    _ = injectiveMoment H node3113 := by rfl

def raw8330 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def raw8330step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical8330 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8330 = injectiveMoment H node3273 := by
  calc
    injectiveMoment H raw8330 = injectiveMoment H raw8330step0 := by
      have heq : raw8330step0 = (fun i j => raw8330 (permutation262 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8330 permutation262 permutation9
    _ = injectiveMoment H node3273 := by rfl

def raw8331 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, 1, 0, -3]]

def raw8331step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

theorem canonical8331 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8331 = injectiveMoment H node2939 := by
  calc
    injectiveMoment H raw8331 = injectiveMoment H raw8331step0 := by
      have heq : raw8331step0 = (fun i j => raw8331 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8331 permutation258 permutation9
    _ = injectiveMoment H node2939 := by rfl

def raw8332 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 2, 0, 0]]

def raw8332step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, -2, 0, 0]]

def raw8332step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem canonical8332 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8332 = injectiveMoment H node3170 := by
  calc
    injectiveMoment H raw8332 = injectiveMoment H raw8332step0 := by
      have heq : raw8332step0 = -raw8332 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8332).symm
    injectiveMoment H raw8332step0 = injectiveMoment H raw8332step1 := by
      have heq : raw8332step1 = (fun i j => raw8332step0 (permutation342 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8332step0 permutation342 permutation18
    _ = injectiveMoment H node3170 := by rfl

def raw8333 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 1, 0]]

def raw8333step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical8333 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8333 = injectiveMoment H node3206 := by
  calc
    injectiveMoment H raw8333 = injectiveMoment H raw8333step0 := by
      have heq : raw8333step0 = (fun i j => raw8333 (permutation338 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8333 permutation338 permutation13
    _ = injectiveMoment H node3206 := by rfl

def raw8334 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 1, 0]]

def raw8334step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical8334 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8334 = injectiveMoment H node3200 := by
  calc
    injectiveMoment H raw8334 = injectiveMoment H raw8334step0 := by
      have heq : raw8334step0 = (fun i j => raw8334 (permutation337 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8334 permutation337 permutation13
    _ = injectiveMoment H node3200 := by rfl

def raw8335 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 2, 1, -3]]

def raw8335step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![0, -2, -1, 3]]

def raw8335step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem canonical8335 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8335 = injectiveMoment H node2949 := by
  calc
    injectiveMoment H raw8335 = injectiveMoment H raw8335step0 := by
      have heq : raw8335step0 = -raw8335 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8335).symm
    injectiveMoment H raw8335step0 = injectiveMoment H raw8335step1 := by
      have heq : raw8335step1 = (fun i j => raw8335step0 (permutation354 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8335step0 permutation354 permutation17
    _ = injectiveMoment H node2949 := by rfl

def raw8336 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 2, -2, 2]]

def raw8336step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical8336 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8336 = injectiveMoment H node3306 := by
  calc
    injectiveMoment H raw8336 = injectiveMoment H raw8336step0 := by
      have heq : raw8336step0 = (fun i j => raw8336 (permutation326 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8336 permutation326 permutation9
    _ = injectiveMoment H node3306 := by rfl

def raw8337 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1]]

def raw8337step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

theorem canonical8337 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8337 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw8337 = injectiveMoment H raw8337step0 := by
      have hz : ∀ i, raw8337 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8337step0 = (fun i j => raw8337 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8337 permutation9 hz
    _ = injectiveMoment H node63 := by rfl

def raw8338 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, 4, -4], ![0, 1, -3, 2]]

def raw8338step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, -4, 4], ![0, -1, 3, -2]]

def raw8338step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![0, -4, 4], ![-1, 3, -2]]

def raw8338step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

theorem canonical8338 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8338 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw8338 = injectiveMoment H raw8338step0 := by
      have heq : raw8338step0 = -raw8338 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8338).symm
    injectiveMoment H raw8338step0 = injectiveMoment H raw8338step1 := by
      have hz : ∀ i, raw8338step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8338step1 = (fun i j => raw8338step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8338step0 permutation9 hz
    injectiveMoment H raw8338step1 = injectiveMoment H raw8338step2 := by
      have heq : raw8338step2 = (fun i j => raw8338step1 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8338step1 permutation8 permutation4
    _ = injectiveMoment H node59 := by rfl

def raw8339 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![1, 0, 3, -4]]

def raw8339step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem canonical8339 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8339 = injectiveMoment H node3159 := by
  calc
    injectiveMoment H raw8339 = injectiveMoment H raw8339step0 := by
      have heq : raw8339step0 = (fun i j => raw8339 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8339 permutation258 permutation9
    _ = injectiveMoment H node3159 := by rfl

def raw8340 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, 2, 0]]

def raw8340step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![2, 0, -2, 0]]

def raw8340step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical8340 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8340 = injectiveMoment H node3174 := by
  calc
    injectiveMoment H raw8340 = injectiveMoment H raw8340step0 := by
      have heq : raw8340step0 = -raw8340 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8340).symm
    injectiveMoment H raw8340step0 = injectiveMoment H raw8340step1 := by
      have heq : raw8340step1 = (fun i j => raw8340step0 (permutation372 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8340step0 permutation372 permutation24
    _ = injectiveMoment H node3174 := by rfl

def raw8341 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def raw8341step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical8341 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8341 = injectiveMoment H node3160 := by
  calc
    injectiveMoment H raw8341 = injectiveMoment H raw8341step0 := by
      have heq : raw8341step0 = (fun i j => raw8341 (permutation262 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8341 permutation262 permutation9
    _ = injectiveMoment H node3160 := by rfl

def raw8342 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 2, 1, -3], ![0, -1, 0, 1]]

def raw8342step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, -2, -1, 3], ![0, 1, 0, -1]]

def raw8342step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![-2, -1, 3], ![1, 0, -1]]

def raw8342step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, 1, -2]]

theorem canonical8342 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8342 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw8342 = injectiveMoment H raw8342step0 := by
      have heq : raw8342step0 = -raw8342 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8342).symm
    injectiveMoment H raw8342step0 = injectiveMoment H raw8342step1 := by
      have hz : ∀ i, raw8342step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8342step1 = (fun i j => raw8342step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8342step0 permutation9 hz
    injectiveMoment H raw8342step1 = injectiveMoment H raw8342step2 := by
      have heq : raw8342step2 = (fun i j => raw8342step1 (permutation6 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8342step1 permutation6 permutation5
    _ = injectiveMoment H node56 := by rfl

def raw8343 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8343step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical8343 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8343 = injectiveMoment H node2578 := by
  calc
    injectiveMoment H raw8343 = injectiveMoment H raw8343step0 := by
      have heq : raw8343step0 = (fun i j => raw8343 (permutation57 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8343 permutation57 permutation9
    _ = injectiveMoment H node2578 := by rfl

def raw8344 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw8344step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem canonical8344 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8344 = injectiveMoment H node2579 := by
  calc
    injectiveMoment H raw8344 = injectiveMoment H raw8344step0 := by
      have heq : raw8344step0 = (fun i j => raw8344 (permutation57 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8344 permutation57 permutation9
    _ = injectiveMoment H node2579 := by rfl

def raw8345 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 0, 2], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw8345step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 2, 0], ![0, 0, 2, -2], ![1, 2, -4, 1]]

def raw8345step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 1, -2, 0], ![0, 0, -2, 2], ![-1, -2, 4, -1]]

def raw8345step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem canonical8345 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8345 = injectiveMoment H node771 := by
  calc
    injectiveMoment H raw8345 = injectiveMoment H raw8345step0 := by
      have heq : raw8345step0 = raw8345.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8345).symm
    injectiveMoment H raw8345step0 = injectiveMoment H raw8345step1 := by
      have heq : raw8345step1 = -raw8345step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8345step0).symm
    injectiveMoment H raw8345step1 = injectiveMoment H raw8345step2 := by
      have heq : raw8345step2 = (fun i j => raw8345step1 (permutation31 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8345step1 permutation31 permutation10
    _ = injectiveMoment H node771 := by rfl

def raw8346 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8346step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical8346 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8346 = injectiveMoment H node2627 := by
  calc
    injectiveMoment H raw8346 = injectiveMoment H raw8346step0 := by
      have heq : raw8346step0 = (fun i j => raw8346 (permutation57 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8346 permutation57 permutation9
    _ = injectiveMoment H node2627 := by rfl

def raw8347 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw8347step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical8347 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8347 = injectiveMoment H node2632 := by
  calc
    injectiveMoment H raw8347 = injectiveMoment H raw8347step0 := by
      have heq : raw8347step0 = (fun i j => raw8347 (permutation57 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8347 permutation57 permutation9
    _ = injectiveMoment H node2632 := by rfl

def raw8348 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-1, 0, -1, 2], ![1, 1, 2, -4]]

def raw8348step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 1, -1, -1], ![0, -1, 1, 0], ![-1, 0, 1, 0], ![1, 0, 1, -2], ![-1, -1, -2, 4]]

def raw8348step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

theorem canonical8348 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8348 = injectiveMoment H node3341 := by
  calc
    injectiveMoment H raw8348 = injectiveMoment H raw8348step0 := by
      have heq : raw8348step0 = -raw8348 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8348).symm
    injectiveMoment H raw8348step0 = injectiveMoment H raw8348step1 := by
      have heq : raw8348step1 = (fun i j => raw8348step0 (permutation384 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8348step0 permutation384 permutation9
    _ = injectiveMoment H node3341 := by rfl

def raw8349 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def raw8349step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 2, 0], ![0, 1, 1, -2], ![1, 1, -3, 1]]

def raw8349step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 1, -2, 0], ![0, -1, -1, 2], ![-1, -1, 3, -1]]

def raw8349step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical8349 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8349 = injectiveMoment H node939 := by
  calc
    injectiveMoment H raw8349 = injectiveMoment H raw8349step0 := by
      have heq : raw8349step0 = raw8349.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8349).symm
    injectiveMoment H raw8349step0 = injectiveMoment H raw8349step1 := by
      have heq : raw8349step1 = -raw8349step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8349step0).symm
    injectiveMoment H raw8349step1 = injectiveMoment H raw8349step2 := by
      have heq : raw8349step2 = (fun i j => raw8349step1 (permutation28 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8349step1 permutation28 permutation13
    _ = injectiveMoment H node939 := by rfl

def raw8350 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 1, 1], ![0, 2, 2, -4], ![1, 0, -3, 2]]

def raw8350step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 2, 0], ![0, 1, 2, -3], ![1, 1, -4, 2]]

def raw8350step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 1, -2, 0], ![0, -1, -2, 3], ![-1, -1, 4, -2]]

def raw8350step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem canonical8350 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8350 = injectiveMoment H node898 := by
  calc
    injectiveMoment H raw8350 = injectiveMoment H raw8350step0 := by
      have heq : raw8350step0 = raw8350.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8350).symm
    injectiveMoment H raw8350step0 = injectiveMoment H raw8350step1 := by
      have heq : raw8350step1 = -raw8350step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8350step0).symm
    injectiveMoment H raw8350step1 = injectiveMoment H raw8350step2 := by
      have heq : raw8350step2 = (fun i j => raw8350step1 (permutation31 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8350step1 permutation31 permutation10
    _ = injectiveMoment H node898 := by rfl

def raw8351 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, -1, 2, 0], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw8351step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem canonical8351 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8351 = injectiveMoment H node1002 := by
  calc
    injectiveMoment H raw8351 = injectiveMoment H raw8351step0 := by
      have heq : raw8351step0 = (fun i j => raw8351 (permutation15 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8351 permutation15 permutation10
    _ = injectiveMoment H node1002 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

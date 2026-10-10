import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6304 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![1, 0, 3, -4]]

def raw6304step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, -2, 3], ![3, 1, -4]]

def raw6304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical6304 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6304 = injectiveMoment H node173 := by
  calc
    injectiveMoment H raw6304 = injectiveMoment H raw6304step0 := by
      have heq : raw6304step0 = raw6304.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6304).symm
    injectiveMoment H raw6304step0 = injectiveMoment H raw6304step1 := by
      have heq : raw6304step1 = (fun i j => raw6304step0 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6304step0 permutation21 permutation5
    _ = injectiveMoment H node173 := by rfl

def raw6305 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -1, 0], ![0, -1, 2, -1], ![1, 1, 0, -2]]

def raw6305step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical6305 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6305 = injectiveMoment H node939 := by
  calc
    injectiveMoment H raw6305 = injectiveMoment H raw6305step0 := by
      have heq : raw6305step0 = (fun i j => raw6305 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6305 permutation9 permutation11
    _ = injectiveMoment H node939 := by rfl

def raw6306 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -1, 0], ![0, 0, 2, -2], ![1, 0, 0, -1]]

def raw6306step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical6306 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6306 = injectiveMoment H node974 := by
  calc
    injectiveMoment H raw6306 = injectiveMoment H raw6306step0 := by
      have heq : raw6306step0 = (fun i j => raw6306 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6306 permutation11 permutation9
    _ = injectiveMoment H node974 := by rfl

def raw6307 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -1, 0], ![0, 0, 3, -3], ![1, 0, -1, 0]]

def raw6307step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, -1, 0]]

theorem canonical6307 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6307 = injectiveMoment H node978 := by
  calc
    injectiveMoment H raw6307 = injectiveMoment H raw6307step0 := by
      have heq : raw6307step0 = (fun i j => raw6307 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6307 permutation11 permutation9
    _ = injectiveMoment H node978 := by rfl

def raw6308 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 3, -3]]

def raw6308step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![-1, -1, -1, 3], ![3, 0, 0, -3]]

def raw6308step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, 1, -1, -1]]

theorem canonical6308 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6308 = injectiveMoment H node960 := by
  calc
    injectiveMoment H raw6308 = injectiveMoment H raw6308step0 := by
      have heq : raw6308step0 = raw6308.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6308).symm
    injectiveMoment H raw6308step0 = injectiveMoment H raw6308step1 := by
      have heq : raw6308step1 = (fun i j => raw6308step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6308step0 permutation22 permutation17
    _ = injectiveMoment H node960 := by rfl

def raw6309 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def raw6309step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![-1, -1, 0, 2], ![3, 0, -1, -2]]

def raw6309step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2], ![-3, 0, 1, 2]]

def raw6309step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

theorem canonical6309 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6309 = injectiveMoment H node1116 := by
  calc
    injectiveMoment H raw6309 = injectiveMoment H raw6309step0 := by
      have heq : raw6309step0 = raw6309.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6309).symm
    injectiveMoment H raw6309step0 = injectiveMoment H raw6309step1 := by
      have heq : raw6309step1 = -raw6309step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6309step0).symm
    injectiveMoment H raw6309step1 = injectiveMoment H raw6309step2 := by
      have heq : raw6309step2 = (fun i j => raw6309step1 (permutation15 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6309step1 permutation15 permutation24
    _ = injectiveMoment H node1116 := by rfl

def raw6310 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw6310step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical6310 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6310 = injectiveMoment H node936 := by
  calc
    injectiveMoment H raw6310 = injectiveMoment H raw6310step0 := by
      have heq : raw6310step0 = (fun i j => raw6310 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6310 permutation9 permutation11
    _ = injectiveMoment H node936 := by rfl

def raw6311 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw6311step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![-1, -1, 2, 0], ![3, 0, -3, 0]]

def raw6311step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1]]

theorem canonical6311 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6311 = injectiveMoment H node1268 := by
  calc
    injectiveMoment H raw6311 = injectiveMoment H raw6311step0 := by
      have heq : raw6311step0 = raw6311.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6311).symm
    injectiveMoment H raw6311step0 = injectiveMoment H raw6311step1 := by
      have heq : raw6311step1 = (fun i j => raw6311step0 (permutation25 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6311step0 permutation25 permutation19
    _ = injectiveMoment H node1268 := by rfl

def raw6312 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1]]

theorem canonical6312 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6312 = injectiveMoment H node986 := by
  rfl

def raw6313 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -1, 0], ![1, -1, 1, -1], ![0, 1, 1, -2]]

def raw6313step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical6313 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6313 = injectiveMoment H node936 := by
  calc
    injectiveMoment H raw6313 = injectiveMoment H raw6313step0 := by
      have heq : raw6313step0 = (fun i j => raw6313 (permutation10 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6313 permutation10 permutation11
    _ = injectiveMoment H node936 := by rfl

def raw6314 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -1, 0], ![1, -1, 3, -3], ![0, 1, -1, 0]]

def raw6314step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![-1, 1, -1, 1], ![-1, -1, 3, -1], ![3, 0, -3, 0]]

def raw6314step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, 1, -1, -1]]

theorem canonical6314 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6314 = injectiveMoment H node960 := by
  calc
    injectiveMoment H raw6314 = injectiveMoment H raw6314step0 := by
      have heq : raw6314step0 = raw6314.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6314).symm
    injectiveMoment H raw6314step0 = injectiveMoment H raw6314step1 := by
      have heq : raw6314step1 = (fun i j => raw6314step0 (permutation22 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6314step0 permutation22 permutation19
    _ = injectiveMoment H node960 := by rfl

def raw6315 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw6315step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, -1, 2], ![3, 0, -3]]

def raw6315step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical6315 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6315 = injectiveMoment H node285 := by
  calc
    injectiveMoment H raw6315 = injectiveMoment H raw6315step0 := by
      have heq : raw6315step0 = raw6315.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6315).symm
    injectiveMoment H raw6315step0 = injectiveMoment H raw6315step1 := by
      have heq : raw6315step1 = (fun i j => raw6315step0 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6315step0 permutation22 permutation5
    _ = injectiveMoment H node285 := by rfl

def raw6316 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 0, -1], ![0, -1, 2, -1], ![1, 1, -1, -1]]

def raw6316step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

theorem canonical6316 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6316 = injectiveMoment H node942 := by
  calc
    injectiveMoment H raw6316 = injectiveMoment H raw6316step0 := by
      have heq : raw6316step0 = (fun i j => raw6316 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6316 permutation11 permutation9
    _ = injectiveMoment H node942 := by rfl

def raw6317 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 0, -1], ![0, 0, 2, -2], ![1, 0, -1, 0]]

def raw6317step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical6317 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6317 = injectiveMoment H node974 := by
  calc
    injectiveMoment H raw6317 = injectiveMoment H raw6317step0 := by
      have heq : raw6317step0 = (fun i j => raw6317 (permutation12 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6317 permutation12 permutation15
    _ = injectiveMoment H node974 := by rfl

def raw6318 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 0, -1], ![0, 0, 3, -3], ![1, 0, -2, 1]]

def raw6318step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem canonical6318 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6318 = injectiveMoment H node977 := by
  calc
    injectiveMoment H raw6318 = injectiveMoment H raw6318step0 := by
      have heq : raw6318step0 = (fun i j => raw6318 (permutation12 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6318 permutation12 permutation15
    _ = injectiveMoment H node977 := by rfl

def raw6319 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 2, -2]]

def raw6319step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![-1, 0, -1, 2], ![3, -1, 0, -2]]

def raw6319step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![1, -1, -1, 1], ![1, 0, 1, -2], ![-3, 1, 0, 2]]

def raw6319step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

theorem canonical6319 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6319 = injectiveMoment H node1116 := by
  calc
    injectiveMoment H raw6319 = injectiveMoment H raw6319step0 := by
      have heq : raw6319step0 = raw6319.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6319).symm
    injectiveMoment H raw6319step0 = injectiveMoment H raw6319step1 := by
      have heq : raw6319step1 = -raw6319step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6319step0).symm
    injectiveMoment H raw6319step1 = injectiveMoment H raw6319step2 := by
      have heq : raw6319step2 = (fun i j => raw6319step1 (permutation15 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6319step1 permutation15 permutation18
    _ = injectiveMoment H node1116 := by rfl

def raw6320 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw6320step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical6320 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6320 = injectiveMoment H node969 := by
  calc
    injectiveMoment H raw6320 = injectiveMoment H raw6320step0 := by
      have heq : raw6320step0 = (fun i j => raw6320 (permutation10 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6320 permutation10 permutation21
    _ = injectiveMoment H node969 := by rfl

def raw6321 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw6321step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

theorem canonical6321 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6321 = injectiveMoment H node972 := by
  calc
    injectiveMoment H raw6321 = injectiveMoment H raw6321step0 := by
      have heq : raw6321step0 = (fun i j => raw6321 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6321 permutation9 permutation11
    _ = injectiveMoment H node972 := by rfl

def raw6322 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 0, -1], ![1, -1, 1, -1], ![0, 1, 0, -1]]

def raw6322step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, -1, -1]]

theorem canonical6322 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6322 = injectiveMoment H node966 := by
  calc
    injectiveMoment H raw6322 = injectiveMoment H raw6322step0 := by
      have heq : raw6322step0 = (fun i j => raw6322 (permutation10 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6322 permutation10 permutation11
    _ = injectiveMoment H node966 := by rfl

def raw6323 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 0, -1], ![1, -1, 3, -3], ![0, 1, -2, 1]]

def raw6323step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 3, -3]]

theorem canonical6323 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6323 = injectiveMoment H node982 := by
  calc
    injectiveMoment H raw6323 = injectiveMoment H raw6323step0 := by
      have heq : raw6323step0 = (fun i j => raw6323 (permutation13 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6323 permutation13 permutation9
    _ = injectiveMoment H node982 := by rfl

def raw6324 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw6324step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![3, -1, -2]]

def raw6324step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical6324 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6324 = injectiveMoment H node271 := by
  calc
    injectiveMoment H raw6324 = injectiveMoment H raw6324step0 := by
      have heq : raw6324step0 = raw6324.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6324).symm
    injectiveMoment H raw6324step0 = injectiveMoment H raw6324step1 := by
      have heq : raw6324step1 = (fun i j => raw6324step0 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6324step0 permutation28 permutation6
    _ = injectiveMoment H node271 := by rfl

def raw6325 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

theorem canonical6325 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6325 = injectiveMoment H node987 := by
  rfl

def raw6326 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw6326step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 1, 0], ![3, -2, -1]]

def raw6326step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical6326 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6326 = injectiveMoment H node271 := by
  calc
    injectiveMoment H raw6326 = injectiveMoment H raw6326step0 := by
      have heq : raw6326step0 = raw6326.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6326).symm
    injectiveMoment H raw6326step0 = injectiveMoment H raw6326step1 := by
      have heq : raw6326step1 = (fun i j => raw6326step0 (permutation30 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6326step0 permutation30 permutation8
    _ = injectiveMoment H node271 := by rfl

def raw6327 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 2, -3], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def raw6327step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![-1, 2, -1, 0], ![3, -3, 0, 0]]

def raw6327step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1]]

theorem canonical6327 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6327 = injectiveMoment H node1268 := by
  calc
    injectiveMoment H raw6327 = injectiveMoment H raw6327step0 := by
      have heq : raw6327step0 = raw6327.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6327).symm
    injectiveMoment H raw6327step0 = injectiveMoment H raw6327step1 := by
      have heq : raw6327step1 = (fun i j => raw6327step0 (permutation25 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6327step0 permutation25 permutation25
    _ = injectiveMoment H node1268 := by rfl

def raw6328 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw6328step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 2, -1], ![3, -3, 0]]

def raw6328step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical6328 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6328 = injectiveMoment H node285 := by
  calc
    injectiveMoment H raw6328 = injectiveMoment H raw6328step0 := by
      have heq : raw6328step0 = raw6328.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6328).symm
    injectiveMoment H raw6328step0 = injectiveMoment H raw6328step1 := by
      have heq : raw6328step1 = (fun i j => raw6328step0 (permutation24 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6328step0 permutation24 permutation7
    _ = injectiveMoment H node285 := by rfl

def raw6329 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, 3, -4], ![1, 0, -2, 1]]

def raw6329step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 3, -2], ![3, -4, 1]]

def raw6329step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical6329 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6329 = injectiveMoment H node173 := by
  calc
    injectiveMoment H raw6329 = injectiveMoment H raw6329step0 := by
      have heq : raw6329step0 = raw6329.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6329).symm
    injectiveMoment H raw6329step0 = injectiveMoment H raw6329step1 := by
      have heq : raw6329step1 = (fun i j => raw6329step0 (permutation23 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6329step0 permutation23 permutation7
    _ = injectiveMoment H node173 := by rfl

def raw6330 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 2, -2, 0], ![1, -1, 3, -3]]

def raw6330step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![-1, -2, 3], ![3, 0, -3]]

def raw6330step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

theorem canonical6330 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6330 = injectiveMoment H node170 := by
  calc
    injectiveMoment H raw6330 = injectiveMoment H raw6330step0 := by
      have heq : raw6330step0 = raw6330.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6330).symm
    injectiveMoment H raw6330step0 = injectiveMoment H raw6330step1 := by
      have heq : raw6330step1 = (fun i j => raw6330step0 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6330step0 permutation22 permutation5
    _ = injectiveMoment H node170 := by rfl

def raw6331 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 2, -1, -1], ![1, -1, 2, -2]]

def raw6331step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![-1, -1, 2], ![3, -1, -2]]

def raw6331step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![1, 1, -2], ![-3, 1, 2]]

def raw6331step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical6331 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6331 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw6331 = injectiveMoment H raw6331step0 := by
      have heq : raw6331step0 = raw6331.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6331).symm
    injectiveMoment H raw6331step0 = injectiveMoment H raw6331step1 := by
      have heq : raw6331step1 = -raw6331step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6331step0).symm
    injectiveMoment H raw6331step1 = injectiveMoment H raw6331step2 := by
      have heq : raw6331step2 = (fun i j => raw6331step1 (permutation15 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6331step1 permutation15 permutation6
    _ = injectiveMoment H node229 := by rfl

def raw6332 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def raw6332step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![-1, 1, 0], ![3, -3, 0]]

def raw6332step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical6332 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6332 = injectiveMoment H node285 := by
  calc
    injectiveMoment H raw6332 = injectiveMoment H raw6332step0 := by
      have heq : raw6332step0 = raw6332.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6332).symm
    injectiveMoment H raw6332step0 = injectiveMoment H raw6332step1 := by
      have heq : raw6332step1 = (fun i j => raw6332step0 (permutation18 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6332step0 permutation18 permutation7
    _ = injectiveMoment H node285 := by rfl

def raw6333 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def raw6333step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![-1, 2, -1], ![3, -4, 1]]

def raw6333step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![1, -2, 1], ![-3, 4, -1]]

def raw6333step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

theorem canonical6333 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6333 = injectiveMoment H node244 := by
  calc
    injectiveMoment H raw6333 = injectiveMoment H raw6333step0 := by
      have heq : raw6333step0 = raw6333.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6333).symm
    injectiveMoment H raw6333step0 = injectiveMoment H raw6333step1 := by
      have heq : raw6333step1 = -raw6333step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6333step0).symm
    injectiveMoment H raw6333step1 = injectiveMoment H raw6333step2 := by
      have heq : raw6333step2 = (fun i j => raw6333step1 (permutation27 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6333step1 permutation27 permutation7
    _ = injectiveMoment H node244 := by rfl

def raw6334 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![1, -1, 1, -1], ![0, 2, 0, -2]]

def raw6334step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![3, -1, -2]]

def raw6334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical6334 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6334 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw6334 = injectiveMoment H raw6334step0 := by
      have heq : raw6334step0 = raw6334.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6334).symm
    injectiveMoment H raw6334step0 = injectiveMoment H raw6334step1 := by
      have heq : raw6334step1 = (fun i j => raw6334step0 (permutation28 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6334step0 permutation28 permutation8
    _ = injectiveMoment H node176 := by rfl

def raw6335 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![1, -1, 2, -2], ![0, 2, -1, -1]]

def raw6335step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 2, -1], ![3, -2, -1]]

def raw6335step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 1, -2], ![1, -2, 1], ![-3, 2, 1]]

def raw6335step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical6335 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6335 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw6335 = injectiveMoment H raw6335step0 := by
      have heq : raw6335step0 = raw6335.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6335).symm
    injectiveMoment H raw6335step0 = injectiveMoment H raw6335step1 := by
      have heq : raw6335step1 = -raw6335step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6335step0).symm
    injectiveMoment H raw6335step1 = injectiveMoment H raw6335step2 := by
      have heq : raw6335step2 = (fun i j => raw6335step1 (permutation15 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6335step1 permutation15 permutation8
    _ = injectiveMoment H node229 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

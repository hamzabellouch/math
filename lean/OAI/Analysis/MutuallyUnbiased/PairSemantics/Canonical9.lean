import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw288 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

theorem canonical288 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw288 = injectiveMoment H node317 := by
  rfl

def raw289 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]

theorem canonical289 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw289 = injectiveMoment H node81 := by
  rfl

def raw290 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical290 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw290 = injectiveMoment H node318 := by
  rfl

def raw291 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical291 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw291 = injectiveMoment H node319 := by
  rfl

def raw292 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]

theorem canonical292 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw292 = injectiveMoment H node82 := by
  rfl

def raw293 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

theorem canonical293 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw293 = injectiveMoment H node320 := by
  rfl

def raw294 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical294 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw294 = injectiveMoment H node737 := by
  calc
    injectiveMoment H raw294 = injectiveMoment H raw294step0 := by
      have heq : raw294step0 = (fun i j => raw294 (permutation41 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw294 permutation41 permutation5
    _ = injectiveMoment H node737 := by rfl

def raw295 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw295step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3]]

theorem canonical295 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw295 = injectiveMoment H node243 := by
  calc
    injectiveMoment H raw295 = injectiveMoment H raw295step0 := by
      have heq : raw295step0 = (fun i j => raw295 (permutation11 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw295 permutation11 permutation5
    _ = injectiveMoment H node243 := by rfl

def raw296 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]

def raw296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical296 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw296 = injectiveMoment H node737 := by
  calc
    injectiveMoment H raw296 = injectiveMoment H raw296step0 := by
      have heq : raw296step0 = (fun i j => raw296 (permutation47 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw296 permutation47 permutation5
    _ = injectiveMoment H node737 := by rfl

def raw297 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

def raw297step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical297 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw297 = injectiveMoment H node246 := by
  calc
    injectiveMoment H raw297 = injectiveMoment H raw297step0 := by
      have heq : raw297step0 = (fun i j => raw297 (permutation13 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw297 permutation13 permutation5
    _ = injectiveMoment H node246 := by rfl

def raw298 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]

theorem canonical298 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw298 = injectiveMoment H node83 := by
  rfl

def raw299 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def raw299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

theorem canonical299 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw299 = injectiveMoment H node315 := by
  calc
    injectiveMoment H raw299 = injectiveMoment H raw299step0 := by
      have heq : raw299step0 = (fun i j => raw299 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw299 permutation39 permutation3
    _ = injectiveMoment H node315 := by rfl

def raw300 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def raw300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]

theorem canonical300 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw300 = injectiveMoment H node316 := by
  calc
    injectiveMoment H raw300 = injectiveMoment H raw300step0 := by
      have heq : raw300step0 = (fun i j => raw300 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw300 permutation39 permutation3
    _ = injectiveMoment H node316 := by rfl

def raw301 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def raw301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

theorem canonical301 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw301 = injectiveMoment H node317 := by
  calc
    injectiveMoment H raw301 = injectiveMoment H raw301step0 := by
      have heq : raw301step0 = (fun i j => raw301 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw301 permutation39 permutation3
    _ = injectiveMoment H node317 := by rfl

def raw302 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![3, -2, -1]]

def raw302step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]

theorem canonical302 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw302 = injectiveMoment H node81 := by
  calc
    injectiveMoment H raw302 = injectiveMoment H raw302step0 := by
      have heq : raw302step0 = (fun i j => raw302 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw302 permutation11 permutation3
    _ = injectiveMoment H node81 := by rfl

def raw303 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical303 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw303 = injectiveMoment H node321 := by
  rfl

def raw304 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

theorem canonical304 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw304 = injectiveMoment H node84 := by
  rfl

def raw305 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

theorem canonical305 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw305 = injectiveMoment H node322 := by
  rfl

def raw306 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical306 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw306 = injectiveMoment H node653 := by
  calc
    injectiveMoment H raw306 = injectiveMoment H raw306step0 := by
      have heq : raw306step0 = -raw306 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw306).symm
    injectiveMoment H raw306step0 = injectiveMoment H raw306step1 := by
      have heq : raw306step1 = (fun i j => raw306step0 (permutation73 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw306step0 permutation73 permutation5
    _ = injectiveMoment H node653 := by rfl

def raw307 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def raw307step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]

def raw307step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

theorem canonical307 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw307 = injectiveMoment H node201 := by
  calc
    injectiveMoment H raw307 = injectiveMoment H raw307step0 := by
      have heq : raw307step0 = -raw307 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw307).symm
    injectiveMoment H raw307step0 = injectiveMoment H raw307step1 := by
      have heq : raw307step1 = (fun i j => raw307step0 (permutation20 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw307step0 permutation20 permutation5
    _ = injectiveMoment H node201 := by rfl

def raw308 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]

def raw308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1]]

def raw308step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical308 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw308 = injectiveMoment H node653 := by
  calc
    injectiveMoment H raw308 = injectiveMoment H raw308step0 := by
      have heq : raw308step0 = -raw308 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw308).symm
    injectiveMoment H raw308step0 = injectiveMoment H raw308step1 := by
      have heq : raw308step1 = (fun i j => raw308step0 (permutation67 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw308step0 permutation67 permutation5
    _ = injectiveMoment H node653 := by rfl

def raw309 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def raw309step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]

def raw309step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

theorem canonical309 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw309 = injectiveMoment H node206 := by
  calc
    injectiveMoment H raw309 = injectiveMoment H raw309step0 := by
      have heq : raw309step0 = -raw309 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw309).symm
    injectiveMoment H raw309step0 = injectiveMoment H raw309step1 := by
      have heq : raw309step1 = (fun i j => raw309step0 (permutation18 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw309step0 permutation18 permutation5
    _ = injectiveMoment H node206 := by rfl

def raw310 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

theorem canonical310 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw310 = injectiveMoment H node85 := by
  rfl

def raw311 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![2, -2, 0], ![1, 1, -2]]

def raw311step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

theorem canonical311 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw311 = injectiveMoment H node85 := by
  calc
    injectiveMoment H raw311 = injectiveMoment H raw311step0 := by
      have heq : raw311step0 = (fun i j => raw311 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw311 permutation10 permutation3
    _ = injectiveMoment H node85 := by rfl

def raw312 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]

def raw312step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![4, -2, -2]]

def raw312step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

theorem canonical312 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw312 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw312 = injectiveMoment H raw312step0 := by
      have heq : raw312step0 = raw312.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw312).symm
    injectiveMoment H raw312step0 = injectiveMoment H raw312step1 := by
      have heq : raw312step1 = (fun i j => raw312step0 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw312step0 permutation7 permutation6
    _ = injectiveMoment H node32 := by rfl

def raw313 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical313 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw313 = injectiveMoment H node323 := by
  rfl

def raw314 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]

theorem canonical314 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw314 = injectiveMoment H node86 := by
  rfl

def raw315 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

theorem canonical315 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw315 = injectiveMoment H node324 := by
  rfl

def raw316 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]

def raw316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

theorem canonical316 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw316 = injectiveMoment H node324 := by
  calc
    injectiveMoment H raw316 = injectiveMoment H raw316step0 := by
      have heq : raw316step0 = (fun i j => raw316 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw316 permutation34 permutation3
    _ = injectiveMoment H node324 := by rfl

def raw317 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]

theorem canonical317 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw317 = injectiveMoment H node87 := by
  rfl

def raw318 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]

theorem canonical318 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw318 = injectiveMoment H node88 := by
  rfl

def raw319 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![2, -2, 0], ![1, 0, -1]]

def raw319step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]

theorem canonical319 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw319 = injectiveMoment H node88 := by
  calc
    injectiveMoment H raw319 = injectiveMoment H raw319step0 := by
      have heq : raw319step0 = (fun i j => raw319 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw319 permutation10 permutation3
    _ = injectiveMoment H node88 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

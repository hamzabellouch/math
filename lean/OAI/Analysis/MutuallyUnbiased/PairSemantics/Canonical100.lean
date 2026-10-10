import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes31

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3200 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw3200step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-1, -1, 0, 2], ![3, 0, -1, -2]]

def raw3200step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![1, 1, 0, -2], ![-3, 0, 1, 2]]

def raw3200step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -3, 2], ![1, 0, 1, -2]]

theorem canonical3200 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3200 = injectiveMoment H node1052 := by
  calc
    injectiveMoment H raw3200 = injectiveMoment H raw3200step0 := by
      have heq : raw3200step0 = raw3200.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3200).symm
    injectiveMoment H raw3200step0 = injectiveMoment H raw3200step1 := by
      have heq : raw3200step1 = -raw3200step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3200step0).symm
    injectiveMoment H raw3200step1 = injectiveMoment H raw3200step2 := by
      have heq : raw3200step2 = (fun i j => raw3200step1 (permutation16 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3200step1 permutation16 permutation17
    _ = injectiveMoment H node1052 := by rfl

def raw3201 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def raw3201step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem canonical3201 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3201 = injectiveMoment H node1641 := by
  calc
    injectiveMoment H raw3201 = injectiveMoment H raw3201step0 := by
      have heq : raw3201step0 = (fun i j => raw3201 (permutation34 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3201 permutation34 permutation11
    _ = injectiveMoment H node1641 := by rfl

def raw3202 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

theorem canonical3202 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3202 = injectiveMoment H node1982 := by
  rfl

def raw3203 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 2, -2]]

theorem canonical3203 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3203 = injectiveMoment H node1983 := by
  rfl

def raw3204 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def raw3204step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-1, -1, 1, 1], ![3, 0, -2, -1]]

def raw3204step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![1, 1, -1, -1], ![-3, 0, 2, 1]]

def raw3204step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

theorem canonical3204 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3204 = injectiveMoment H node1056 := by
  calc
    injectiveMoment H raw3204 = injectiveMoment H raw3204step0 := by
      have heq : raw3204step0 = raw3204.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3204).symm
    injectiveMoment H raw3204step0 = injectiveMoment H raw3204step1 := by
      have heq : raw3204step1 = -raw3204step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3204step0).symm
    injectiveMoment H raw3204step1 = injectiveMoment H raw3204step2 := by
      have heq : raw3204step2 = (fun i j => raw3204step1 (permutation16 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3204step1 permutation16 permutation17
    _ = injectiveMoment H node1056 := by rfl

def raw3205 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 0, -1, 0]]

theorem canonical3205 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3205 = injectiveMoment H node1984 := by
  rfl

def raw3206 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 1, -1]]

theorem canonical3206 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3206 = injectiveMoment H node1985 := by
  rfl

def raw3207 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3207step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem canonical3207 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3207 = injectiveMoment H node1644 := by
  calc
    injectiveMoment H raw3207 = injectiveMoment H raw3207step0 := by
      have heq : raw3207step0 = (fun i j => raw3207 (permutation33 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3207 permutation33 permutation11
    _ = injectiveMoment H node1644 := by rfl

def raw3208 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -2, 0, 0]]

def raw3208step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-1, -1, 2, 0], ![3, 0, -3, 0]]

def raw3208step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -2, 0, 1]]

theorem canonical3208 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3208 = injectiveMoment H node1269 := by
  calc
    injectiveMoment H raw3208 = injectiveMoment H raw3208step0 := by
      have heq : raw3208step0 = raw3208.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3208).symm
    injectiveMoment H raw3208step0 = injectiveMoment H raw3208step1 := by
      have heq : raw3208step1 = (fun i j => raw3208step0 (permutation25 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3208step0 permutation25 permutation19
    _ = injectiveMoment H node1269 := by rfl

def raw3209 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

theorem canonical3209 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3209 = injectiveMoment H node1986 := by
  rfl

def raw3210 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem canonical3210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3210 = injectiveMoment H node1987 := by
  rfl

def raw3211 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw3211step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem canonical3211 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3211 = injectiveMoment H node1987 := by
  calc
    injectiveMoment H raw3211 = injectiveMoment H raw3211step0 := by
      have heq : raw3211step0 = (fun i j => raw3211 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3211 permutation34 permutation9
    _ = injectiveMoment H node1987 := by rfl

def raw3212 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, -2, -1, 1]]

def raw3212step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-1, -1, 3, -1], ![3, 0, -4, 1]]

def raw3212step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -2, 2, 0], ![0, 3, 1, -4], ![1, 0, -2, 1]]

theorem canonical3212 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3212 = injectiveMoment H node929 := by
  calc
    injectiveMoment H raw3212 = injectiveMoment H raw3212step0 := by
      have heq : raw3212step0 = raw3212.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3212).symm
    injectiveMoment H raw3212step0 = injectiveMoment H raw3212step1 := by
      have heq : raw3212step1 = (fun i j => raw3212step0 (permutation22 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3212step0 permutation22 permutation16
    _ = injectiveMoment H node929 := by rfl

def raw3213 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def raw3213step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![-1, -1, 0, 2], ![3, 0, 1, -4]]

def raw3213step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem canonical3213 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3213 = injectiveMoment H node1278 := by
  calc
    injectiveMoment H raw3213 = injectiveMoment H raw3213step0 := by
      have heq : raw3213step0 = raw3213.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3213).symm
    injectiveMoment H raw3213step0 = injectiveMoment H raw3213step1 := by
      have heq : raw3213step1 = (fun i j => raw3213step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3213step0 permutation22 permutation17
    _ = injectiveMoment H node1278 := by rfl

def raw3214 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw3214step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![-1, -1, 1, 1], ![3, 0, 0, -3]]

def raw3214step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -2, 0, 1]]

theorem canonical3214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3214 = injectiveMoment H node1352 := by
  calc
    injectiveMoment H raw3214 = injectiveMoment H raw3214step0 := by
      have heq : raw3214step0 = raw3214.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3214).symm
    injectiveMoment H raw3214step0 = injectiveMoment H raw3214step1 := by
      have heq : raw3214step1 = (fun i j => raw3214step0 (permutation25 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3214step0 permutation25 permutation17
    _ = injectiveMoment H node1352 := by rfl

def raw3215 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 1, 0, -2]]

def raw3215step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![-1, -1, 2, 0], ![3, 0, -1, -2]]

def raw3215step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![1, 1, -2, 0], ![-3, 0, 1, 2]]

def raw3215step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![1, 0, 1, -2]]

theorem canonical3215 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3215 = injectiveMoment H node1007 := by
  calc
    injectiveMoment H raw3215 = injectiveMoment H raw3215step0 := by
      have heq : raw3215step0 = raw3215.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3215).symm
    injectiveMoment H raw3215step0 = injectiveMoment H raw3215step1 := by
      have heq : raw3215step1 = -raw3215step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3215step0).symm
    injectiveMoment H raw3215step1 = injectiveMoment H raw3215step2 := by
      have heq : raw3215step2 = (fun i j => raw3215step1 (permutation16 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3215step1 permutation16 permutation19
    _ = injectiveMoment H node1007 := by rfl

def raw3216 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 1, -1, -1]]

def raw3216step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![-1, -1, 3, -1], ![3, 0, -2, -1]]

def raw3216step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem canonical3216 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3216 = injectiveMoment H node948 := by
  calc
    injectiveMoment H raw3216 = injectiveMoment H raw3216step0 := by
      have heq : raw3216step0 = raw3216.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3216).symm
    injectiveMoment H raw3216step0 = injectiveMoment H raw3216step1 := by
      have heq : raw3216step1 = (fun i j => raw3216step0 (permutation25 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3216step0 permutation25 permutation19
    _ = injectiveMoment H node948 := by rfl

def raw3217 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw3217step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-1, -1, -1, 3], ![3, 0, 1, -4]]

def raw3217step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem canonical3217 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3217 = injectiveMoment H node985 := by
  calc
    injectiveMoment H raw3217 = injectiveMoment H raw3217step0 := by
      have heq : raw3217step0 = raw3217.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3217).symm
    injectiveMoment H raw3217step0 = injectiveMoment H raw3217step1 := by
      have heq : raw3217step1 = (fun i j => raw3217step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3217step0 permutation22 permutation17
    _ = injectiveMoment H node985 := by rfl

def raw3218 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw3218step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-1, -1, 0, 2], ![3, 0, 0, -3]]

def raw3218step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0]]

theorem canonical3218 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3218 = injectiveMoment H node1267 := by
  calc
    injectiveMoment H raw3218 = injectiveMoment H raw3218step0 := by
      have heq : raw3218step0 = raw3218.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3218).symm
    injectiveMoment H raw3218step0 = injectiveMoment H raw3218step1 := by
      have heq : raw3218step1 = (fun i j => raw3218step0 (permutation25 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3218step0 permutation25 permutation17
    _ = injectiveMoment H node1267 := by rfl

def raw3219 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw3219step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![-1, 0, -1, 2]]

def raw3219step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, -1, -1, 1]]

theorem canonical3219 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3219 = injectiveMoment H node1299 := by
  calc
    injectiveMoment H raw3219 = injectiveMoment H raw3219step0 := by
      have heq : raw3219step0 = -raw3219 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3219).symm
    injectiveMoment H raw3219step0 = injectiveMoment H raw3219step1 := by
      have heq : raw3219step1 = (fun i j => raw3219step0 (permutation19 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3219step0 permutation19 permutation15
    _ = injectiveMoment H node1299 := by rfl

def raw3220 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw3220step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-1, -1, 2, 0], ![3, 0, -2, -1]]

def raw3220step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical3220 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3220 = injectiveMoment H node1206 := by
  calc
    injectiveMoment H raw3220 = injectiveMoment H raw3220step0 := by
      have heq : raw3220step0 = raw3220.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3220).symm
    injectiveMoment H raw3220step0 = injectiveMoment H raw3220step1 := by
      have heq : raw3220step1 = (fun i j => raw3220step0 (permutation32 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3220step0 permutation32 permutation30
    _ = injectiveMoment H node1206 := by rfl

def raw3221 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw3221step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-1, -1, 3, -1], ![3, 0, -3, 0]]

def raw3221step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem canonical3221 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3221 = injectiveMoment H node977 := by
  calc
    injectiveMoment H raw3221 = injectiveMoment H raw3221step0 := by
      have heq : raw3221step0 = raw3221.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3221).symm
    injectiveMoment H raw3221step0 = injectiveMoment H raw3221step1 := by
      have heq : raw3221step1 = (fun i j => raw3221step0 (permutation25 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3221step0 permutation25 permutation19
    _ = injectiveMoment H node977 := by rfl

def raw3222 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, -1, 3, -3]]

def raw3222step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![-1, -1, -1, 3], ![3, 0, 0, -3]]

def raw3222step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem canonical3222 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3222 = injectiveMoment H node977 := by
  calc
    injectiveMoment H raw3222 = injectiveMoment H raw3222step0 := by
      have heq : raw3222step0 = raw3222.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3222).symm
    injectiveMoment H raw3222step0 = injectiveMoment H raw3222step1 := by
      have heq : raw3222step1 = (fun i j => raw3222step0 (permutation25 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3222step0 permutation25 permutation17
    _ = injectiveMoment H node977 := by rfl

def raw3223 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, -1, 2, -2]]

def raw3223step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![-1, -1, 0, 2], ![3, 0, -1, -2]]

def raw3223step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical3223 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3223 = injectiveMoment H node1206 := by
  calc
    injectiveMoment H raw3223 = injectiveMoment H raw3223step0 := by
      have heq : raw3223step0 = raw3223.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3223).symm
    injectiveMoment H raw3223step0 = injectiveMoment H raw3223step1 := by
      have heq : raw3223step1 = (fun i j => raw3223step0 (permutation32 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3223step0 permutation32 permutation24
    _ = injectiveMoment H node1206 := by rfl

def raw3224 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 1, -2]]

def raw3224step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem canonical3224 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3224 = injectiveMoment H node1636 := by
  calc
    injectiveMoment H raw3224 = injectiveMoment H raw3224step0 := by
      have heq : raw3224step0 = (fun i j => raw3224 (permutation39 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3224 permutation39 permutation11
    _ = injectiveMoment H node1636 := by rfl

def raw3225 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw3225step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

theorem canonical3225 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3225 = injectiveMoment H node1635 := by
  calc
    injectiveMoment H raw3225 = injectiveMoment H raw3225step0 := by
      have heq : raw3225step0 = (fun i j => raw3225 (permutation40 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3225 permutation40 permutation11
    _ = injectiveMoment H node1635 := by rfl

def raw3226 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw3226step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

theorem canonical3226 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3226 = injectiveMoment H node1634 := by
  calc
    injectiveMoment H raw3226 = injectiveMoment H raw3226step0 := by
      have heq : raw3226step0 = (fun i j => raw3226 (permutation39 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3226 permutation39 permutation11
    _ = injectiveMoment H node1634 := by rfl

def raw3227 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw3227step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-1, 0, -1, 2], ![3, -1, 0, -2]]

def raw3227step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![1, 0, 1, -2], ![-3, 1, 0, 2]]

def raw3227step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -3, 2], ![1, 0, 1, -2]]

theorem canonical3227 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3227 = injectiveMoment H node1052 := by
  calc
    injectiveMoment H raw3227 = injectiveMoment H raw3227step0 := by
      have heq : raw3227step0 = raw3227.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3227).symm
    injectiveMoment H raw3227step0 = injectiveMoment H raw3227step1 := by
      have heq : raw3227step1 = -raw3227step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3227step0).symm
    injectiveMoment H raw3227step1 = injectiveMoment H raw3227step2 := by
      have heq : raw3227step2 = (fun i j => raw3227step1 (permutation16 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3227step1 permutation16 permutation23
    _ = injectiveMoment H node1052 := by rfl

def raw3228 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw3228step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -2, -1]]

theorem canonical3228 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3228 = injectiveMoment H node1674 := by
  calc
    injectiveMoment H raw3228 = injectiveMoment H raw3228step0 := by
      have heq : raw3228step0 = (fun i j => raw3228 (permutation34 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3228 permutation34 permutation11
    _ = injectiveMoment H node1674 := by rfl

def raw3229 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def raw3229step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 2, -1, -2]]

theorem canonical3229 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3229 = injectiveMoment H node1673 := by
  calc
    injectiveMoment H raw3229 = injectiveMoment H raw3229step0 := by
      have heq : raw3229step0 = (fun i j => raw3229 (permutation33 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3229 permutation33 permutation11
    _ = injectiveMoment H node1673 := by rfl

def raw3230 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw3230step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical3230 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3230 = injectiveMoment H node1686 := by
  calc
    injectiveMoment H raw3230 = injectiveMoment H raw3230step0 := by
      have heq : raw3230step0 = (fun i j => raw3230 (permutation34 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3230 permutation34 permutation11
    _ = injectiveMoment H node1686 := by rfl

def raw3231 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw3231step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 0, 1], ![0, -1, -2, 3], ![-1, 1, 1, -1], ![-1, 1, 0, 0]]

def raw3231step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, 2, -3], ![1, 1, -1, -1]]

theorem canonical3231 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3231 = injectiveMoment H node1624 := by
  calc
    injectiveMoment H raw3231 = injectiveMoment H raw3231step0 := by
      have heq : raw3231step0 = -raw3231 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3231).symm
    injectiveMoment H raw3231step0 = injectiveMoment H raw3231step1 := by
      have heq : raw3231step1 = (fun i j => raw3231step0 (permutation90 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3231step0 permutation90 permutation23
    _ = injectiveMoment H node1624 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

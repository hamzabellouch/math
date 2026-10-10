import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes53

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw10048 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, 0, -1, 2], ![-1, -1, 3, -1]]

def raw10048step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 0, 1, -2], ![1, 1, -3, 1]]

def raw10048step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem canonical10048 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw10048 = injectiveMoment H node3203 := by
  calc
    injectiveMoment H raw10048 = injectiveMoment H raw10048step0 := by
      have heq : raw10048step0 = -raw10048 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw10048).symm
    injectiveMoment H raw10048step0 = injectiveMoment H raw10048step1 := by
      have heq : raw10048step1 = (fun i j => raw10048step0 (permutation272 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10048step0 permutation272 permutation29
    _ = injectiveMoment H node3203 := by rfl

def raw10049 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, -1, -1, 2], ![-2, 0, 3, -1]]

def raw10049step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical10049 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10049 = injectiveMoment H node2969 := by
  calc
    injectiveMoment H raw10049 = injectiveMoment H raw10049step0 := by
      have heq : raw10049step0 = (fun i j => raw10049 (permutation335 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10049 permutation335 permutation13
    _ = injectiveMoment H node2969 := by rfl

def raw10050 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, -2, 4], ![0, -1, 3, -2]]

def raw10050step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical10050 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10050 = injectiveMoment H node3116 := by
  calc
    injectiveMoment H raw10050 = injectiveMoment H raw10050step0 := by
      have heq : raw10050step0 = (fun i j => raw10050 (permutation294 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10050 permutation294 permutation9
    _ = injectiveMoment H node3116 := by rfl

def raw10051 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, -1, 3], ![0, -1, 2, -1]]

def raw10051step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical10051 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10051 = injectiveMoment H node2969 := by
  calc
    injectiveMoment H raw10051 = injectiveMoment H raw10051step0 := by
      have heq : raw10051step0 = (fun i j => raw10051 (permutation262 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10051 permutation262 permutation11
    _ = injectiveMoment H node2969 := by rfl

def raw10052 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, 3, -1], ![0, -1, -2, 3]]

def raw10052step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical10052 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10052 = injectiveMoment H node3130 := by
  calc
    injectiveMoment H raw10052 = injectiveMoment H raw10052step0 := by
      have heq : raw10052step0 = (fun i j => raw10052 (permutation298 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10052 permutation298 permutation10
    _ = injectiveMoment H node3130 := by rfl

def raw10053 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -2, 4], ![-1, 0, 3, -2]]

def raw10053step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical10053 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10053 = injectiveMoment H node3344 := by
  calc
    injectiveMoment H raw10053 = injectiveMoment H raw10053step0 := by
      have heq : raw10053step0 = (fun i j => raw10053 (permutation294 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10053 permutation294 permutation9
    _ = injectiveMoment H node3344 := by rfl

def raw10054 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 0, 2, -1]]

def raw10054step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 1, -3], ![1, 0, -2, 1]]

def raw10054step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem canonical10054 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw10054 = injectiveMoment H node3203 := by
  calc
    injectiveMoment H raw10054 = injectiveMoment H raw10054step0 := by
      have heq : raw10054step0 = -raw10054 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw10054).symm
    injectiveMoment H raw10054step0 = injectiveMoment H raw10054step1 := by
      have heq : raw10054step1 = (fun i j => raw10054step0 (permutation345 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10054step0 permutation345 permutation23
    _ = injectiveMoment H node3203 := by rfl

def raw10055 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 3, -1], ![-1, 0, -2, 3]]

def raw10055step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical10055 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10055 = injectiveMoment H node3364 := by
  calc
    injectiveMoment H raw10055 = injectiveMoment H raw10055step0 := by
      have heq : raw10055step0 = (fun i j => raw10055 (permutation298 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10055 permutation298 permutation10
    _ = injectiveMoment H node3364 := by rfl

def raw10056 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 0, -2, 3], ![-1, -1, 3, -1]]

def raw10056step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical10056 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10056 = injectiveMoment H node3364 := by
  calc
    injectiveMoment H raw10056 = injectiveMoment H raw10056step0 := by
      have heq : raw10056step0 = (fun i j => raw10056 (permutation398 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10056 permutation398 permutation10
    _ = injectiveMoment H node3364 := by rfl

def raw10057 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 0, -1, 2], ![-1, -1, 2, 0]]

def raw10057step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw10057step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical10057 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw10057 = injectiveMoment H node3210 := by
  calc
    injectiveMoment H raw10057 = injectiveMoment H raw10057step0 := by
      have heq : raw10057step0 = -raw10057 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw10057).symm
    injectiveMoment H raw10057step0 = injectiveMoment H raw10057step1 := by
      have heq : raw10057step1 = (fun i j => raw10057step0 (permutation268 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10057step0 permutation268 permutation29
    _ = injectiveMoment H node3210 := by rfl

def raw10058 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 0, 2, -1], ![-1, -2, 0, 3]]

def raw10058step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical10058 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10058 = injectiveMoment H node2977 := by
  calc
    injectiveMoment H raw10058 = injectiveMoment H raw10058step0 := by
      have heq : raw10058step0 = (fun i j => raw10058 (permutation404 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10058 permutation404 permutation15
    _ = injectiveMoment H node2977 := by rfl

def raw10059 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, -1, 0, 3]]

def raw10059step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical10059 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10059 = injectiveMoment H node2977 := by
  calc
    injectiveMoment H raw10059 = injectiveMoment H raw10059step0 := by
      have heq : raw10059step0 = (fun i j => raw10059 (permutation395 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10059 permutation395 permutation9
    _ = injectiveMoment H node2977 := by rfl

def raw10060 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, 0, -1, 2], ![-1, -1, 3, -1]]

def raw10060step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 0, 1, -2], ![1, 1, -3, 1]]

def raw10060step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem canonical10060 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw10060 = injectiveMoment H node3203 := by
  calc
    injectiveMoment H raw10060 = injectiveMoment H raw10060step0 := by
      have heq : raw10060step0 = -raw10060 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw10060).symm
    injectiveMoment H raw10060step0 = injectiveMoment H raw10060step1 := by
      have heq : raw10060step1 = (fun i j => raw10060step0 (permutation281 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10060step0 permutation281 permutation29
    _ = injectiveMoment H node3203 := by rfl

def raw10061 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, -1, -1, 2], ![-2, 0, 3, -1]]

def raw10061step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical10061 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10061 = injectiveMoment H node2969 := by
  calc
    injectiveMoment H raw10061 = injectiveMoment H raw10061step0 := by
      have heq : raw10061step0 = (fun i j => raw10061 (permutation312 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10061 permutation312 permutation13
    _ = injectiveMoment H node2969 := by rfl

def raw10062 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, 3, -1], ![0, -1, -2, 3]]

def raw10062step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical10062 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10062 = injectiveMoment H node3130 := by
  calc
    injectiveMoment H raw10062 = injectiveMoment H raw10062step0 := by
      have heq : raw10062step0 = (fun i j => raw10062 (permutation294 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10062 permutation294 permutation10
    _ = injectiveMoment H node3130 := by rfl

def raw10063 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 3, -1], ![-1, 0, -2, 3]]

def raw10063step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical10063 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10063 = injectiveMoment H node3364 := by
  calc
    injectiveMoment H raw10063 = injectiveMoment H raw10063step0 := by
      have heq : raw10063step0 = (fun i j => raw10063 (permutation294 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10063 permutation294 permutation10
    _ = injectiveMoment H node3364 := by rfl

def raw10064 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 0, 2, -1], ![-1, -2, 0, 3]]

def raw10064step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical10064 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10064 = injectiveMoment H node2977 := by
  calc
    injectiveMoment H raw10064 = injectiveMoment H raw10064step0 := by
      have heq : raw10064step0 = (fun i j => raw10064 (permutation405 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10064 permutation405 permutation15
    _ = injectiveMoment H node2977 := by rfl

def raw10065 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, -1, 0, 3]]

def raw10065step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

theorem canonical10065 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10065 = injectiveMoment H node2977 := by
  calc
    injectiveMoment H raw10065 = injectiveMoment H raw10065step0 := by
      have heq : raw10065step0 = (fun i j => raw10065 (permutation398 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10065 permutation398 permutation9
    _ = injectiveMoment H node2977 := by rfl

def raw10066 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![-1, 0, -1, 2], ![-1, -1, 3, -1]]

def raw10066step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical10066 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10066 = injectiveMoment H node3358 := by
  calc
    injectiveMoment H raw10066 = injectiveMoment H raw10066step0 := by
      have heq : raw10066step0 = (fun i j => raw10066 (permutation395 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10066 permutation395 permutation10
    _ = injectiveMoment H node3358 := by rfl

def raw10067 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0], ![0, -1, -1, 2], ![-2, 0, 3, -1]]

def raw10067step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical10067 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10067 = injectiveMoment H node3126 := by
  calc
    injectiveMoment H raw10067 = injectiveMoment H raw10067step0 := by
      have heq : raw10067step0 = (fun i j => raw10067 (permutation395 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10067 permutation395 permutation10
    _ = injectiveMoment H node3126 := by rfl

def raw10068 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-2, 0, 3, -1], ![0, -1, -2, 3]]

def raw10068step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -2, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical10068 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10068 = injectiveMoment H node3219 := by
  calc
    injectiveMoment H raw10068 = injectiveMoment H raw10068step0 := by
      have heq : raw10068step0 = (fun i j => raw10068 (permutation294 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10068 permutation294 permutation9
    _ = injectiveMoment H node3219 := by rfl

def raw10069 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-1, -1, 3, -1], ![-1, 0, -2, 3]]

def raw10069step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![-1, 0, -2, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical10069 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10069 = injectiveMoment H node3409 := by
  calc
    injectiveMoment H raw10069 = injectiveMoment H raw10069step0 := by
      have heq : raw10069step0 = (fun i j => raw10069 (permutation294 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10069 permutation294 permutation9
    _ = injectiveMoment H node3409 := by rfl

def raw10070 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1], ![-1, 0, -1, 2], ![-1, -1, 3, -1]]

def raw10070step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical10070 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10070 = injectiveMoment H node3357 := by
  calc
    injectiveMoment H raw10070 = injectiveMoment H raw10070step0 := by
      have heq : raw10070step0 = (fun i j => raw10070 (permutation395 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10070 permutation395 permutation10
    _ = injectiveMoment H node3357 := by rfl

def raw10071 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1], ![0, -1, -1, 2], ![-2, 0, 3, -1]]

def raw10071step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical10071 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10071 = injectiveMoment H node3125 := by
  calc
    injectiveMoment H raw10071 = injectiveMoment H raw10071step0 := by
      have heq : raw10071step0 = (fun i j => raw10071 (permutation395 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10071 permutation395 permutation10
    _ = injectiveMoment H node3125 := by rfl

def raw10072 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 3, -1], ![0, -1, -2, 3]]

def raw10072step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical10072 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10072 = injectiveMoment H node3128 := by
  calc
    injectiveMoment H raw10072 = injectiveMoment H raw10072step0 := by
      have heq : raw10072step0 = (fun i j => raw10072 (permutation294 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10072 permutation294 permutation10
    _ = injectiveMoment H node3128 := by rfl

def raw10073 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 3, -1], ![-1, 0, -2, 3]]

def raw10073step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical10073 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10073 = injectiveMoment H node3362 := by
  calc
    injectiveMoment H raw10073 = injectiveMoment H raw10073step0 := by
      have heq : raw10073step0 = (fun i j => raw10073 (permutation294 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10073 permutation294 permutation10
    _ = injectiveMoment H node3362 := by rfl

def raw10074 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, 0, -2, 3], ![-1, -1, 3, -1]]

def raw10074step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical10074 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10074 = injectiveMoment H node3362 := by
  calc
    injectiveMoment H raw10074 = injectiveMoment H raw10074step0 := by
      have heq : raw10074step0 = (fun i j => raw10074 (permutation395 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10074 permutation395 permutation10
    _ = injectiveMoment H node3362 := by rfl

def raw10075 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, 0, -1, 2], ![-1, -1, 2, 0]]

def raw10075step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def raw10075step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical10075 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw10075 = injectiveMoment H node3217 := by
  calc
    injectiveMoment H raw10075 = injectiveMoment H raw10075step0 := by
      have heq : raw10075step0 = -raw10075 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw10075).symm
    injectiveMoment H raw10075step0 = injectiveMoment H raw10075step1 := by
      have heq : raw10075step1 = (fun i j => raw10075step0 (permutation292 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10075step0 permutation292 permutation29
    _ = injectiveMoment H node3217 := by rfl

def raw10076 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, -1, -2, 3], ![-2, 0, 3, -1]]

def raw10076step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical10076 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10076 = injectiveMoment H node3128 := by
  calc
    injectiveMoment H raw10076 = injectiveMoment H raw10076step0 := by
      have heq : raw10076step0 = (fun i j => raw10076 (permutation395 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10076 permutation395 permutation10
    _ = injectiveMoment H node3128 := by rfl

def raw10077 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, -1, -1, 2], ![-2, 0, 2, 0]]

def raw10077step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw10077step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem canonical10077 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw10077 = injectiveMoment H node3170 := by
  calc
    injectiveMoment H raw10077 = injectiveMoment H raw10077step0 := by
      have heq : raw10077step0 = -raw10077 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw10077).symm
    injectiveMoment H raw10077step0 = injectiveMoment H raw10077step1 := by
      have heq : raw10077step1 = (fun i j => raw10077step0 (permutation308 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10077step0 permutation308 permutation24
    _ = injectiveMoment H node3170 := by rfl

def raw10078 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, 2, 0], ![0, -1, -2, 3]]

def raw10078step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical10078 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10078 = injectiveMoment H node2966 := by
  calc
    injectiveMoment H raw10078 = injectiveMoment H raw10078step0 := by
      have heq : raw10078step0 = (fun i j => raw10078 (permutation363 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10078 permutation363 permutation23
    _ = injectiveMoment H node2966 := by rfl

def raw10079 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, 3, -1], ![0, -1, -3, 4]]

def raw10079step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -3, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical10079 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10079 = injectiveMoment H node3218 := by
  calc
    injectiveMoment H raw10079 = injectiveMoment H raw10079step0 := by
      have heq : raw10079step0 = (fun i j => raw10079 (permutation294 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10079 permutation294 permutation9
    _ = injectiveMoment H node3218 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

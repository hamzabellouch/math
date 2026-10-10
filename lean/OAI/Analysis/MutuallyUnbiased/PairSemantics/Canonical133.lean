import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes33

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4256 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

theorem canonical4256 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4256 = injectiveMoment H node2153 := by
  rfl

def raw4257 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, 0, 0]]

theorem canonical4257 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4257 = injectiveMoment H node2154 := by
  rfl

def raw4258 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, 0, 0]]

theorem canonical4258 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4258 = injectiveMoment H node2155 := by
  rfl

def raw4259 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

theorem canonical4259 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4259 = injectiveMoment H node2156 := by
  rfl

def raw4260 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw4260step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-3, 1, 0, 2], ![4, -1, -1, -2]]

def raw4260step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 2, -3]]

theorem canonical4260 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4260 = injectiveMoment H node913 := by
  calc
    injectiveMoment H raw4260 = injectiveMoment H raw4260step0 := by
      have heq : raw4260step0 = raw4260.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4260).symm
    injectiveMoment H raw4260step0 = injectiveMoment H raw4260step1 := by
      have heq : raw4260step1 = (fun i j => raw4260step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4260step0 permutation27 permutation18
    _ = injectiveMoment H node913 := by rfl

def raw4261 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical4261 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4261 = injectiveMoment H node2157 := by
  rfl

def raw4262 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def raw4262step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-3, 1, 1, 1], ![4, -1, -2, -1]]

def raw4262step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, 1, -3]]

theorem canonical4262 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4262 = injectiveMoment H node770 := by
  calc
    injectiveMoment H raw4262 = injectiveMoment H raw4262step0 := by
      have heq : raw4262step0 = raw4262.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4262).symm
    injectiveMoment H raw4262step0 = injectiveMoment H raw4262step1 := by
      have heq : raw4262step1 = (fun i j => raw4262step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4262step0 permutation27 permutation18
    _ = injectiveMoment H node770 := by rfl

def raw4263 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical4263 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4263 = injectiveMoment H node2158 := by
  rfl

def raw4264 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 1, 2, -3], ![2, -2, 0, 0]]

def raw4264step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-3, 1, 2, 0], ![4, -1, -3, 0]]

def raw4264step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 1, 1], ![0, 2, 0, -2], ![1, 0, 2, -3]]

theorem canonical4264 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4264 = injectiveMoment H node1162 := by
  calc
    injectiveMoment H raw4264 = injectiveMoment H raw4264step0 := by
      have heq : raw4264step0 = raw4264.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4264).symm
    injectiveMoment H raw4264step0 = injectiveMoment H raw4264step1 := by
      have heq : raw4264step1 = (fun i j => raw4264step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4264step0 permutation29 permutation20
    _ = injectiveMoment H node1162 := by rfl

def raw4265 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw4265step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-3, 1, 1, 1], ![4, -1, 0, -3]]

def raw4265step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![3, -1, -1, -1], ![-4, 1, 0, 3]]

def raw4265step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, 0, 3, -4]]

theorem canonical4265 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4265 = injectiveMoment H node932 := by
  calc
    injectiveMoment H raw4265 = injectiveMoment H raw4265step0 := by
      have heq : raw4265step0 = raw4265.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4265).symm
    injectiveMoment H raw4265step0 = injectiveMoment H raw4265step1 := by
      have heq : raw4265step1 = -raw4265step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4265step0).symm
    injectiveMoment H raw4265step1 = injectiveMoment H raw4265step2 := by
      have heq : raw4265step2 = (fun i j => raw4265step1 (permutation21 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4265step1 permutation21 permutation18
    _ = injectiveMoment H node932 := by rfl

def raw4266 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![1, -2, 2, -1], ![1, 1, 0, -2]]

def raw4266step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-3, 1, 2, 0], ![4, -1, -1, -2]]

def raw4266step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 2, -3]]

theorem canonical4266 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4266 = injectiveMoment H node784 := by
  calc
    injectiveMoment H raw4266 = injectiveMoment H raw4266step0 := by
      have heq : raw4266step0 = raw4266.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4266).symm
    injectiveMoment H raw4266step0 = injectiveMoment H raw4266step1 := by
      have heq : raw4266step1 = (fun i j => raw4266step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4266step0 permutation29 permutation20
    _ = injectiveMoment H node784 := by rfl

def raw4267 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0]]

def raw4267step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, 0, 0]]

theorem canonical4267 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4267 = injectiveMoment H node2155 := by
  calc
    injectiveMoment H raw4267 = injectiveMoment H raw4267step0 := by
      have heq : raw4267step0 = (fun i j => raw4267 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4267 permutation39 permutation9
    _ = injectiveMoment H node2155 := by rfl

def raw4268 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw4268step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-3, 2, 0, 1], ![4, -2, -1, -1]]

def raw4268step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical4268 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4268 = injectiveMoment H node776 := by
  calc
    injectiveMoment H raw4268 = injectiveMoment H raw4268step0 := by
      have heq : raw4268step0 = raw4268.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4268).symm
    injectiveMoment H raw4268step0 = injectiveMoment H raw4268step1 := by
      have heq : raw4268step1 = (fun i j => raw4268step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4268step0 permutation28 permutation24
    _ = injectiveMoment H node776 := by rfl

def raw4269 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical4269 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4269 = injectiveMoment H node2159 := by
  rfl

def raw4270 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def raw4270step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-3, 2, 1, 0], ![4, -2, -2, 0]]

def raw4270step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, 1, 0, -3]]

theorem canonical4270 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4270 = injectiveMoment H node394 := by
  calc
    injectiveMoment H raw4270 = injectiveMoment H raw4270step0 := by
      have heq : raw4270step0 = raw4270.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4270).symm
    injectiveMoment H raw4270step0 = injectiveMoment H raw4270step1 := by
      have heq : raw4270step1 = (fun i j => raw4270step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4270step0 permutation27 permutation18
    _ = injectiveMoment H node394 := by rfl

def raw4271 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 1, 0, -2]]

def raw4271step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![-3, 2, 1, 0], ![4, -2, 0, -2]]

def raw4271step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 1, -3]]

theorem canonical4271 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4271 = injectiveMoment H node400 := by
  calc
    injectiveMoment H raw4271 = injectiveMoment H raw4271step0 := by
      have heq : raw4271step0 = raw4271.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4271).symm
    injectiveMoment H raw4271step0 = injectiveMoment H raw4271step1 := by
      have heq : raw4271step1 = (fun i j => raw4271step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4271step0 permutation29 permutation20
    _ = injectiveMoment H node400 := by rfl

def raw4272 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw4272step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-3, 2, 0, 1], ![4, -2, 0, -2]]

def raw4272step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![3, -2, 0, -1], ![-4, 2, 0, 2]]

def raw4272step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, 0, 0, -1]]

theorem canonical4272 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4272 = injectiveMoment H node994 := by
  calc
    injectiveMoment H raw4272 = injectiveMoment H raw4272step0 := by
      have heq : raw4272step0 = raw4272.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4272).symm
    injectiveMoment H raw4272step0 = injectiveMoment H raw4272step1 := by
      have heq : raw4272step1 = -raw4272step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4272step0).symm
    injectiveMoment H raw4272step1 = injectiveMoment H raw4272step2 := by
      have heq : raw4272step2 = (fun i j => raw4272step1 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4272step1 permutation12 permutation26
    _ = injectiveMoment H node994 := by rfl

def raw4273 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw4273step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-3, 2, 1, 0], ![4, -2, -1, -1]]

def raw4273step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 1, -2]]

theorem canonical4273 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4273 = injectiveMoment H node764 := by
  calc
    injectiveMoment H raw4273 = injectiveMoment H raw4273step0 := by
      have heq : raw4273step0 = raw4273.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4273).symm
    injectiveMoment H raw4273step0 = injectiveMoment H raw4273step1 := by
      have heq : raw4273step1 = (fun i j => raw4273step0 (permutation30 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4273step0 permutation30 permutation30
    _ = injectiveMoment H node764 := by rfl

def raw4274 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 2, -2], ![1, 0, 1, -2], ![1, -1, 0, 0]]

def raw4274step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, 0, -1], ![-3, 2, 1, 0], ![4, -2, -2, 0]]

def raw4274step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 0, 1], ![3, -2, -1, 0], ![-4, 2, 2, 0]]

def raw4274step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, 0, 0, -1]]

theorem canonical4274 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4274 = injectiveMoment H node994 := by
  calc
    injectiveMoment H raw4274 = injectiveMoment H raw4274step0 := by
      have heq : raw4274step0 = raw4274.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4274).symm
    injectiveMoment H raw4274step0 = injectiveMoment H raw4274step1 := by
      have heq : raw4274step1 = -raw4274step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4274step0).symm
    injectiveMoment H raw4274step1 = injectiveMoment H raw4274step2 := by
      have heq : raw4274step2 = (fun i j => raw4274step1 (permutation12 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4274step1 permutation12 permutation32
    _ = injectiveMoment H node994 := by rfl

def raw4275 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical4275 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4275 = injectiveMoment H node2160 := by
  rfl

def raw4276 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 3, -3], ![0, 1, 0, -1], ![2, -2, 0, 0]]

def raw4276step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![-3, 3, 0, 0], ![4, -3, -1, 0]]

def raw4276step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 3, -3], ![0, 2, 0, -2], ![1, -2, 0, 1]]

theorem canonical4276 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4276 = injectiveMoment H node1184 := by
  calc
    injectiveMoment H raw4276 = injectiveMoment H raw4276step0 := by
      have heq : raw4276step0 = raw4276.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4276).symm
    injectiveMoment H raw4276step0 = injectiveMoment H raw4276step1 := by
      have heq : raw4276step1 = (fun i j => raw4276step0 (permutation31 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4276step0 permutation31 permutation26
    _ = injectiveMoment H node1184 := by rfl

def raw4277 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4277step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![-3, 3, 0, 0], ![4, -3, 0, -1]]

def raw4277step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 1, 0], ![3, -3, 0, 0], ![-4, 3, 0, 1]]

def raw4277step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -3, 3], ![0, 1, 0, -1], ![1, 0, 3, -4]]

theorem canonical4277 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4277 = injectiveMoment H node1023 := by
  calc
    injectiveMoment H raw4277 = injectiveMoment H raw4277step0 := by
      have heq : raw4277step0 = raw4277.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4277).symm
    injectiveMoment H raw4277step0 = injectiveMoment H raw4277step1 := by
      have heq : raw4277step1 = -raw4277step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4277step0).symm
    injectiveMoment H raw4277step1 = injectiveMoment H raw4277step2 := by
      have heq : raw4277step2 = (fun i j => raw4277step1 (permutation11 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4277step1 permutation11 permutation32
    _ = injectiveMoment H node1023 := by rfl

def raw4278 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 3, -3], ![1, 0, 0, -1], ![1, -1, 0, 0]]

def raw4278step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, 0, -1], ![-3, 3, 0, 0], ![4, -3, -1, 0]]

def raw4278step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 0, 1], ![3, -3, 0, 0], ![-4, 3, 1, 0]]

def raw4278step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -3, 3], ![0, 1, 0, -1], ![1, 0, 3, -4]]

theorem canonical4278 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4278 = injectiveMoment H node1023 := by
  calc
    injectiveMoment H raw4278 = injectiveMoment H raw4278step0 := by
      have heq : raw4278step0 = raw4278.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4278).symm
    injectiveMoment H raw4278step0 = injectiveMoment H raw4278step1 := by
      have heq : raw4278step1 = -raw4278step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4278step0).symm
    injectiveMoment H raw4278step1 = injectiveMoment H raw4278step2 := by
      have heq : raw4278step2 = (fun i j => raw4278step1 (permutation11 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4278step1 permutation11 permutation26
    _ = injectiveMoment H node1023 := by rfl

def raw4279 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw4279step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-3, 0, 2, 1], ![4, -1, -1, -2]]

def raw4279step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 1, -2], ![0, 1, 2, -3], ![1, 0, -2, 1]]

theorem canonical4279 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4279 = injectiveMoment H node788 := by
  calc
    injectiveMoment H raw4279 = injectiveMoment H raw4279step0 := by
      have heq : raw4279step0 = raw4279.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4279).symm
    injectiveMoment H raw4279step0 = injectiveMoment H raw4279step1 := by
      have heq : raw4279step1 = (fun i j => raw4279step0 (permutation28 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4279step0 permutation28 permutation20
    _ = injectiveMoment H node788 := by rfl

def raw4280 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw4280step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-3, 0, 3, 0], ![4, -1, -2, -1]]

def raw4280step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem canonical4280 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4280 = injectiveMoment H node918 := by
  calc
    injectiveMoment H raw4280 = injectiveMoment H raw4280step0 := by
      have heq : raw4280step0 = raw4280.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4280).symm
    injectiveMoment H raw4280step0 = injectiveMoment H raw4280step1 := by
      have heq : raw4280step1 = (fun i j => raw4280step0 (permutation32 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4280step0 permutation32 permutation30
    _ = injectiveMoment H node918 := by rfl

def raw4281 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw4281step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-3, 0, 0, 3], ![4, -1, 0, -3]]

def raw4281step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 3, -3], ![0, 1, 1, -2], ![1, -1, -1, 1]]

theorem canonical4281 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4281 = injectiveMoment H node1182 := by
  calc
    injectiveMoment H raw4281 = injectiveMoment H raw4281step0 := by
      have heq : raw4281step0 = raw4281.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4281).symm
    injectiveMoment H raw4281step0 = injectiveMoment H raw4281step1 := by
      have heq : raw4281step1 = (fun i j => raw4281step0 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4281step0 permutation31 permutation18
    _ = injectiveMoment H node1182 := by rfl

def raw4282 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def raw4282step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-3, 0, 1, 2], ![4, -1, -1, -2]]

def raw4282step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 1, 1, -2], ![0, 1, 2, -3], ![1, -1, -1, 1]]

theorem canonical4282 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4282 = injectiveMoment H node923 := by
  calc
    injectiveMoment H raw4282 = injectiveMoment H raw4282step0 := by
      have heq : raw4282step0 = raw4282.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4282).symm
    injectiveMoment H raw4282step0 = injectiveMoment H raw4282step1 := by
      have heq : raw4282step1 = (fun i j => raw4282step0 (permutation28 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4282step0 permutation28 permutation18
    _ = injectiveMoment H node923 := by rfl

def raw4283 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw4283step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-3, 1, 2, 0], ![4, -2, -1, -1]]

def raw4283step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, 1, -2]]

theorem canonical4283 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4283 = injectiveMoment H node785 := by
  calc
    injectiveMoment H raw4283 = injectiveMoment H raw4283step0 := by
      have heq : raw4283step0 = raw4283.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4283).symm
    injectiveMoment H raw4283step0 = injectiveMoment H raw4283step1 := by
      have heq : raw4283step1 = (fun i j => raw4283step0 (permutation30 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4283step0 permutation30 permutation30
    _ = injectiveMoment H node785 := by rfl

def raw4284 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw4284step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-3, 1, 0, 2], ![4, -2, 0, -2]]

def raw4284step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![3, -1, 0, -2], ![-4, 2, 0, 2]]

def raw4284step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, -1, 1, -1]]

theorem canonical4284 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4284 = injectiveMoment H node1236 := by
  calc
    injectiveMoment H raw4284 = injectiveMoment H raw4284step0 := by
      have heq : raw4284step0 = raw4284.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4284).symm
    injectiveMoment H raw4284step0 = injectiveMoment H raw4284step1 := by
      have heq : raw4284step1 = -raw4284step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4284step0).symm
    injectiveMoment H raw4284step1 = injectiveMoment H raw4284step2 := by
      have heq : raw4284step2 = (fun i j => raw4284step1 (permutation12 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4284step1 permutation12 permutation24
    _ = injectiveMoment H node1236 := by rfl

def raw4285 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw4285step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-3, 1, 1, 1], ![4, -2, -1, -1]]

def raw4285step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, 1, -3]]

theorem canonical4285 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4285 = injectiveMoment H node463 := by
  calc
    injectiveMoment H raw4285 = injectiveMoment H raw4285step0 := by
      have heq : raw4285step0 = raw4285.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4285).symm
    injectiveMoment H raw4285step0 = injectiveMoment H raw4285step1 := by
      have heq : raw4285step1 = (fun i j => raw4285step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4285step0 permutation27 permutation18
    _ = injectiveMoment H node463 := by rfl

def raw4286 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw4286step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-3, 2, 0, 1], ![4, -3, 0, -1]]

def raw4286step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![3, -2, 0, -1], ![-4, 3, 0, 1]]

def raw4286step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, 1, -1, -1]]

theorem canonical4286 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4286 = injectiveMoment H node992 := by
  calc
    injectiveMoment H raw4286 = injectiveMoment H raw4286step0 := by
      have heq : raw4286step0 = raw4286.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4286).symm
    injectiveMoment H raw4286step0 = injectiveMoment H raw4286step1 := by
      have heq : raw4286step1 = -raw4286step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4286step0).symm
    injectiveMoment H raw4286step1 = injectiveMoment H raw4286step2 := by
      have heq : raw4286step2 = (fun i j => raw4286step1 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4286step1 permutation12 permutation26
    _ = injectiveMoment H node992 := by rfl

def raw4287 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw4287step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-3, 2, 1, 0], ![4, -3, -1, 0]]

def raw4287step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![3, -2, -1, 0], ![-4, 3, 1, 0]]

def raw4287step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, 1, -1, -1]]

theorem canonical4287 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4287 = injectiveMoment H node992 := by
  calc
    injectiveMoment H raw4287 = injectiveMoment H raw4287step0 := by
      have heq : raw4287step0 = raw4287.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4287).symm
    injectiveMoment H raw4287step0 = injectiveMoment H raw4287step1 := by
      have heq : raw4287step1 = -raw4287step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4287step0).symm
    injectiveMoment H raw4287step1 = injectiveMoment H raw4287step2 := by
      have heq : raw4287step2 = (fun i j => raw4287step1 (permutation12 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4287step1 permutation12 permutation32
    _ = injectiveMoment H node992 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

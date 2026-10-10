import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes24

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw128 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]

def raw128step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]

def raw128step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical128 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw128 = injectiveMoment H node246 := by
  calc
    injectiveMoment H raw128 = injectiveMoment H raw128step0 := by
      have heq : raw128step0 = -raw128 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw128).symm
    injectiveMoment H raw128step0 = injectiveMoment H raw128step1 := by
      have heq : raw128step1 = (fun i j => raw128step0 (permutation11 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw128step0 permutation11 permutation6
    _ = injectiveMoment H node246 := by rfl

def raw129 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]

def raw129step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

theorem canonical129 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw129 = injectiveMoment H node206 := by
  calc
    injectiveMoment H raw129 = injectiveMoment H raw129step0 := by
      have heq : raw129step0 = (fun i j => raw129 (permutation30 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw129 permutation30 permutation6
    _ = injectiveMoment H node206 := by rfl

def raw130 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]

def raw130step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 3, -4]]

theorem canonical130 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw130 = injectiveMoment H node40 := by
  calc
    injectiveMoment H raw130 = injectiveMoment H raw130step0 := by
      have heq : raw130step0 = (fun i j => raw130 (permutation8 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw130 permutation8 permutation6
    _ = injectiveMoment H node40 := by rfl

def raw131 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]

def raw131step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]

def raw131step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 2, -1], ![-3, 0, 3]]

def raw131step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

theorem canonical131 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw131 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw131 = injectiveMoment H raw131step0 := by
      have heq : raw131step0 = raw131.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw131).symm
    injectiveMoment H raw131step0 = injectiveMoment H raw131step1 := by
      have heq : raw131step1 = -raw131step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw131step0).symm
    injectiveMoment H raw131step1 = injectiveMoment H raw131step2 := by
      have heq : raw131step2 = (fun i j => raw131step1 (permutation4 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw131step1 permutation4 permutation6
    _ = injectiveMoment H node32 := by rfl

def raw132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]

def raw132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]

def raw132step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

theorem canonical132 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw132 = injectiveMoment H node1526 := by
  calc
    injectiveMoment H raw132 = injectiveMoment H raw132step0 := by
      have heq : raw132step0 = -raw132 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw132).symm
    injectiveMoment H raw132step0 = injectiveMoment H raw132step1 := by
      have heq : raw132step1 = (fun i j => raw132step0 (permutation158 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw132step0 permutation158 permutation8
    _ = injectiveMoment H node1526 := by rfl

def raw133 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]

def raw133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]

theorem canonical133 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw133 = injectiveMoment H node414 := by
  calc
    injectiveMoment H raw133 = injectiveMoment H raw133step0 := by
      have heq : raw133step0 = (fun i j => raw133 (permutation148 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw133 permutation148 permutation6
    _ = injectiveMoment H node414 := by rfl

def raw134 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]

def raw134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]

def raw134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]

theorem canonical134 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw134 = injectiveMoment H node416 := by
  calc
    injectiveMoment H raw134 = injectiveMoment H raw134step0 := by
      have heq : raw134step0 = -raw134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw134).symm
    injectiveMoment H raw134step0 = injectiveMoment H raw134step1 := by
      have heq : raw134step1 = (fun i j => raw134step0 (permutation35 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw134step0 permutation35 permutation8
    _ = injectiveMoment H node416 := by rfl

def raw135 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]

def raw135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]

theorem canonical135 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw135 = injectiveMoment H node326 := by
  calc
    injectiveMoment H raw135 = injectiveMoment H raw135step0 := by
      have heq : raw135step0 = (fun i j => raw135 (permutation148 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw135 permutation148 permutation6
    _ = injectiveMoment H node326 := by rfl

def raw136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]

def raw136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]

def raw136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical136 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw136 = injectiveMoment H node1539 := by
  calc
    injectiveMoment H raw136 = injectiveMoment H raw136step0 := by
      have heq : raw136step0 = -raw136 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw136).symm
    injectiveMoment H raw136step0 = injectiveMoment H raw136step1 := by
      have heq : raw136step1 = (fun i j => raw136step0 (permutation164 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw136step0 permutation164 permutation6
    _ = injectiveMoment H node1539 := by rfl

def raw137 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]

def raw137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]

def raw137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem canonical137 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw137 = injectiveMoment H node435 := by
  calc
    injectiveMoment H raw137 = injectiveMoment H raw137step0 := by
      have heq : raw137step0 = -raw137 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw137).symm
    injectiveMoment H raw137step0 = injectiveMoment H raw137step1 := by
      have heq : raw137step1 = (fun i j => raw137step0 (permutation37 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw137step0 permutation37 permutation6
    _ = injectiveMoment H node435 := by rfl

def raw138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]

def raw138step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw138step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical138 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw138 = injectiveMoment H node1538 := by
  calc
    injectiveMoment H raw138 = injectiveMoment H raw138step0 := by
      have heq : raw138step0 = -raw138 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw138).symm
    injectiveMoment H raw138step0 = injectiveMoment H raw138step1 := by
      have heq : raw138step1 = (fun i j => raw138step0 (permutation158 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw138step0 permutation158 permutation6
    _ = injectiveMoment H node1538 := by rfl

def raw139 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]

def raw139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]

def raw139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical139 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw139 = injectiveMoment H node432 := by
  calc
    injectiveMoment H raw139 = injectiveMoment H raw139step0 := by
      have heq : raw139step0 = -raw139 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw139).symm
    injectiveMoment H raw139step0 = injectiveMoment H raw139step1 := by
      have heq : raw139step1 = (fun i j => raw139step0 (permutation35 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw139step0 permutation35 permutation6
    _ = injectiveMoment H node432 := by rfl

def raw140 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]

def raw140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]

def raw140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

theorem canonical140 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw140 = injectiveMoment H node415 := by
  calc
    injectiveMoment H raw140 = injectiveMoment H raw140step0 := by
      have heq : raw140step0 = -raw140 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw140).symm
    injectiveMoment H raw140step0 = injectiveMoment H raw140step1 := by
      have heq : raw140step1 = (fun i j => raw140step0 (permutation34 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw140step0 permutation34 permutation8
    _ = injectiveMoment H node415 := by rfl

def raw141 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]

def raw141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]

theorem canonical141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw141 = injectiveMoment H node352 := by
  calc
    injectiveMoment H raw141 = injectiveMoment H raw141step0 := by
      have heq : raw141step0 = (fun i j => raw141 (permutation150 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw141 permutation150 permutation8
    _ = injectiveMoment H node352 := by rfl

def raw142 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]

def raw142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]

def raw142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical142 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw142 = injectiveMoment H node434 := by
  calc
    injectiveMoment H raw142 = injectiveMoment H raw142step0 := by
      have heq : raw142step0 = -raw142 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw142).symm
    injectiveMoment H raw142step0 = injectiveMoment H raw142step1 := by
      have heq : raw142step1 = (fun i j => raw142step0 (permutation37 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw142step0 permutation37 permutation6
    _ = injectiveMoment H node434 := by rfl

def raw143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw143step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]

def raw143step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical143 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw143 = injectiveMoment H node1536 := by
  calc
    injectiveMoment H raw143 = injectiveMoment H raw143step0 := by
      have heq : raw143step0 = -raw143 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw143).symm
    injectiveMoment H raw143step0 = injectiveMoment H raw143step1 := by
      have heq : raw143step1 = (fun i j => raw143step0 (permutation151 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw143step0 permutation151 permutation6
    _ = injectiveMoment H node1536 := by rfl

def raw144 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]

def raw144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]

def raw144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

theorem canonical144 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw144 = injectiveMoment H node429 := by
  calc
    injectiveMoment H raw144 = injectiveMoment H raw144step0 := by
      have heq : raw144step0 = -raw144 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw144).symm
    injectiveMoment H raw144step0 = injectiveMoment H raw144step1 := by
      have heq : raw144step1 = (fun i j => raw144step0 (permutation33 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw144step0 permutation33 permutation6
    _ = injectiveMoment H node429 := by rfl

def raw145 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]

def raw145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]

def raw145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical145 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw145 = injectiveMoment H node430 := by
  calc
    injectiveMoment H raw145 = injectiveMoment H raw145step0 := by
      have heq : raw145step0 = -raw145 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw145).symm
    injectiveMoment H raw145step0 = injectiveMoment H raw145step1 := by
      have heq : raw145step1 = (fun i j => raw145step0 (permutation34 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw145step0 permutation34 permutation6
    _ = injectiveMoment H node430 := by rfl

def raw146 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]

def raw146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]

def raw146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical146 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw146 = injectiveMoment H node433 := by
  calc
    injectiveMoment H raw146 = injectiveMoment H raw146step0 := by
      have heq : raw146step0 = -raw146 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw146).symm
    injectiveMoment H raw146step0 = injectiveMoment H raw146step1 := by
      have heq : raw146step1 = (fun i j => raw146step0 (permutation33 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw146step0 permutation33 permutation6
    _ = injectiveMoment H node433 := by rfl

def raw147 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]

def raw147step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![2, 2, -4]]

theorem canonical147 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw147 = injectiveMoment H node139 := by
  calc
    injectiveMoment H raw147 = injectiveMoment H raw147step0 := by
      have heq : raw147step0 = (fun i j => raw147 (permutation32 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw147 permutation32 permutation6
    _ = injectiveMoment H node139 := by rfl

def raw148 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]

def raw148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 2, 0], ![-2, 1, 1]]

def raw148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

theorem canonical148 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw148 = injectiveMoment H node417 := by
  calc
    injectiveMoment H raw148 = injectiveMoment H raw148step0 := by
      have heq : raw148step0 = -raw148 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw148).symm
    injectiveMoment H raw148step0 = injectiveMoment H raw148step1 := by
      have heq : raw148step1 = (fun i j => raw148step0 (permutation36 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw148step0 permutation36 permutation8
    _ = injectiveMoment H node417 := by rfl

def raw149 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]

def raw149step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-2, 2, 0], ![-3, 0, 3]]

def raw149step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

theorem canonical149 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw149 = injectiveMoment H node141 := by
  calc
    injectiveMoment H raw149 = injectiveMoment H raw149step0 := by
      have heq : raw149step0 = -raw149 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw149).symm
    injectiveMoment H raw149step0 = injectiveMoment H raw149step1 := by
      have heq : raw149step1 = (fun i j => raw149step0 (permutation10 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw149step0 permutation10 permutation6
    _ = injectiveMoment H node141 := by rfl

def raw150 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]

def raw150step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-2, 1, 1], ![-3, 1, 2]]

def raw150step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 1, -2], ![1, 2, -3]]

theorem canonical150 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw150 = injectiveMoment H node144 := by
  calc
    injectiveMoment H raw150 = injectiveMoment H raw150step0 := by
      have heq : raw150step0 = -raw150 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw150).symm
    injectiveMoment H raw150step0 = injectiveMoment H raw150step1 := by
      have heq : raw150step1 = (fun i j => raw150step0 (permutation9 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw150step0 permutation9 permutation6
    _ = injectiveMoment H node144 := by rfl

def raw151 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]

def raw151step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-2, 0, 2], ![-3, 2, 1]]

def raw151step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 2, -2], ![2, 1, -3]]

theorem canonical151 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw151 = injectiveMoment H node140 := by
  calc
    injectiveMoment H raw151 = injectiveMoment H raw151step0 := by
      have heq : raw151step0 = -raw151 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw151).symm
    injectiveMoment H raw151step0 = injectiveMoment H raw151step1 := by
      have heq : raw151step1 = (fun i j => raw151step0 (permutation9 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw151step0 permutation9 permutation6
    _ = injectiveMoment H node140 := by rfl

def raw152 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]

def raw152step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]

theorem canonical152 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw152 = injectiveMoment H node94 := by
  calc
    injectiveMoment H raw152 = injectiveMoment H raw152step0 := by
      have heq : raw152step0 = (fun i j => raw152 (permutation30 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw152 permutation30 permutation6
    _ = injectiveMoment H node94 := by rfl

def raw153 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]

def raw153step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 2, -2], ![-1, 0, 1], ![-3, 0, 3]]

def raw153step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 3, -3], ![2, -2, 0]]

theorem canonical153 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw153 = injectiveMoment H node147 := by
  calc
    injectiveMoment H raw153 = injectiveMoment H raw153step0 := by
      have heq : raw153step0 = -raw153 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw153).symm
    injectiveMoment H raw153step0 = injectiveMoment H raw153step1 := by
      have heq : raw153step1 = (fun i j => raw153step0 (permutation12 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw153step0 permutation12 permutation6
    _ = injectiveMoment H node147 := by rfl

def raw154 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]

def raw154step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 2, -2], ![-2, 0, 2], ![-2, 0, 2]]

def raw154step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]

theorem canonical154 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw154 = injectiveMoment H node151 := by
  calc
    injectiveMoment H raw154 = injectiveMoment H raw154step0 := by
      have heq : raw154step0 = -raw154 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw154).symm
    injectiveMoment H raw154step0 = injectiveMoment H raw154step1 := by
      have heq : raw154step1 = (fun i j => raw154step0 (permutation12 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw154step0 permutation12 permutation6
    _ = injectiveMoment H node151 := by rfl

def raw155 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]

def raw155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-3, 0, 3]]

def raw155step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical155 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw155 = injectiveMoment H node445 := by
  calc
    injectiveMoment H raw155 = injectiveMoment H raw155step0 := by
      have heq : raw155step0 = -raw155 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw155).symm
    injectiveMoment H raw155step0 = injectiveMoment H raw155step1 := by
      have heq : raw155step1 = (fun i j => raw155step0 (permutation49 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw155step0 permutation49 permutation6
    _ = injectiveMoment H node445 := by rfl

def raw156 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]

def raw156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]

def raw156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

theorem canonical156 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw156 = injectiveMoment H node446 := by
  calc
    injectiveMoment H raw156 = injectiveMoment H raw156step0 := by
      have heq : raw156step0 = -raw156 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw156).symm
    injectiveMoment H raw156step0 = injectiveMoment H raw156step1 := by
      have heq : raw156step1 = (fun i j => raw156step0 (permutation49 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw156step0 permutation49 permutation6
    _ = injectiveMoment H node446 := by rfl

def raw157 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]

def raw157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]

def raw157step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

theorem canonical157 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw157 = injectiveMoment H node420 := by
  calc
    injectiveMoment H raw157 = injectiveMoment H raw157step0 := by
      have heq : raw157step0 = -raw157 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw157).symm
    injectiveMoment H raw157step0 = injectiveMoment H raw157step1 := by
      have heq : raw157step1 = (fun i j => raw157step0 (permutation43 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw157step0 permutation43 permutation6
    _ = injectiveMoment H node420 := by rfl

def raw158 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]

def raw158step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]

theorem canonical158 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw158 = injectiveMoment H node131 := by
  calc
    injectiveMoment H raw158 = injectiveMoment H raw158step0 := by
      have heq : raw158step0 = (fun i j => raw158 (permutation30 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw158 permutation30 permutation6
    _ = injectiveMoment H node131 := by rfl

def raw159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]

def raw159step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]

def raw159step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical159 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw159 = injectiveMoment H node1542 := by
  calc
    injectiveMoment H raw159 = injectiveMoment H raw159step0 := by
      have heq : raw159step0 = -raw159 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw159).symm
    injectiveMoment H raw159step0 = injectiveMoment H raw159step1 := by
      have heq : raw159step1 = (fun i j => raw159step0 (permutation180 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw159step0 permutation180 permutation6
    _ = injectiveMoment H node1542 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

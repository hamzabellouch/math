import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw96 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]

def raw96step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]

def raw96step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical96 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw96 = injectiveMoment H node740 := by
  calc
    injectiveMoment H raw96 = injectiveMoment H raw96step0 := by
      have heq : raw96step0 = -raw96 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw96).symm
    injectiveMoment H raw96step0 = injectiveMoment H raw96step1 := by
      have heq : raw96step1 = (fun i j => raw96step0 (permutation43 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw96step0 permutation43 permutation6
    _ = injectiveMoment H node740 := by rfl

def raw97 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]

def raw97step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw97step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical97 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw97 = injectiveMoment H node2379 := by
  calc
    injectiveMoment H raw97 = injectiveMoment H raw97step0 := by
      have heq : raw97step0 = -raw97 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw97).symm
    injectiveMoment H raw97step0 = injectiveMoment H raw97step1 := by
      have heq : raw97step1 = (fun i j => raw97step0 (permutation171 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw97step0 permutation171 permutation6
    _ = injectiveMoment H node2379 := by rfl

def raw98 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]

def raw98step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]

def raw98step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical98 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw98 = injectiveMoment H node736 := by
  calc
    injectiveMoment H raw98 = injectiveMoment H raw98step0 := by
      have heq : raw98step0 = -raw98 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw98).symm
    injectiveMoment H raw98step0 = injectiveMoment H raw98step1 := by
      have heq : raw98step1 = (fun i j => raw98step0 (permutation41 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw98step0 permutation41 permutation6
    _ = injectiveMoment H node736 := by rfl

def raw99 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]

def raw99step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]

def raw99step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical99 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw99 = injectiveMoment H node738 := by
  calc
    injectiveMoment H raw99 = injectiveMoment H raw99step0 := by
      have heq : raw99step0 = -raw99 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw99).symm
    injectiveMoment H raw99step0 = injectiveMoment H raw99step1 := by
      have heq : raw99step1 = (fun i j => raw99step0 (permutation43 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw99step0 permutation43 permutation6
    _ = injectiveMoment H node738 := by rfl

def raw100 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]

def raw100step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 3, -4]]

theorem canonical100 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw100 = injectiveMoment H node242 := by
  calc
    injectiveMoment H raw100 = injectiveMoment H raw100step0 := by
      have heq : raw100step0 = (fun i j => raw100 (permutation30 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw100 permutation30 permutation6
    _ = injectiveMoment H node242 := by rfl

def raw101 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]

def raw101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]

def raw101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical101 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw101 = injectiveMoment H node744 := by
  calc
    injectiveMoment H raw101 = injectiveMoment H raw101step0 := by
      have heq : raw101step0 = -raw101 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw101).symm
    injectiveMoment H raw101step0 = injectiveMoment H raw101step1 := by
      have heq : raw101step1 = (fun i j => raw101step0 (permutation55 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw101step0 permutation55 permutation6
    _ = injectiveMoment H node744 := by rfl

def raw102 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]

def raw102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]

def raw102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical102 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw102 = injectiveMoment H node743 := by
  calc
    injectiveMoment H raw102 = injectiveMoment H raw102step0 := by
      have heq : raw102step0 = -raw102 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw102).symm
    injectiveMoment H raw102step0 = injectiveMoment H raw102step1 := by
      have heq : raw102step1 = (fun i j => raw102step0 (permutation49 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw102step0 permutation49 permutation6
    _ = injectiveMoment H node743 := by rfl

def raw103 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]

def raw103step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-3, -1, 4]]

def raw103step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 4, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical103 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw103 = injectiveMoment H node249 := by
  calc
    injectiveMoment H raw103 = injectiveMoment H raw103step0 := by
      have heq : raw103step0 = -raw103 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw103).symm
    injectiveMoment H raw103step0 = injectiveMoment H raw103step1 := by
      have heq : raw103step1 = (fun i j => raw103step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw103step0 permutation28 permutation5
    _ = injectiveMoment H node249 := by rfl

def raw104 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]

def raw104step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-2, 1, 1], ![-2, -1, 3]]

def raw104step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical104 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw104 = injectiveMoment H node247 := by
  calc
    injectiveMoment H raw104 = injectiveMoment H raw104step0 := by
      have heq : raw104step0 = -raw104 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw104).symm
    injectiveMoment H raw104step0 = injectiveMoment H raw104step1 := by
      have heq : raw104step1 = (fun i j => raw104step0 (permutation13 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw104step0 permutation13 permutation6
    _ = injectiveMoment H node247 := by rfl

def raw105 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]

def raw105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]

def raw105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

theorem canonical105 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw105 = injectiveMoment H node324 := by
  calc
    injectiveMoment H raw105 = injectiveMoment H raw105step0 := by
      have heq : raw105step0 = -raw105 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw105).symm
    injectiveMoment H raw105step0 = injectiveMoment H raw105step1 := by
      have heq : raw105step1 = (fun i j => raw105step0 (permutation51 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw105step0 permutation51 permutation8
    _ = injectiveMoment H node324 := by rfl

def raw106 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]

def raw106step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

theorem canonical106 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw106 = injectiveMoment H node90 := by
  calc
    injectiveMoment H raw106 = injectiveMoment H raw106step0 := by
      have heq : raw106step0 = (fun i j => raw106 (permutation30 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw106 permutation30 permutation6
    _ = injectiveMoment H node90 := by rfl

def raw107 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]

def raw107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical107 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw107 = injectiveMoment H node701 := by
  calc
    injectiveMoment H raw107 = injectiveMoment H raw107step0 := by
      have heq : raw107step0 = (fun i j => raw107 (permutation103 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw107 permutation103 permutation6
    _ = injectiveMoment H node701 := by rfl

def raw108 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]

def raw108step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, -1, 0], ![1, 3, -4]]

theorem canonical108 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw108 = injectiveMoment H node221 := by
  calc
    injectiveMoment H raw108 = injectiveMoment H raw108step0 := by
      have heq : raw108step0 = (fun i j => raw108 (permutation26 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw108 permutation26 permutation6
    _ = injectiveMoment H node221 := by rfl

def raw109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw109step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw109step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical109 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw109 = injectiveMoment H node2380 := by
  calc
    injectiveMoment H raw109 = injectiveMoment H raw109step0 := by
      have heq : raw109step0 = -raw109 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw109).symm
    injectiveMoment H raw109step0 = injectiveMoment H raw109step1 := by
      have heq : raw109step1 = (fun i j => raw109step0 (permutation164 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw109step0 permutation164 permutation6
    _ = injectiveMoment H node2380 := by rfl

def raw110 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]

def raw110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical110 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw110 = injectiveMoment H node739 := by
  calc
    injectiveMoment H raw110 = injectiveMoment H raw110step0 := by
      have heq : raw110step0 = -raw110 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw110).symm
    injectiveMoment H raw110step0 = injectiveMoment H raw110step1 := by
      have heq : raw110step1 = (fun i j => raw110step0 (permutation37 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw110step0 permutation37 permutation6
    _ = injectiveMoment H node739 := by rfl

def raw111 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]

def raw111step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical111 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw111 = injectiveMoment H node737 := by
  calc
    injectiveMoment H raw111 = injectiveMoment H raw111step0 := by
      have heq : raw111step0 = -raw111 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw111).symm
    injectiveMoment H raw111step0 = injectiveMoment H raw111step1 := by
      have heq : raw111step1 = (fun i j => raw111step0 (permutation35 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw111step0 permutation35 permutation6
    _ = injectiveMoment H node737 := by rfl

def raw112 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]

def raw112step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]

def raw112step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3]]

theorem canonical112 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw112 = injectiveMoment H node243 := by
  calc
    injectiveMoment H raw112 = injectiveMoment H raw112step0 := by
      have heq : raw112step0 = -raw112 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw112).symm
    injectiveMoment H raw112step0 = injectiveMoment H raw112step1 := by
      have heq : raw112step1 = (fun i j => raw112step0 (permutation9 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw112step0 permutation9 permutation6
    _ = injectiveMoment H node243 := by rfl

def raw113 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical113 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw113 = injectiveMoment H node653 := by
  calc
    injectiveMoment H raw113 = injectiveMoment H raw113step0 := by
      have heq : raw113step0 = (fun i j => raw113 (permutation144 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw113 permutation144 permutation6
    _ = injectiveMoment H node653 := by rfl

def raw114 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]

def raw114step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical114 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw114 = injectiveMoment H node173 := by
  calc
    injectiveMoment H raw114 = injectiveMoment H raw114step0 := by
      have heq : raw114step0 = (fun i j => raw114 (permutation32 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw114 permutation32 permutation6
    _ = injectiveMoment H node173 := by rfl

def raw115 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]

def raw115step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]

def raw115step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]

theorem canonical115 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw115 = injectiveMoment H node87 := by
  calc
    injectiveMoment H raw115 = injectiveMoment H raw115step0 := by
      have heq : raw115step0 = -raw115 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw115).symm
    injectiveMoment H raw115step0 = injectiveMoment H raw115step1 := by
      have heq : raw115step1 = (fun i j => raw115step0 (permutation13 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw115step0 permutation13 permutation8
    _ = injectiveMoment H node87 := by rfl

def raw116 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]

def raw116step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

theorem canonical116 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw116 = injectiveMoment H node201 := by
  calc
    injectiveMoment H raw116 = injectiveMoment H raw116step0 := by
      have heq : raw116step0 = (fun i j => raw116 (permutation26 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw116 permutation26 permutation6
    _ = injectiveMoment H node201 := by rfl

def raw117 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]

def raw117step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]

def raw117step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

theorem canonical117 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw117 = injectiveMoment H node244 := by
  calc
    injectiveMoment H raw117 = injectiveMoment H raw117step0 := by
      have heq : raw117step0 = -raw117 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw117).symm
    injectiveMoment H raw117step0 = injectiveMoment H raw117step1 := by
      have heq : raw117step1 = (fun i j => raw117step0 (permutation9 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw117step0 permutation9 permutation6
    _ = injectiveMoment H node244 := by rfl

def raw118 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]

def raw118step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![3, -1, -2]]

def raw118step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

theorem canonical118 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw118 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw118 = injectiveMoment H raw118step0 := by
      have heq : raw118step0 = raw118.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw118).symm
    injectiveMoment H raw118step0 = injectiveMoment H raw118step1 := by
      have heq : raw118step1 = (fun i j => raw118step0 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw118step0 permutation7 permutation6
    _ = injectiveMoment H node59 := by rfl

def raw119 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]

def raw119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]

def raw119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

theorem canonical119 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw119 = injectiveMoment H node317 := by
  calc
    injectiveMoment H raw119 = injectiveMoment H raw119step0 := by
      have heq : raw119step0 = -raw119 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw119).symm
    injectiveMoment H raw119step0 = injectiveMoment H raw119step1 := by
      have heq : raw119step1 = (fun i j => raw119step0 (permutation44 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw119step0 permutation44 permutation8
    _ = injectiveMoment H node317 := by rfl

def raw120 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]

def raw120step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]

def raw120step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]

theorem canonical120 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw120 = injectiveMoment H node88 := by
  calc
    injectiveMoment H raw120 = injectiveMoment H raw120step0 := by
      have heq : raw120step0 = -raw120 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw120).symm
    injectiveMoment H raw120step0 = injectiveMoment H raw120step1 := by
      have heq : raw120step1 = (fun i j => raw120step0 (permutation14 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw120step0 permutation14 permutation8
    _ = injectiveMoment H node88 := by rfl

def raw121 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]

def raw121step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]

def raw121step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

theorem canonical121 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw121 = injectiveMoment H node85 := by
  calc
    injectiveMoment H raw121 = injectiveMoment H raw121step0 := by
      have heq : raw121step0 = -raw121 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw121).symm
    injectiveMoment H raw121step0 = injectiveMoment H raw121step1 := by
      have heq : raw121step1 = (fun i j => raw121step0 (permutation12 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw121step0 permutation12 permutation8
    _ = injectiveMoment H node85 := by rfl

def raw122 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![4, -3, -1]]

def raw122step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]

def raw122step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![2, -3, 1]]

theorem canonical122 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw122 = injectiveMoment H node38 := by
  calc
    injectiveMoment H raw122 = injectiveMoment H raw122step0 := by
      have heq : raw122step0 = raw122.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw122).symm
    injectiveMoment H raw122step0 = injectiveMoment H raw122step1 := by
      have heq : raw122step1 = (fun i j => raw122step0 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw122step0 permutation7 permutation6
    _ = injectiveMoment H node38 := by rfl

def raw123 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]

def raw123step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -3, 2], ![1, 3, -4]]

theorem canonical123 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw123 = injectiveMoment H node228 := by
  calc
    injectiveMoment H raw123 = injectiveMoment H raw123step0 := by
      have heq : raw123step0 = (fun i j => raw123 (permutation18 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw123 permutation18 permutation6
    _ = injectiveMoment H node228 := by rfl

def raw124 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]

def raw124step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

theorem canonical124 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw124 = injectiveMoment H node225 := by
  calc
    injectiveMoment H raw124 = injectiveMoment H raw124step0 := by
      have heq : raw124step0 = (fun i j => raw124 (permutation20 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw124 permutation20 permutation6
    _ = injectiveMoment H node225 := by rfl

def raw125 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]

def raw125step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -4, 3], ![1, 3, -4]]

theorem canonical125 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw125 = injectiveMoment H node42 := by
  calc
    injectiveMoment H raw125 = injectiveMoment H raw125step0 := by
      have heq : raw125step0 = (fun i j => raw125 (permutation5 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw125 permutation5 permutation5
    _ = injectiveMoment H node42 := by rfl

def raw126 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]

def raw126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical126 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw126 = injectiveMoment H node742 := by
  calc
    injectiveMoment H raw126 = injectiveMoment H raw126step0 := by
      have heq : raw126step0 = -raw126 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw126).symm
    injectiveMoment H raw126step0 = injectiveMoment H raw126step1 := by
      have heq : raw126step1 = (fun i j => raw126step0 (permutation55 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw126step0 permutation55 permutation6
    _ = injectiveMoment H node742 := by rfl

def raw127 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]

def raw127step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]

def raw127step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical127 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw127 = injectiveMoment H node248 := by
  calc
    injectiveMoment H raw127 = injectiveMoment H raw127step0 := by
      have heq : raw127step0 = -raw127 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw127).symm
    injectiveMoment H raw127step0 = injectiveMoment H raw127step1 := by
      have heq : raw127step1 = (fun i j => raw127step0 (permutation13 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw127step0 permutation13 permutation6
    _ = injectiveMoment H node248 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

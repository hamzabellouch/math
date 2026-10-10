import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8256 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![-1, 1, 0, 0], ![1, 0, -1, 0]]

def raw8256step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

theorem canonical8256 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8256 = injectiveMoment H node2759 := by
  calc
    injectiveMoment H raw8256 = injectiveMoment H raw8256step0 := by
      have heq : raw8256step0 = (fun i j => raw8256 (permutation116 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8256 permutation116 permutation14
    _ = injectiveMoment H node2759 := by rfl

def raw8257 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, 0, -1, 1]]

def raw8257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]

def raw8257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

theorem canonical8257 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8257 = injectiveMoment H node668 := by
  calc
    injectiveMoment H raw8257 = injectiveMoment H raw8257step0 := by
      have hz : ∀ i, raw8257 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8257step0 = (fun i j => raw8257 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8257 permutation9 hz
    injectiveMoment H raw8257step0 = injectiveMoment H raw8257step1 := by
      have heq : raw8257step1 = (fun i j => raw8257step0 (permutation37 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8257step0 permutation37 permutation4
    _ = injectiveMoment H node668 := by rfl

def raw8258 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![0, 0, -1, 1]]

def raw8258step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![0, -1, 1]]

def raw8258step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

theorem canonical8258 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8258 = injectiveMoment H node207 := by
  calc
    injectiveMoment H raw8258 = injectiveMoment H raw8258step0 := by
      have hz : ∀ i, raw8258 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8258step0 = (fun i j => raw8258 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8258 permutation9 hz
    injectiveMoment H raw8258step0 = injectiveMoment H raw8258step1 := by
      have heq : raw8258step1 = (fun i j => raw8258step0 (permutation10 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8258step0 permutation10 permutation4
    _ = injectiveMoment H node207 := by rfl

def raw8259 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, 1, -1], ![-1, 1, -3, 3], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8259step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -2, 0], ![0, 0, -1, 1], ![1, -1, 3, -3], ![0, -1, 0, 1], ![-1, 0, 0, 1]]

def raw8259step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -2, 0], ![1, -1, 3, -3]]

theorem canonical8259 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8259 = injectiveMoment H node2754 := by
  calc
    injectiveMoment H raw8259 = injectiveMoment H raw8259step0 := by
      have heq : raw8259step0 = -raw8259 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8259).symm
    injectiveMoment H raw8259step0 = injectiveMoment H raw8259step1 := by
      have heq : raw8259step1 = (fun i j => raw8259step0 (permutation147 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8259step0 permutation147 permutation9
    _ = injectiveMoment H node2754 := by rfl

def raw8260 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, 1, -1], ![0, 1, -3, 2], ![-1, 1, 0, 0], ![1, 0, 0, -1]]

def raw8260step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -2, 0], ![0, 0, -1, 1], ![0, -1, 3, -2], ![1, -1, 0, 0], ![-1, 0, 0, 1]]

def raw8260step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

theorem canonical8260 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8260 = injectiveMoment H node2810 := by
  calc
    injectiveMoment H raw8260 = injectiveMoment H raw8260step0 := by
      have heq : raw8260step0 = -raw8260 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8260).symm
    injectiveMoment H raw8260step0 = injectiveMoment H raw8260step1 := by
      have heq : raw8260step1 = (fun i j => raw8260step0 (permutation141 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8260step0 permutation141 permutation10
    _ = injectiveMoment H node2810 := by rfl

def raw8261 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, 1, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![0, 0, 0, 0]]

def raw8261step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -2, 0], ![0, 0, -1, 1], ![0, -1, 3, -2], ![0, -1, 0, 1], ![0, 0, 0, 0]]

def raw8261step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, -2, 0], ![0, 0, -1, 1], ![0, -1, 3, -2], ![0, -1, 0, 1]]

def raw8261step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1]]

def raw8261step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8261 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8261 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw8261 = injectiveMoment H raw8261step0 := by
      have heq : raw8261step0 = -raw8261 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8261).symm
    injectiveMoment H raw8261step0 = injectiveMoment H raw8261step1 := by
      have hz : ∀ j, raw8261step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw8261step1 = (fun i j => raw8261step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8261step0 permutation128 hz
    injectiveMoment H raw8261step1 = injectiveMoment H raw8261step2 := by
      have hz : ∀ i, raw8261step1 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8261step2 = (fun i j => raw8261step1 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8261step1 permutation9 hz
    injectiveMoment H raw8261step2 = injectiveMoment H raw8261step3 := by
      have heq : raw8261step3 = (fun i j => raw8261step2 (permutation22 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8261step2 permutation22 permutation7
    _ = injectiveMoment H node185 := by rfl

def raw8262 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![1, -1, 1, -1], ![-1, 3, -3, 1]]

def raw8262step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, -1, 3], ![2, 1, -3], ![0, -1, 1]]

def raw8262step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

theorem canonical8262 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8262 = injectiveMoment H node168 := by
  calc
    injectiveMoment H raw8262 = injectiveMoment H raw8262step0 := by
      have heq : raw8262step0 = raw8262.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8262).symm
    injectiveMoment H raw8262step0 = injectiveMoment H raw8262step1 := by
      have heq : raw8262step1 = (fun i j => raw8262step0 (permutation19 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8262step0 permutation19 permutation3
    _ = injectiveMoment H node168 := by rfl

def raw8263 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![1, 0, 0, -1], ![-1, 2, -2, 1]]

def raw8263step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![2, 0, -2], ![0, -1, 1]]

def raw8263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

theorem canonical8263 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8263 = injectiveMoment H node291 := by
  calc
    injectiveMoment H raw8263 = injectiveMoment H raw8263step0 := by
      have heq : raw8263step0 = raw8263.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8263).symm
    injectiveMoment H raw8263step0 = injectiveMoment H raw8263step1 := by
      have heq : raw8263step1 = (fun i j => raw8263step0 (permutation30 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8263step0 permutation30 permutation5
    _ = injectiveMoment H node291 := by rfl

def raw8264 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![1, 0, 1, -2], ![-1, 2, -3, 2]]

def raw8264step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 0, 2], ![2, 1, -3], ![0, -2, 2]]

def raw8264step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![2, 0, -2], ![-2, -1, 3], ![0, 2, -2]]

def raw8264step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical8264 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8264 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw8264 = injectiveMoment H raw8264step0 := by
      have heq : raw8264step0 = raw8264.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8264).symm
    injectiveMoment H raw8264step0 = injectiveMoment H raw8264step1 := by
      have heq : raw8264step1 = -raw8264step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8264step0).symm
    injectiveMoment H raw8264step1 = injectiveMoment H raw8264step2 := by
      have heq : raw8264step2 = (fun i j => raw8264step1 (permutation22 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8264step1 permutation22 permutation3
    _ = injectiveMoment H node169 := by rfl

def raw8265 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![1, 1, 1, -3], ![-1, 1, -3, 3]]

def raw8265step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-2, 1, 1], ![2, 1, -3], ![0, -3, 3]]

def raw8265step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![2, -1, -1], ![-2, -1, 3], ![0, 3, -3]]

def raw8265step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

theorem canonical8265 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8265 = injectiveMoment H node170 := by
  calc
    injectiveMoment H raw8265 = injectiveMoment H raw8265step0 := by
      have heq : raw8265step0 = raw8265.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8265).symm
    injectiveMoment H raw8265step0 = injectiveMoment H raw8265step1 := by
      have heq : raw8265step1 = -raw8265step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8265step0).symm
    injectiveMoment H raw8265step1 = injectiveMoment H raw8265step2 := by
      have heq : raw8265step2 = (fun i j => raw8265step1 (permutation22 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8265step1 permutation22 permutation3
    _ = injectiveMoment H node170 := by rfl

def raw8266 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![2, -1, 1, -2], ![-2, 3, -3, 2]]

def raw8266step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![-2, -1, 3], ![2, 1, -3], ![0, -2, 2]]

def raw8266step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]

theorem canonical8266 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8266 = injectiveMoment H node162 := by
  calc
    injectiveMoment H raw8266 = injectiveMoment H raw8266step0 := by
      have heq : raw8266step0 = raw8266.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8266).symm
    injectiveMoment H raw8266step0 = injectiveMoment H raw8266step1 := by
      have heq : raw8266step1 = (fun i j => raw8266step0 (permutation19 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8266step0 permutation19 permutation3
    _ = injectiveMoment H node162 := by rfl

def raw8267 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![2, 0, 0, -2], ![-2, 2, -2, 2]]

def raw8267step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![-2, 0, 2], ![2, 0, -2], ![0, -2, 2]]

def raw8267step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

theorem canonical8267 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8267 = injectiveMoment H node197 := by
  calc
    injectiveMoment H raw8267 = injectiveMoment H raw8267step0 := by
      have heq : raw8267step0 = raw8267.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8267).symm
    injectiveMoment H raw8267step0 = injectiveMoment H raw8267step1 := by
      have heq : raw8267step1 = (fun i j => raw8267step0 (permutation19 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8267step0 permutation19 permutation3
    _ = injectiveMoment H node197 := by rfl

def raw8268 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![2, 0, 1, -3], ![-2, 2, -3, 3]]

def raw8268step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![-2, 0, 2], ![2, 1, -3], ![0, -3, 3]]

def raw8268step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, 0, -2], ![-2, -1, 3], ![0, 3, -3]]

def raw8268step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

theorem canonical8268 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8268 = injectiveMoment H node163 := by
  calc
    injectiveMoment H raw8268 = injectiveMoment H raw8268step0 := by
      have heq : raw8268step0 = raw8268.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8268).symm
    injectiveMoment H raw8268step0 = injectiveMoment H raw8268step1 := by
      have heq : raw8268step1 = -raw8268step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8268step0).symm
    injectiveMoment H raw8268step1 = injectiveMoment H raw8268step2 := by
      have heq : raw8268step2 = (fun i j => raw8268step1 (permutation22 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8268step1 permutation22 permutation3
    _ = injectiveMoment H node163 := by rfl

def raw8269 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 3, -1], ![-1, 1, -3, 3], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8269step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 1, 0], ![3, -3, 0, 0], ![-1, 3, -1, -1]]

def raw8269step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem canonical8269 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8269 = injectiveMoment H node977 := by
  calc
    injectiveMoment H raw8269 = injectiveMoment H raw8269step0 := by
      have heq : raw8269step0 = raw8269.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8269).symm
    injectiveMoment H raw8269step0 = injectiveMoment H raw8269step1 := by
      have heq : raw8269step1 = (fun i j => raw8269step0 (permutation32 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8269step0 permutation32 permutation31
    _ = injectiveMoment H node977 := by rfl

def raw8270 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 3, -1], ![0, 1, -3, 2], ![-1, 1, 0, 0], ![1, 0, 0, -1]]

def raw8270step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 1, 0], ![3, -3, 0, 0], ![-1, 2, 0, -1]]

def raw8270step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0]]

theorem canonical8270 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8270 = injectiveMoment H node1267 := by
  calc
    injectiveMoment H raw8270 = injectiveMoment H raw8270step0 := by
      have heq : raw8270step0 = raw8270.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8270).symm
    injectiveMoment H raw8270step0 = injectiveMoment H raw8270step1 := by
      have heq : raw8270step1 = (fun i j => raw8270step0 (permutation32 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8270step0 permutation32 permutation31
    _ = injectiveMoment H node1267 := by rfl

def raw8271 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 3, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![0, 0, 0, 0]]

def raw8271step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 0, 0], ![-2, 1, 1, 0], ![3, -3, 0, 0], ![-1, 2, -1, 0]]

def raw8271step1 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![3, -3, 0, 0], ![-1, 2, -1, 0]]

def raw8271step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![3, -3, 0], ![-1, 2, -1]]

def raw8271step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

theorem canonical8271 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8271 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw8271 = injectiveMoment H raw8271step0 := by
      have heq : raw8271step0 = raw8271.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8271).symm
    injectiveMoment H raw8271step0 = injectiveMoment H raw8271step1 := by
      have hz : ∀ j, raw8271step0 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8271step1 = (fun i j => raw8271step0 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8271step0 permutation9 hz
    injectiveMoment H raw8271step1 = injectiveMoment H raw8271step2 := by
      have hz : ∀ i, raw8271step1 i (permutation27 0) = 0 := by decide +kernel
      have heq : raw8271step2 = (fun i j => raw8271step1 i (permutation27 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8271step1 permutation27 hz
    injectiveMoment H raw8271step2 = injectiveMoment H raw8271step3 := by
      have heq : raw8271step3 = (fun i j => raw8271step2 (permutation8 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8271step2 permutation8 permutation7
    _ = injectiveMoment H node63 := by rfl

def raw8272 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, -3, 4], ![-1, 0, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw8272step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

theorem canonical8272 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8272 = injectiveMoment H node2825 := by
  calc
    injectiveMoment H raw8272 = injectiveMoment H raw8272step0 := by
      have heq : raw8272step0 = (fun i j => raw8272 (permutation57 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8272 permutation57 permutation9
    _ = injectiveMoment H node2825 := by rfl

def raw8273 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw8273step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, -1, 1, -1]]

theorem canonical8273 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8273 = injectiveMoment H node1306 := by
  calc
    injectiveMoment H raw8273 = injectiveMoment H raw8273step0 := by
      have heq : raw8273step0 = (fun i j => raw8273 (permutation15 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8273 permutation15 permutation9
    _ = injectiveMoment H node1306 := by rfl

def raw8274 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![-1, 0, 3, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw8274step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![-3, 3, 0, 0], ![4, -2, -2, 0]]

def raw8274step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, -2, 1], ![3, -3, 0, 0], ![-4, 2, 2, 0]]

def raw8274step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -3, 3], ![0, 2, 2, -4], ![1, -2, 0, 1]]

theorem canonical8274 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8274 = injectiveMoment H node1300 := by
  calc
    injectiveMoment H raw8274 = injectiveMoment H raw8274step0 := by
      have heq : raw8274step0 = raw8274.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8274).symm
    injectiveMoment H raw8274step0 = injectiveMoment H raw8274step1 := by
      have heq : raw8274step1 = -raw8274step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8274step0).symm
    injectiveMoment H raw8274step1 = injectiveMoment H raw8274step2 := by
      have heq : raw8274step2 = (fun i j => raw8274step1 (permutation12 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8274step1 permutation12 permutation32
    _ = injectiveMoment H node1300 := by rfl

def raw8275 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw8275step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 3, -4], ![1, -1, -1, 1], ![0, -1, -1, 2], ![-1, 1, -1, 1]]

def raw8275step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

theorem canonical8275 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8275 = injectiveMoment H node1341 := by
  calc
    injectiveMoment H raw8275 = injectiveMoment H raw8275step0 := by
      have heq : raw8275step0 = -raw8275 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8275).symm
    injectiveMoment H raw8275step0 = injectiveMoment H raw8275step1 := by
      have heq : raw8275step1 = (fun i j => raw8275step0 (permutation31 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8275step0 permutation31 permutation9
    _ = injectiveMoment H node1341 := by rfl

def raw8276 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![-1, 1, 1, -1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw8276step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 3, -4], ![1, -1, -1, 1], ![0, -1, -2, 3], ![-1, 1, 0, 0]]

def raw8276step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, -1, -1, 1]]

theorem canonical8276 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8276 = injectiveMoment H node1354 := by
  calc
    injectiveMoment H raw8276 = injectiveMoment H raw8276step0 := by
      have heq : raw8276step0 = -raw8276 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8276).symm
    injectiveMoment H raw8276step0 = injectiveMoment H raw8276step1 := by
      have heq : raw8276step1 = (fun i j => raw8276step0 (permutation31 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8276step0 permutation31 permutation9
    _ = injectiveMoment H node1354 := by rfl

def raw8277 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![-1, 1, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw8277step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![-3, 2, 1, 0], ![4, -2, -2, 0]]

def raw8277step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, -1, -1, 1], ![3, -2, -1, 0], ![-4, 2, 2, 0]]

def raw8277step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, -1, -1, 1]]

theorem canonical8277 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8277 = injectiveMoment H node1298 := by
  calc
    injectiveMoment H raw8277 = injectiveMoment H raw8277step0 := by
      have heq : raw8277step0 = raw8277.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8277).symm
    injectiveMoment H raw8277step0 = injectiveMoment H raw8277step1 := by
      have heq : raw8277step1 = -raw8277step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8277step0).symm
    injectiveMoment H raw8277step1 = injectiveMoment H raw8277step2 := by
      have heq : raw8277step2 = (fun i j => raw8277step1 (permutation12 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8277step1 permutation12 permutation32
    _ = injectiveMoment H node1298 := by rfl

def raw8278 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, -1, 2, -1], ![0, 2, 1, -3]]

def raw8278step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 3, -4], ![0, 1, -2, 1], ![0, -2, -1, 3]]

def raw8278step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-2, -1, 3]]

def raw8278step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 3, -4]]

theorem canonical8278 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8278 = injectiveMoment H node40 := by
  calc
    injectiveMoment H raw8278 = injectiveMoment H raw8278step0 := by
      have heq : raw8278step0 = -raw8278 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8278).symm
    injectiveMoment H raw8278step0 = injectiveMoment H raw8278step1 := by
      have hz : ∀ i, raw8278step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8278step1 = (fun i j => raw8278step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8278step0 permutation9 hz
    injectiveMoment H raw8278step1 = injectiveMoment H raw8278step2 := by
      have heq : raw8278step2 = (fun i j => raw8278step1 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8278step1 permutation8 permutation3
    _ = injectiveMoment H node40 := by rfl

def raw8279 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, -1, 3, -2], ![0, 2, 0, -2]]

def raw8279step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![-1, -1, 2], ![-3, 3, 0], ![4, -2, -2]]

def raw8279step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![4, -2, -2]]

def raw8279step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

theorem canonical8279 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8279 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw8279 = injectiveMoment H raw8279step0 := by
      have heq : raw8279step0 = raw8279.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8279).symm
    injectiveMoment H raw8279step0 = injectiveMoment H raw8279step1 := by
      have hz : ∀ j, raw8279step0 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8279step1 = (fun i j => raw8279step0 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8279step0 permutation9 hz
    injectiveMoment H raw8279step1 = injectiveMoment H raw8279step2 := by
      have heq : raw8279step2 = (fun i j => raw8279step1 (permutation8 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8279step1 permutation8 permutation8
    _ = injectiveMoment H node32 := by rfl

def raw8280 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, 0, 1, -1], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw8280step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

theorem canonical8280 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8280 = injectiveMoment H node2825 := by
  calc
    injectiveMoment H raw8280 = injectiveMoment H raw8280step0 := by
      have heq : raw8280step0 = (fun i j => raw8280 (permutation80 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8280 permutation80 permutation9
    _ = injectiveMoment H node2825 := by rfl

def raw8281 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, -1, 1, -1]]

def raw8281step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![-3, 1, 1, 1], ![4, -1, -2, -1]]

def raw8281step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, 1, -3]]

theorem canonical8281 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8281 = injectiveMoment H node893 := by
  calc
    injectiveMoment H raw8281 = injectiveMoment H raw8281step0 := by
      have heq : raw8281step0 = raw8281.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8281).symm
    injectiveMoment H raw8281step0 = injectiveMoment H raw8281step1 := by
      have heq : raw8281step1 = (fun i j => raw8281step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8281step0 permutation29 permutation20
    _ = injectiveMoment H node893 := by rfl

def raw8282 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, -1, 0, 0]]

def raw8282step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 3, -4], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, -1, 2], ![-1, 1, 0, 0]]

def raw8282step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, -1, 2]]

theorem canonical8282 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8282 = injectiveMoment H node2853 := by
  calc
    injectiveMoment H raw8282 = injectiveMoment H raw8282step0 := by
      have heq : raw8282step0 = -raw8282 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8282).symm
    injectiveMoment H raw8282step0 = injectiveMoment H raw8282step1 := by
      have heq : raw8282step1 = (fun i j => raw8282step0 (permutation135 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8282step0 permutation135 permutation9
    _ = injectiveMoment H node2853 := by rfl

def raw8283 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, -1, 1, 0]]

def raw8283step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 3, -4], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -2, 0, 2], ![0, 1, -1, 0]]

def raw8283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2], ![1, -1, 0]]

def raw8283step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical8283 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8283 = injectiveMoment H node653 := by
  calc
    injectiveMoment H raw8283 = injectiveMoment H raw8283step0 := by
      have heq : raw8283step0 = -raw8283 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8283).symm
    injectiveMoment H raw8283step0 = injectiveMoment H raw8283step1 := by
      have hz : ∀ i, raw8283step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8283step1 = (fun i j => raw8283step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8283step0 permutation9 hz
    injectiveMoment H raw8283step1 = injectiveMoment H raw8283step2 := by
      have heq : raw8283step2 = (fun i j => raw8283step1 (permutation113 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8283step1 permutation113 permutation3
    _ = injectiveMoment H node653 := by rfl

def raw8284 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, -1, 2, -1]]

def raw8284step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 3, -4], ![0, 0, -1, 1], ![0, -2, 0, 2], ![0, 1, -2, 1]]

def raw8284step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-2, 0, 2], ![1, -2, 1]]

def raw8284step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

theorem canonical8284 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8284 = injectiveMoment H node206 := by
  calc
    injectiveMoment H raw8284 = injectiveMoment H raw8284step0 := by
      have heq : raw8284step0 = -raw8284 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8284).symm
    injectiveMoment H raw8284step0 = injectiveMoment H raw8284step1 := by
      have hz : ∀ i, raw8284step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8284step1 = (fun i j => raw8284step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8284step0 permutation9 hz
    injectiveMoment H raw8284step1 = injectiveMoment H raw8284step2 := by
      have heq : raw8284step2 = (fun i j => raw8284step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8284step1 permutation24 permutation3
    _ = injectiveMoment H node206 := by rfl

def raw8285 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, 0, 2, -2], ![-1, 2, 1, -2], ![1, -1, 0, 0]]

def raw8285step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![-3, 2, 1, 0], ![4, -2, -2, 0]]

def raw8285step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![3, -2, -1, 0], ![-4, 2, 2, 0]]

def raw8285step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -1, 3], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical8285 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8285 = injectiveMoment H node1295 := by
  calc
    injectiveMoment H raw8285 = injectiveMoment H raw8285step0 := by
      have heq : raw8285step0 = raw8285.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8285).symm
    injectiveMoment H raw8285step0 = injectiveMoment H raw8285step1 := by
      have heq : raw8285step1 = -raw8285step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8285step0).symm
    injectiveMoment H raw8285step1 = injectiveMoment H raw8285step2 := by
      have heq : raw8285step2 = (fun i j => raw8285step1 (permutation12 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8285step1 permutation12 permutation30
    _ = injectiveMoment H node1295 := by rfl

def raw8286 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2]]

def raw8286step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

theorem canonical8286 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8286 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw8286 = injectiveMoment H raw8286step0 := by
      have hz : ∀ i, raw8286 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8286step0 = (fun i j => raw8286 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8286 permutation9 hz
    _ = injectiveMoment H node52 := by rfl

def raw8287 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![0, -1, 1, 0]]

def raw8287step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 3, -4], ![0, 0, -2, 2], ![0, -2, 0, 2], ![0, 1, -1, 0]]

def raw8287step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -2, 2], ![-2, 0, 2], ![1, -1, 0]]

def raw8287step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

theorem canonical8287 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8287 = injectiveMoment H node201 := by
  calc
    injectiveMoment H raw8287 = injectiveMoment H raw8287step0 := by
      have heq : raw8287step0 = -raw8287 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8287).symm
    injectiveMoment H raw8287step0 = injectiveMoment H raw8287step1 := by
      have hz : ∀ i, raw8287step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8287step1 = (fun i j => raw8287step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8287step0 permutation9 hz
    injectiveMoment H raw8287step1 = injectiveMoment H raw8287step2 := by
      have heq : raw8287step2 = (fun i j => raw8287step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8287step1 permutation24 permutation3
    _ = injectiveMoment H node201 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

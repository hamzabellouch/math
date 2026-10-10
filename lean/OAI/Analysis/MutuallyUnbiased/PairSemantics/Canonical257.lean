import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8224 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-4, 3, -1, 2], ![4, -1, -1, -2]]

def raw8224step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![-2, 3, -1], ![2, -1, -1], ![0, 2, -2]]

def raw8224step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 4, -4], ![2, -1, -1]]

theorem canonical8224 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8224 = injectiveMoment H node164 := by
  calc
    injectiveMoment H raw8224 = injectiveMoment H raw8224step0 := by
      have heq : raw8224step0 = raw8224.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8224).symm
    injectiveMoment H raw8224step0 = injectiveMoment H raw8224step1 := by
      have heq : raw8224step1 = (fun i j => raw8224step0 (permutation19 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8224step0 permutation19 permutation4
    _ = injectiveMoment H node164 := by rfl

def raw8225 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-3, 1, -1, 3], ![3, 1, -1, -3]]

def raw8225step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-2, 1, 1], ![2, -1, -1], ![0, 3, -3]]

def raw8225step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 3, -3], ![2, -1, -1]]

theorem canonical8225 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8225 = injectiveMoment H node220 := by
  calc
    injectiveMoment H raw8225 = injectiveMoment H raw8225step0 := by
      have heq : raw8225step0 = raw8225.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8225).symm
    injectiveMoment H raw8225step0 = injectiveMoment H raw8225step1 := by
      have heq : raw8225step1 = (fun i j => raw8225step0 (permutation16 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8225step0 permutation16 permutation3
    _ = injectiveMoment H node220 := by rfl

def raw8226 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-3, 1, 0, 2], ![3, 1, -2, -2]]

def raw8226step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-2, 1, 1], ![2, 0, -2], ![0, 2, -2]]

def raw8226step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-2, 0, 2], ![0, -2, 2]]

def raw8226step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

theorem canonical8226 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8226 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw8226 = injectiveMoment H raw8226step0 := by
      have heq : raw8226step0 = raw8226.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8226).symm
    injectiveMoment H raw8226step0 = injectiveMoment H raw8226step1 := by
      have heq : raw8226step1 = -raw8226step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8226step0).symm
    injectiveMoment H raw8226step1 = injectiveMoment H raw8226step2 := by
      have heq : raw8226step2 = (fun i j => raw8226step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8226step1 permutation25 permutation3
    _ = injectiveMoment H node198 := by rfl

def raw8227 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-3, 2, -1, 2], ![3, 0, -1, -2]]

def raw8227step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-2, 2, 0], ![2, -1, -1], ![0, 2, -2]]

def raw8227step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

theorem canonical8227 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8227 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw8227 = injectiveMoment H raw8227step0 := by
      have heq : raw8227step0 = raw8227.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8227).symm
    injectiveMoment H raw8227step0 = injectiveMoment H raw8227step1 := by
      have heq : raw8227step1 = (fun i j => raw8227step0 (permutation19 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8227step0 permutation19 permutation4
    _ = injectiveMoment H node198 := by rfl

def raw8228 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-3, 2, 0, 1], ![3, 0, -2, -1]]

def raw8228step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-2, 2, 0], ![2, 0, -2], ![0, 1, -1]]

def raw8228step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -2, 0]]

theorem canonical8228 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8228 = injectiveMoment H node204 := by
  calc
    injectiveMoment H raw8228 = injectiveMoment H raw8228step0 := by
      have heq : raw8228step0 = raw8228.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8228).symm
    injectiveMoment H raw8228step0 = injectiveMoment H raw8228step1 := by
      have heq : raw8228step1 = (fun i j => raw8228step0 (permutation19 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8228step0 permutation19 permutation4
    _ = injectiveMoment H node204 := by rfl

def raw8229 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-3, 2, 2, -1], ![3, 0, -4, 1]]

def raw8229step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-2, 2, 0], ![2, 2, -4], ![0, -1, 1]]

def raw8229step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, -2, 4], ![0, 1, -1]]

def raw8229step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 3, -3], ![2, -2, 0]]

theorem canonical8229 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8229 = injectiveMoment H node147 := by
  calc
    injectiveMoment H raw8229 = injectiveMoment H raw8229step0 := by
      have heq : raw8229step0 = raw8229.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8229).symm
    injectiveMoment H raw8229step0 = injectiveMoment H raw8229step1 := by
      have heq : raw8229step1 = -raw8229step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8229step0).symm
    injectiveMoment H raw8229step1 = injectiveMoment H raw8229step2 := by
      have heq : raw8229step2 = (fun i j => raw8229step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8229step1 permutation25 permutation3
    _ = injectiveMoment H node147 := by rfl

def raw8230 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-3, 3, -1, 1], ![3, -1, -1, -1]]

def raw8230step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-2, 3, -1], ![2, -1, -1], ![0, 1, -1]]

def raw8230step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

theorem canonical8230 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8230 = injectiveMoment H node170 := by
  calc
    injectiveMoment H raw8230 = injectiveMoment H raw8230step0 := by
      have heq : raw8230step0 = raw8230.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8230).symm
    injectiveMoment H raw8230step0 = injectiveMoment H raw8230step1 := by
      have heq : raw8230step1 = (fun i j => raw8230step0 (permutation19 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8230step0 permutation19 permutation4
    _ = injectiveMoment H node170 := by rfl

def raw8231 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-3, 4, 0, -1], ![3, -2, -2, 1]]

def raw8231step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-2, 4, -2], ![2, 0, -2], ![0, -1, 1]]

def raw8231step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 3, -3], ![2, -2, 0]]

theorem canonical8231 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8231 = injectiveMoment H node147 := by
  calc
    injectiveMoment H raw8231 = injectiveMoment H raw8231step0 := by
      have heq : raw8231step0 = raw8231.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8231).symm
    injectiveMoment H raw8231step0 = injectiveMoment H raw8231step1 := by
      have heq : raw8231step1 = (fun i j => raw8231step0 (permutation19 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8231step0 permutation19 permutation4
    _ = injectiveMoment H node147 := by rfl

def raw8232 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-2, 0, 3, -1], ![2, 2, -5, 1]]

def raw8232step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-2, 0, 2], ![2, 3, -5], ![0, -1, 1]]

def raw8232step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-2, -3, 5], ![0, 1, -1]]

def raw8232step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical8232 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8232 = injectiveMoment H node120 := by
  calc
    injectiveMoment H raw8232 = injectiveMoment H raw8232step0 := by
      have heq : raw8232step0 = raw8232.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8232).symm
    injectiveMoment H raw8232step0 = injectiveMoment H raw8232step1 := by
      have heq : raw8232step1 = -raw8232step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8232step0).symm
    injectiveMoment H raw8232step1 = injectiveMoment H raw8232step2 := by
      have heq : raw8232step2 = (fun i j => raw8232step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8232step1 permutation25 permutation3
    _ = injectiveMoment H node120 := by rfl

def raw8233 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-2, 1, -1, 2], ![2, 1, -1, -2]]

def raw8233step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-2, 1, 1], ![2, -1, -1], ![0, 2, -2]]

def raw8233step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

theorem canonical8233 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8233 = injectiveMoment H node224 := by
  calc
    injectiveMoment H raw8233 = injectiveMoment H raw8233step0 := by
      have heq : raw8233step0 = raw8233.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8233).symm
    injectiveMoment H raw8233step0 = injectiveMoment H raw8233step1 := by
      have heq : raw8233step1 = (fun i j => raw8233step0 (permutation16 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8233step0 permutation16 permutation3
    _ = injectiveMoment H node224 := by rfl

def raw8234 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-2, 1, 2, -1], ![2, 1, -4, 1]]

def raw8234step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-2, 1, 1], ![2, 2, -4], ![0, -1, 1]]

def raw8234step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, -2, 4], ![0, 1, -1]]

def raw8234step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical8234 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8234 = injectiveMoment H node146 := by
  calc
    injectiveMoment H raw8234 = injectiveMoment H raw8234step0 := by
      have heq : raw8234step0 = raw8234.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8234).symm
    injectiveMoment H raw8234step0 = injectiveMoment H raw8234step1 := by
      have heq : raw8234step1 = -raw8234step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8234step0).symm
    injectiveMoment H raw8234step1 = injectiveMoment H raw8234step2 := by
      have heq : raw8234step2 = (fun i j => raw8234step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8234step1 permutation25 permutation3
    _ = injectiveMoment H node146 := by rfl

def raw8235 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-2, 2, -1, 1], ![2, 0, -1, -1]]

def raw8235step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-2, 2, 0], ![2, -1, -1], ![0, 1, -1]]

def raw8235step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical8235 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8235 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw8235 = injectiveMoment H raw8235step0 := by
      have heq : raw8235step0 = raw8235.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8235).symm
    injectiveMoment H raw8235step0 = injectiveMoment H raw8235step1 := by
      have heq : raw8235step1 = (fun i j => raw8235step0 (permutation19 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8235step0 permutation19 permutation4
    _ = injectiveMoment H node203 := by rfl

def raw8236 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-2, 2, 1, -1], ![2, 0, -3, 1]]

def raw8236step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-2, 2, 0], ![2, 1, -3], ![0, -1, 1]]

def raw8236step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -2, 0], ![-2, -1, 3], ![0, 1, -1]]

def raw8236step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem canonical8236 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8236 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw8236 = injectiveMoment H raw8236step0 := by
      have heq : raw8236step0 = raw8236.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8236).symm
    injectiveMoment H raw8236step0 = injectiveMoment H raw8236step1 := by
      have heq : raw8236step1 = -raw8236step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8236step0).symm
    injectiveMoment H raw8236step1 = injectiveMoment H raw8236step2 := by
      have heq : raw8236step2 = (fun i j => raw8236step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8236step1 permutation25 permutation3
    _ = injectiveMoment H node177 := by rfl

def raw8237 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-2, 2, 2, -2], ![2, 0, -4, 2]]

def raw8237step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-2, 2, 0], ![2, 2, -4], ![0, -2, 2]]

def raw8237step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -2, 0], ![-2, -2, 4], ![0, 2, -2]]

def raw8237step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]

theorem canonical8237 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8237 = injectiveMoment H node151 := by
  calc
    injectiveMoment H raw8237 = injectiveMoment H raw8237step0 := by
      have heq : raw8237step0 = raw8237.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8237).symm
    injectiveMoment H raw8237step0 = injectiveMoment H raw8237step1 := by
      have heq : raw8237step1 = -raw8237step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8237step0).symm
    injectiveMoment H raw8237step1 = injectiveMoment H raw8237step2 := by
      have heq : raw8237step2 = (fun i j => raw8237step1 (permutation22 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8237step1 permutation22 permutation3
    _ = injectiveMoment H node151 := by rfl

def raw8238 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-2, 4, 0, -2], ![2, -2, -2, 2]]

def raw8238step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-2, 4, -2], ![2, 0, -2], ![0, -2, 2]]

def raw8238step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]

theorem canonical8238 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8238 = injectiveMoment H node151 := by
  calc
    injectiveMoment H raw8238 = injectiveMoment H raw8238step0 := by
      have heq : raw8238step0 = raw8238.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8238).symm
    injectiveMoment H raw8238step0 = injectiveMoment H raw8238step1 := by
      have heq : raw8238step1 = (fun i j => raw8238step0 (permutation16 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8238step0 permutation16 permutation4
    _ = injectiveMoment H node151 := by rfl

def raw8239 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8239step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical8239 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8239 = injectiveMoment H node2718 := by
  calc
    injectiveMoment H raw8239 = injectiveMoment H raw8239step0 := by
      have heq : raw8239step0 = (fun i j => raw8239 (permutation57 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8239 permutation57 permutation9
    _ = injectiveMoment H node2718 := by rfl

def raw8240 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8240step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical8240 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8240 = injectiveMoment H node2583 := by
  calc
    injectiveMoment H raw8240 = injectiveMoment H raw8240step0 := by
      have heq : raw8240step0 = (fun i j => raw8240 (permutation64 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8240 permutation64 permutation11
    _ = injectiveMoment H node2583 := by rfl

def raw8241 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-1, 0, -1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw8241step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0]]

theorem canonical8241 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8241 = injectiveMoment H node2609 := by
  calc
    injectiveMoment H raw8241 = injectiveMoment H raw8241step0 := by
      have heq : raw8241step0 = (fun i j => raw8241 (permutation64 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8241 permutation64 permutation11
    _ = injectiveMoment H node2609 := by rfl

def raw8242 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-1, 0, -1, 2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw8242step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

theorem canonical8242 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8242 = injectiveMoment H node1057 := by
  calc
    injectiveMoment H raw8242 = injectiveMoment H raw8242step0 := by
      have heq : raw8242step0 = (fun i j => raw8242 (permutation17 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8242 permutation17 permutation11
    _ = injectiveMoment H node1057 := by rfl

def raw8243 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-1, 0, 1, 0], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8243step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem canonical8243 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8243 = injectiveMoment H node2740 := by
  calc
    injectiveMoment H raw8243 = injectiveMoment H raw8243step0 := by
      have heq : raw8243step0 = (fun i j => raw8243 (permutation59 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8243 permutation59 permutation10
    _ = injectiveMoment H node2740 := by rfl

def raw8244 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-1, 0, 3, -2], ![1, 2, -5, 2]]

def raw8244step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 0, 2], ![2, 3, -5], ![0, -2, 2]]

def raw8244step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![2, 0, -2], ![-2, -3, 5], ![0, 2, -2]]

def raw8244step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical8244 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8244 = injectiveMoment H node120 := by
  calc
    injectiveMoment H raw8244 = injectiveMoment H raw8244step0 := by
      have heq : raw8244step0 = raw8244.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8244).symm
    injectiveMoment H raw8244step0 = injectiveMoment H raw8244step1 := by
      have heq : raw8244step1 = -raw8244step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8244step0).symm
    injectiveMoment H raw8244step1 = injectiveMoment H raw8244step2 := by
      have heq : raw8244step2 = (fun i j => raw8244step1 (permutation22 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8244step1 permutation22 permutation3
    _ = injectiveMoment H node120 := by rfl

def raw8245 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-1, 1, 2, -2], ![1, 1, -4, 2]]

def raw8245step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![2, 2, -4], ![0, -2, 2]]

def raw8245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![2, -1, -1], ![-2, -2, 4], ![0, 2, -2]]

def raw8245step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical8245 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8245 = injectiveMoment H node146 := by
  calc
    injectiveMoment H raw8245 = injectiveMoment H raw8245step0 := by
      have heq : raw8245step0 = raw8245.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8245).symm
    injectiveMoment H raw8245step0 = injectiveMoment H raw8245step1 := by
      have heq : raw8245step1 = -raw8245step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8245step0).symm
    injectiveMoment H raw8245step1 = injectiveMoment H raw8245step2 := by
      have heq : raw8245step2 = (fun i j => raw8245step1 (permutation22 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8245step1 permutation22 permutation3
    _ = injectiveMoment H node146 := by rfl

def raw8246 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![-1, 2, 1, -2], ![1, 0, -3, 2]]

def raw8246step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 2, 0], ![2, 1, -3], ![0, -2, 2]]

def raw8246step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![2, -2, 0], ![-2, -1, 3], ![0, 2, -2]]

def raw8246step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

theorem canonical8246 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8246 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw8246 = injectiveMoment H raw8246step0 := by
      have heq : raw8246step0 = raw8246.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8246).symm
    injectiveMoment H raw8246step0 = injectiveMoment H raw8246step1 := by
      have heq : raw8246step1 = -raw8246step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8246step0).symm
    injectiveMoment H raw8246step1 = injectiveMoment H raw8246step2 := by
      have heq : raw8246step2 = (fun i j => raw8246step1 (permutation22 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8246step1 permutation22 permutation3
    _ = injectiveMoment H node177 := by rfl

def raw8247 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -2, 2], ![0, 2, 0, -2]]

def raw8247step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![2, 0, -2]]

def raw8247step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]

theorem canonical8247 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8247 = injectiveMoment H node41 := by
  calc
    injectiveMoment H raw8247 = injectiveMoment H raw8247step0 := by
      have hz : ∀ i, raw8247 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8247step0 = (fun i j => raw8247 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8247 permutation9 hz
    injectiveMoment H raw8247step0 = injectiveMoment H raw8247step1 := by
      have heq : raw8247step1 = (fun i j => raw8247step0 (permutation3 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8247step0 permutation3 permutation4
    _ = injectiveMoment H node41 := by rfl

def raw8248 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8248step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical8248 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8248 = injectiveMoment H node2718 := by
  calc
    injectiveMoment H raw8248 = injectiveMoment H raw8248step0 := by
      have heq : raw8248step0 = (fun i j => raw8248 (permutation80 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8248 permutation80 permutation9
    _ = injectiveMoment H node2718 := by rfl

def raw8249 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![-1, 1, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8249step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical8249 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8249 = injectiveMoment H node2629 := by
  calc
    injectiveMoment H raw8249 = injectiveMoment H raw8249step0 := by
      have heq : raw8249step0 = (fun i j => raw8249 (permutation88 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8249 permutation88 permutation11
    _ = injectiveMoment H node2629 := by rfl

def raw8250 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw8250step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

theorem canonical8250 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8250 = injectiveMoment H node2759 := by
  calc
    injectiveMoment H raw8250 = injectiveMoment H raw8250step0 := by
      have heq : raw8250step0 = (fun i j => raw8250 (permutation92 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8250 permutation92 permutation14
    _ = injectiveMoment H node2759 := by rfl

def raw8251 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![-1, 2, 0, -1], ![1, 0, -1, 0]]

def raw8251step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

theorem canonical8251 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8251 = injectiveMoment H node1054 := by
  calc
    injectiveMoment H raw8251 = injectiveMoment H raw8251step0 := by
      have heq : raw8251step0 = (fun i j => raw8251 (permutation21 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8251 permutation21 permutation14
    _ = injectiveMoment H node1054 := by rfl

def raw8252 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 2, 1, -2], ![1, 0, -1, 0]]

def raw8252step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical8252 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8252 = injectiveMoment H node2453 := by
  calc
    injectiveMoment H raw8252 = injectiveMoment H raw8252step0 := by
      have heq : raw8252step0 = (fun i j => raw8252 (permutation104 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8252 permutation104 permutation13
    _ = injectiveMoment H node2453 := by rfl

def raw8253 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![0, 0, -1, 1]]

def raw8253step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, -2, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -2, -1, 3], ![0, 0, 1, -1]]

def raw8253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, 1, -1], ![0, 1, -1], ![-2, -1, 3], ![0, 1, -1]]

def raw8253step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

theorem canonical8253 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8253 = injectiveMoment H node566 := by
  calc
    injectiveMoment H raw8253 = injectiveMoment H raw8253step0 := by
      have heq : raw8253step0 = -raw8253 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8253).symm
    injectiveMoment H raw8253step0 = injectiveMoment H raw8253step1 := by
      have hz : ∀ i, raw8253step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8253step1 = (fun i j => raw8253step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8253step0 permutation9 hz
    injectiveMoment H raw8253step1 = injectiveMoment H raw8253step2 := by
      have heq : raw8253step2 = (fun i j => raw8253step1 (permutation113 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8253step1 permutation113 permutation3
    _ = injectiveMoment H node566 := by rfl

def raw8254 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, 1, 0, 0], ![1, 0, 0, -1]]

def raw8254step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0]]

theorem canonical8254 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8254 = injectiveMoment H node2784 := by
  calc
    injectiveMoment H raw8254 = injectiveMoment H raw8254step0 := by
      have heq : raw8254step0 = (fun i j => raw8254 (permutation116 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8254 permutation116 permutation14
    _ = injectiveMoment H node2784 := by rfl

def raw8255 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![0, 0, 0, 0]]

def raw8255step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1]]

def raw8255step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]

def raw8255step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical8255 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8255 = injectiveMoment H node294 := by
  calc
    injectiveMoment H raw8255 = injectiveMoment H raw8255step0 := by
      have hz : ∀ j, raw8255 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw8255step0 = (fun i j => raw8255 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8255 permutation128 hz
    injectiveMoment H raw8255step0 = injectiveMoment H raw8255step1 := by
      have hz : ∀ i, raw8255step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8255step1 = (fun i j => raw8255step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8255step0 permutation9 hz
    injectiveMoment H raw8255step1 = injectiveMoment H raw8255step2 := by
      have heq : raw8255step2 = (fun i j => raw8255step1 (permutation31 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8255step1 permutation31 permutation8
    _ = injectiveMoment H node294 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

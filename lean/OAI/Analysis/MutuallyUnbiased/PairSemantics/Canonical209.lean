import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6688 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![1, 0, 2, -3]]

def raw6688step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 2, -3]]

def raw6688step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![-1, 3, -2], ![-1, -2, 3]]

def raw6688step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical6688 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6688 = injectiveMoment H node263 := by
  calc
    injectiveMoment H raw6688 = injectiveMoment H raw6688step0 := by
      have heq : raw6688step0 = raw6688.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6688).symm
    injectiveMoment H raw6688step0 = injectiveMoment H raw6688step1 := by
      have heq : raw6688step1 = -raw6688step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6688step0).symm
    injectiveMoment H raw6688step1 = injectiveMoment H raw6688step2 := by
      have heq : raw6688step2 = (fun i j => raw6688step1 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6688step1 permutation32 permutation3
    _ = injectiveMoment H node263 := by rfl

def raw6689 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -2, 1], ![0, 0, 1, -1], ![1, 0, 0, -1]]

def raw6689step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical6689 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6689 = injectiveMoment H node1117 := by
  calc
    injectiveMoment H raw6689 = injectiveMoment H raw6689step0 := by
      have heq : raw6689step0 = (fun i j => raw6689 (permutation12 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6689 permutation12 permutation16
    _ = injectiveMoment H node1117 := by rfl

def raw6690 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def raw6690step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, -1, 2, -1], ![0, -1, 0, 1], ![-1, 1, -1, 1]]

def raw6690step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

theorem canonical6690 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6690 = injectiveMoment H node1119 := by
  calc
    injectiveMoment H raw6690 = injectiveMoment H raw6690step0 := by
      have heq : raw6690step0 = -raw6690 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6690).symm
    injectiveMoment H raw6690step0 = injectiveMoment H raw6690step1 := by
      have heq : raw6690step1 = (fun i j => raw6690step0 (permutation32 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6690step0 permutation32 permutation11
    _ = injectiveMoment H node1119 := by rfl

def raw6691 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem canonical6691 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6691 = injectiveMoment H node1126 := by
  rfl

def raw6692 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw6692step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical6692 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6692 = injectiveMoment H node1123 := by
  calc
    injectiveMoment H raw6692 = injectiveMoment H raw6692step0 := by
      have heq : raw6692step0 = (fun i j => raw6692 (permutation11 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6692 permutation11 permutation10
    _ = injectiveMoment H node1123 := by rfl

def raw6693 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def raw6693step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2]]

def raw6693step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical6693 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6693 = injectiveMoment H node230 := by
  calc
    injectiveMoment H raw6693 = injectiveMoment H raw6693step0 := by
      have heq : raw6693step0 = raw6693.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6693).symm
    injectiveMoment H raw6693step0 = injectiveMoment H raw6693step1 := by
      have heq : raw6693step1 = (fun i j => raw6693step0 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6693step0 permutation21 permutation5
    _ = injectiveMoment H node230 := by rfl

def raw6694 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0]]

def raw6694step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical6694 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6694 = injectiveMoment H node1118 := by
  calc
    injectiveMoment H raw6694 = injectiveMoment H raw6694step0 := by
      have heq : raw6694step0 = (fun i j => raw6694 (permutation11 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6694 permutation11 permutation10
    _ = injectiveMoment H node1118 := by rfl

def raw6695 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def raw6695step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw6695step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, -1, -1]]

theorem canonical6695 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6695 = injectiveMoment H node1114 := by
  calc
    injectiveMoment H raw6695 = injectiveMoment H raw6695step0 := by
      have heq : raw6695step0 = raw6695.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6695).symm
    injectiveMoment H raw6695step0 = injectiveMoment H raw6695step1 := by
      have heq : raw6695step1 = (fun i j => raw6695step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6695step0 permutation22 permutation17
    _ = injectiveMoment H node1114 := by rfl

def raw6696 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw6696step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 1, 0, 0]]

def raw6696step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical6696 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6696 = injectiveMoment H node1118 := by
  calc
    injectiveMoment H raw6696 = injectiveMoment H raw6696step0 := by
      have heq : raw6696step0 = -raw6696 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6696).symm
    injectiveMoment H raw6696step0 = injectiveMoment H raw6696step1 := by
      have heq : raw6696step1 = (fun i j => raw6696step0 (permutation14 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6696step0 permutation14 permutation25
    _ = injectiveMoment H node1118 := by rfl

def raw6697 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def raw6697step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, -1, 1, 0], ![0, -1, -1, 2], ![-1, 1, 1, -1]]

def raw6697step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

theorem canonical6697 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6697 = injectiveMoment H node1119 := by
  calc
    injectiveMoment H raw6697 = injectiveMoment H raw6697step0 := by
      have heq : raw6697step0 = -raw6697 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6697).symm
    injectiveMoment H raw6697step0 = injectiveMoment H raw6697step1 := by
      have heq : raw6697step1 = (fun i j => raw6697step0 (permutation30 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6697step0 permutation30 permutation13
    _ = injectiveMoment H node1119 := by rfl

def raw6698 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -2, 2]]

def raw6698step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -1, 2, -2]]

theorem canonical6698 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6698 = injectiveMoment H node1122 := by
  calc
    injectiveMoment H raw6698 = injectiveMoment H raw6698step0 := by
      have heq : raw6698step0 = (fun i j => raw6698 (permutation11 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6698 permutation11 permutation10
    _ = injectiveMoment H node1122 := by rfl

def raw6699 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw6699step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]

def raw6699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical6699 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6699 = injectiveMoment H node293 := by
  calc
    injectiveMoment H raw6699 = injectiveMoment H raw6699step0 := by
      have heq : raw6699step0 = raw6699.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6699).symm
    injectiveMoment H raw6699step0 = injectiveMoment H raw6699step1 := by
      have heq : raw6699step1 = (fun i j => raw6699step0 (permutation25 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6699step0 permutation25 permutation6
    _ = injectiveMoment H node293 := by rfl

def raw6700 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def raw6700step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![1, 0, 0, -1], ![1, -1, -1, 1]]

def raw6700step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, -1, -1]]

theorem canonical6700 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6700 = injectiveMoment H node1114 := by
  calc
    injectiveMoment H raw6700 = injectiveMoment H raw6700step0 := by
      have heq : raw6700step0 = raw6700.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6700).symm
    injectiveMoment H raw6700step0 = injectiveMoment H raw6700step1 := by
      have heq : raw6700step1 = (fun i j => raw6700step0 (permutation28 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6700step0 permutation28 permutation17
    _ = injectiveMoment H node1114 := by rfl

def raw6701 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def raw6701step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![1, 0, 1, -2], ![1, -1, -2, 2]]

def raw6701step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical6701 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6701 = injectiveMoment H node835 := by
  calc
    injectiveMoment H raw6701 = injectiveMoment H raw6701step0 := by
      have heq : raw6701step0 = raw6701.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6701).symm
    injectiveMoment H raw6701step0 = injectiveMoment H raw6701step1 := by
      have heq : raw6701step1 = (fun i j => raw6701step0 (permutation28 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6701step0 permutation28 permutation17
    _ = injectiveMoment H node835 := by rfl

def raw6702 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw6702step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0]]

def raw6702step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical6702 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6702 = injectiveMoment H node293 := by
  calc
    injectiveMoment H raw6702 = injectiveMoment H raw6702step0 := by
      have heq : raw6702step0 = raw6702.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6702).symm
    injectiveMoment H raw6702step0 = injectiveMoment H raw6702step1 := by
      have heq : raw6702step1 = (fun i j => raw6702step0 (permutation31 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6702step0 permutation31 permutation6
    _ = injectiveMoment H node293 := by rfl

def raw6703 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw6703step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![1, 1, 0, -2], ![1, -2, -1, 2]]

def raw6703step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical6703 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6703 = injectiveMoment H node835 := by
  calc
    injectiveMoment H raw6703 = injectiveMoment H raw6703step0 := by
      have heq : raw6703step0 = raw6703.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6703).symm
    injectiveMoment H raw6703step0 = injectiveMoment H raw6703step1 := by
      have heq : raw6703step1 = (fun i j => raw6703step0 (permutation28 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6703step0 permutation28 permutation23
    _ = injectiveMoment H node835 := by rfl

def raw6704 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, 2, -3], ![1, 0, -3, 2]]

def raw6704step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, 2, -3], ![1, -3, 2]]

def raw6704step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![-1, -2, 3], ![-1, 3, -2]]

def raw6704step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical6704 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6704 = injectiveMoment H node263 := by
  calc
    injectiveMoment H raw6704 = injectiveMoment H raw6704step0 := by
      have heq : raw6704step0 = raw6704.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6704).symm
    injectiveMoment H raw6704step0 = injectiveMoment H raw6704step1 := by
      have heq : raw6704step1 = -raw6704step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6704step0).symm
    injectiveMoment H raw6704step1 = injectiveMoment H raw6704step2 := by
      have heq : raw6704step2 = (fun i j => raw6704step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6704step1 permutation26 permutation3
    _ = injectiveMoment H node263 := by rfl

def raw6705 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 2, -3, 1], ![1, -1, 2, -2]]

def raw6705step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![1, -3, 2], ![1, 1, -2]]

def raw6705step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![-1, 3, -2], ![-1, -1, 2]]

def raw6705step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical6705 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6705 = injectiveMoment H node261 := by
  calc
    injectiveMoment H raw6705 = injectiveMoment H raw6705step0 := by
      have heq : raw6705step0 = raw6705.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6705).symm
    injectiveMoment H raw6705step0 = injectiveMoment H raw6705step1 := by
      have heq : raw6705step1 = -raw6705step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6705step0).symm
    injectiveMoment H raw6705step1 = injectiveMoment H raw6705step2 := by
      have heq : raw6705step2 = (fun i j => raw6705step1 (permutation25 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6705step1 permutation25 permutation4
    _ = injectiveMoment H node261 := by rfl

def raw6706 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 2, -2, 0], ![1, -1, 1, -1]]

def raw6706step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1]]

def raw6706step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical6706 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6706 = injectiveMoment H node227 := by
  calc
    injectiveMoment H raw6706 = injectiveMoment H raw6706step0 := by
      have heq : raw6706step0 = raw6706.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6706).symm
    injectiveMoment H raw6706step0 = injectiveMoment H raw6706step1 := by
      have heq : raw6706step1 = (fun i j => raw6706step0 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6706step0 permutation22 permutation5
    _ = injectiveMoment H node227 := by rfl

def raw6707 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw6707step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]

def raw6707step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical6707 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6707 = injectiveMoment H node287 := by
  calc
    injectiveMoment H raw6707 = injectiveMoment H raw6707step0 := by
      have heq : raw6707step0 = raw6707.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6707).symm
    injectiveMoment H raw6707step0 = injectiveMoment H raw6707step1 := by
      have heq : raw6707step1 = (fun i j => raw6707step0 (permutation18 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6707step0 permutation18 permutation7
    _ = injectiveMoment H node287 := by rfl

def raw6708 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def raw6708step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![1, 1, -2], ![1, -3, 2]]

def raw6708step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![-1, -1, 2], ![-1, 3, -2]]

def raw6708step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical6708 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6708 = injectiveMoment H node261 := by
  calc
    injectiveMoment H raw6708 = injectiveMoment H raw6708step0 := by
      have heq : raw6708step0 = raw6708.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6708).symm
    injectiveMoment H raw6708step0 = injectiveMoment H raw6708step1 := by
      have heq : raw6708step1 = -raw6708step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6708step0).symm
    injectiveMoment H raw6708step1 = injectiveMoment H raw6708step2 := by
      have heq : raw6708step2 = (fun i j => raw6708step1 (permutation31 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6708step1 permutation31 permutation4
    _ = injectiveMoment H node261 := by rfl

def raw6709 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 2, 2, -4], ![1, -1, -3, 3]]

def raw6709step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![1, 2, -3], ![1, -4, 3]]

def raw6709step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -2, 1], ![-1, -2, 3], ![-1, 4, -3]]

def raw6709step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical6709 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6709 = injectiveMoment H node247 := by
  calc
    injectiveMoment H raw6709 = injectiveMoment H raw6709step0 := by
      have heq : raw6709step0 = raw6709.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6709).symm
    injectiveMoment H raw6709step0 = injectiveMoment H raw6709step1 := by
      have heq : raw6709step1 = -raw6709step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6709step0).symm
    injectiveMoment H raw6709step1 = injectiveMoment H raw6709step2 := by
      have heq : raw6709step2 = (fun i j => raw6709step1 (permutation31 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6709step1 permutation31 permutation4
    _ = injectiveMoment H node247 := by rfl

def raw6710 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 3, -3, 0], ![1, -2, 2, -1]]

def raw6710step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 3, -2], ![1, -3, 2], ![1, 0, -1]]

def raw6710step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

theorem canonical6710 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6710 = injectiveMoment H node259 := by
  calc
    injectiveMoment H raw6710 = injectiveMoment H raw6710step0 := by
      have heq : raw6710step0 = raw6710.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6710).symm
    injectiveMoment H raw6710step0 = injectiveMoment H raw6710step1 := by
      have heq : raw6710step1 = (fun i j => raw6710step0 (permutation16 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6710step0 permutation16 permutation4
    _ = injectiveMoment H node259 := by rfl

def raw6711 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 3, -2, -1], ![1, -2, 1, 0]]

def raw6711step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0]]

def raw6711step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical6711 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6711 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw6711 = injectiveMoment H raw6711step0 := by
      have heq : raw6711step0 = raw6711.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6711).symm
    injectiveMoment H raw6711step0 = injectiveMoment H raw6711step1 := by
      have heq : raw6711step1 = (fun i j => raw6711step0 (permutation19 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6711step0 permutation19 permutation7
    _ = injectiveMoment H node181 := by rfl

def raw6712 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 4, -3, -1], ![1, -3, 2, 0]]

def raw6712step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 4, -3], ![1, -3, 2], ![1, -1, 0]]

def raw6712step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3]]

theorem canonical6712 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6712 = injectiveMoment H node243 := by
  calc
    injectiveMoment H raw6712 = injectiveMoment H raw6712step0 := by
      have heq : raw6712step0 = raw6712.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6712).symm
    injectiveMoment H raw6712step0 = injectiveMoment H raw6712step1 := by
      have heq : raw6712step1 = (fun i j => raw6712step0 (permutation16 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6712step0 permutation16 permutation4
    _ = injectiveMoment H node243 := by rfl

def raw6713 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, -2, 2, -1], ![0, 3, -3, 0]]

def raw6713step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![1, 2, -3], ![1, -1, 0]]

def raw6713step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

theorem canonical6713 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6713 = injectiveMoment H node259 := by
  calc
    injectiveMoment H raw6713 = injectiveMoment H raw6713step0 := by
      have heq : raw6713step0 = raw6713.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6713).symm
    injectiveMoment H raw6713step0 = injectiveMoment H raw6713step1 := by
      have heq : raw6713step1 = (fun i j => raw6713step0 (permutation16 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6713step0 permutation16 permutation3
    _ = injectiveMoment H node259 := by rfl

def raw6714 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, -1, -3, 3], ![0, 2, 2, -4]]

def raw6714step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![1, -3, 2], ![1, 3, -4]]

def raw6714step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 1, -2], ![-1, 3, -2], ![-1, -3, 4]]

def raw6714step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical6714 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6714 = injectiveMoment H node247 := by
  calc
    injectiveMoment H raw6714 = injectiveMoment H raw6714step0 := by
      have heq : raw6714step0 = raw6714.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6714).symm
    injectiveMoment H raw6714step0 = injectiveMoment H raw6714step1 := by
      have heq : raw6714step1 = -raw6714step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6714step0).symm
    injectiveMoment H raw6714step1 = injectiveMoment H raw6714step2 := by
      have heq : raw6714step2 = (fun i j => raw6714step1 (permutation31 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6714step1 permutation31 permutation3
    _ = injectiveMoment H node247 := by rfl

def raw6715 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, -1, -2, 2], ![0, 2, 1, -3]]

def raw6715step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 2, -3]]

def raw6715step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, -2, 3]]

def raw6715step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical6715 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6715 = injectiveMoment H node261 := by
  calc
    injectiveMoment H raw6715 = injectiveMoment H raw6715step0 := by
      have heq : raw6715step0 = raw6715.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6715).symm
    injectiveMoment H raw6715step0 = injectiveMoment H raw6715step1 := by
      have heq : raw6715step1 = -raw6715step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6715step0).symm
    injectiveMoment H raw6715step1 = injectiveMoment H raw6715step2 := by
      have heq : raw6715step2 = (fun i j => raw6715step1 (permutation31 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6715step1 permutation31 permutation3
    _ = injectiveMoment H node261 := by rfl

def raw6716 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, -1, 1, -1], ![0, 2, -2, 0]]

def raw6716step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0]]

def raw6716step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical6716 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6716 = injectiveMoment H node227 := by
  calc
    injectiveMoment H raw6716 = injectiveMoment H raw6716step0 := by
      have heq : raw6716step0 = raw6716.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6716).symm
    injectiveMoment H raw6716step0 = injectiveMoment H raw6716step1 := by
      have heq : raw6716step1 = (fun i j => raw6716step0 (permutation22 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6716step0 permutation22 permutation7
    _ = injectiveMoment H node227 := by rfl

def raw6717 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 0, -3, 2], ![0, 1, 2, -3]]

def raw6717step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 2, -3]]

def raw6717step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -1, 0], ![1, 0, -1], ![-1, 3, -2], ![-1, -2, 3]]

def raw6717step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical6717 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6717 = injectiveMoment H node263 := by
  calc
    injectiveMoment H raw6717 = injectiveMoment H raw6717step0 := by
      have heq : raw6717step0 = raw6717.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6717).symm
    injectiveMoment H raw6717step0 = injectiveMoment H raw6717step1 := by
      have heq : raw6717step1 = -raw6717step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6717step0).symm
    injectiveMoment H raw6717step1 = injectiveMoment H raw6717step2 := by
      have heq : raw6717step2 = (fun i j => raw6717step1 (permutation31 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6717step1 permutation31 permutation3
    _ = injectiveMoment H node263 := by rfl

def raw6718 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![1, 0, -2, 1], ![0, 1, 1, -2]]

def raw6718step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2]]

def raw6718step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical6718 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6718 = injectiveMoment H node230 := by
  calc
    injectiveMoment H raw6718 = injectiveMoment H raw6718step0 := by
      have heq : raw6718step0 = raw6718.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6718).symm
    injectiveMoment H raw6718step0 = injectiveMoment H raw6718step1 := by
      have heq : raw6718step1 = (fun i j => raw6718step0 (permutation23 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6718step0 permutation23 permutation5
    _ = injectiveMoment H node230 := by rfl

def raw6719 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def raw6719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical6719 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6719 = injectiveMoment H node858 := by
  calc
    injectiveMoment H raw6719 = injectiveMoment H raw6719step0 := by
      have heq : raw6719step0 = (fun i j => raw6719 (permutation57 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6719 permutation57 permutation3
    _ = injectiveMoment H node858 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

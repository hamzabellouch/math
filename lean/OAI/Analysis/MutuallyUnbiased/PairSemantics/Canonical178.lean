import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5696 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0]]

theorem canonical5696 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5696 = injectiveMoment H node2430 := by
  rfl

def raw5697 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 1, -2, 0]]

theorem canonical5697 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5697 = injectiveMoment H node810 := by
  rfl

def raw5698 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, 0, -1, 0]]

theorem canonical5698 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5698 = injectiveMoment H node811 := by
  rfl

def raw5699 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 3, -3], ![1, 2, -3, 0]]

def raw5699step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 3, -3], ![3, -3, 0]]

def raw5699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]

theorem canonical5699 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5699 = injectiveMoment H node93 := by
  calc
    injectiveMoment H raw5699 = injectiveMoment H raw5699step0 := by
      have heq : raw5699step0 = raw5699.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5699).symm
    injectiveMoment H raw5699step0 = injectiveMoment H raw5699step1 := by
      have heq : raw5699step1 = (fun i j => raw5699step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5699step0 permutation27 permutation6
    _ = injectiveMoment H node93 := by rfl

def raw5700 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def raw5700step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![0, -2, -1, 3], ![3, 1, 0, -4]]

def raw5700step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, 1, -2, 0]]

theorem canonical5700 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5700 = injectiveMoment H node798 := by
  calc
    injectiveMoment H raw5700 = injectiveMoment H raw5700step0 := by
      have heq : raw5700step0 = raw5700.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5700).symm
    injectiveMoment H raw5700step0 = injectiveMoment H raw5700step1 := by
      have heq : raw5700step1 = (fun i j => raw5700step0 (permutation22 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5700step0 permutation22 permutation23
    _ = injectiveMoment H node798 := by rfl

def raw5701 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def raw5701step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 2, 0, -3], ![0, -1, 2, -1], ![0, -1, 0, 1], ![-1, 0, -2, 3]]

def raw5701step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 2, -3]]

theorem canonical5701 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5701 = injectiveMoment H node799 := by
  calc
    injectiveMoment H raw5701 = injectiveMoment H raw5701step0 := by
      have heq : raw5701step0 = -raw5701 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5701).symm
    injectiveMoment H raw5701step0 = injectiveMoment H raw5701step1 := by
      have heq : raw5701step1 = (fun i j => raw5701step0 (permutation32 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5701step0 permutation32 permutation11
    _ = injectiveMoment H node799 := by rfl

def raw5702 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical5702 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5702 = injectiveMoment H node815 := by
  rfl

def raw5703 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

theorem canonical5703 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5703 = injectiveMoment H node816 := by
  rfl

def raw5704 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, 0, -1, 0]]

theorem canonical5704 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5704 = injectiveMoment H node817 := by
  rfl

def raw5705 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![1, 1, 2, -4]]

def raw5705step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2], ![3, 1, -4]]

def raw5705step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

theorem canonical5705 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5705 = injectiveMoment H node206 := by
  calc
    injectiveMoment H raw5705 = injectiveMoment H raw5705step0 := by
      have heq : raw5705step0 = raw5705.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5705).symm
    injectiveMoment H raw5705step0 = injectiveMoment H raw5705step1 := by
      have heq : raw5705step1 = (fun i j => raw5705step0 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5705step0 permutation21 permutation5
    _ = injectiveMoment H node206 := by rfl

def raw5706 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -1, 0], ![0, 1, -2, 1], ![1, 0, 3, -4]]

def raw5706step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![0, -1, -2, 3], ![3, 0, 1, -4]]

def raw5706step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, 1, -2, 0]]

theorem canonical5706 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5706 = injectiveMoment H node798 := by
  calc
    injectiveMoment H raw5706 = injectiveMoment H raw5706step0 := by
      have heq : raw5706step0 = raw5706.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5706).symm
    injectiveMoment H raw5706step0 = injectiveMoment H raw5706step1 := by
      have heq : raw5706step1 = (fun i j => raw5706step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5706step0 permutation22 permutation17
    _ = injectiveMoment H node798 := by rfl

def raw5707 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def raw5707step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![0, -1, -1, 2], ![3, 0, 0, -3]]

def raw5707step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, 1, -2, 0]]

theorem canonical5707 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5707 = injectiveMoment H node1041 := by
  calc
    injectiveMoment H raw5707 = injectiveMoment H raw5707step0 := by
      have heq : raw5707step0 = raw5707.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5707).symm
    injectiveMoment H raw5707step0 = injectiveMoment H raw5707step1 := by
      have heq : raw5707step1 = (fun i j => raw5707step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5707step0 permutation22 permutation17
    _ = injectiveMoment H node1041 := by rfl

def raw5708 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def raw5708step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 2, 0, -3], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 0, -1, 2]]

def raw5708step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem canonical5708 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5708 = injectiveMoment H node1043 := by
  calc
    injectiveMoment H raw5708 = injectiveMoment H raw5708step0 := by
      have heq : raw5708step0 = -raw5708 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5708).symm
    injectiveMoment H raw5708step0 = injectiveMoment H raw5708step1 := by
      have heq : raw5708step1 = (fun i j => raw5708step0 (permutation32 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5708step0 permutation32 permutation11
    _ = injectiveMoment H node1043 := by rfl

def raw5709 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def raw5709step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical5709 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5709 = injectiveMoment H node1203 := by
  calc
    injectiveMoment H raw5709 = injectiveMoment H raw5709step0 := by
      have heq : raw5709step0 = (fun i j => raw5709 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5709 permutation9 permutation11
    _ = injectiveMoment H node1203 := by rfl

def raw5710 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw5710step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![0, -1, 2, -1], ![3, 0, -3, 0]]

def raw5710step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, -1, 0]]

theorem canonical5710 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5710 = injectiveMoment H node1063 := by
  calc
    injectiveMoment H raw5710 = injectiveMoment H raw5710step0 := by
      have heq : raw5710step0 = raw5710.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5710).symm
    injectiveMoment H raw5710step0 = injectiveMoment H raw5710step1 := by
      have heq : raw5710step1 = (fun i j => raw5710step0 (permutation26 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5710step0 permutation26 permutation29
    _ = injectiveMoment H node1063 := by rfl

def raw5711 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -2, 1]]

theorem canonical5711 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5711 = injectiveMoment H node818 := by
  rfl

def raw5712 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -1, 0], ![1, 1, 1, -3]]

def raw5712step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![3, 0, -3]]

def raw5712step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![-3, 0, 3]]

def raw5712step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical5712 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5712 = injectiveMoment H node285 := by
  calc
    injectiveMoment H raw5712 = injectiveMoment H raw5712step0 := by
      have heq : raw5712step0 = raw5712.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5712).symm
    injectiveMoment H raw5712step0 = injectiveMoment H raw5712step1 := by
      have heq : raw5712step1 = -raw5712step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5712step0).symm
    injectiveMoment H raw5712step1 = injectiveMoment H raw5712step2 := by
      have heq : raw5712step2 = (fun i j => raw5712step1 (permutation16 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5712step1 permutation16 permutation6
    _ = injectiveMoment H node285 := by rfl

def raw5713 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def raw5713step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 2, 0, -3], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 0, -1, 2]]

def raw5713step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 2, -3]]

theorem canonical5713 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5713 = injectiveMoment H node1043 := by
  calc
    injectiveMoment H raw5713 = injectiveMoment H raw5713step0 := by
      have heq : raw5713step0 = -raw5713 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5713).symm
    injectiveMoment H raw5713step0 = injectiveMoment H raw5713step1 := by
      have heq : raw5713step1 = (fun i j => raw5713step0 (permutation30 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5713step0 permutation30 permutation11
    _ = injectiveMoment H node1043 := by rfl

def raw5714 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw5714step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![0, 0, 1, -1], ![3, -1, -2, 0]]

def raw5714step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical5714 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5714 = injectiveMoment H node1202 := by
  calc
    injectiveMoment H raw5714 = injectiveMoment H raw5714step0 := by
      have heq : raw5714step0 = raw5714.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5714).symm
    injectiveMoment H raw5714step0 = injectiveMoment H raw5714step1 := by
      have heq : raw5714step1 = (fun i j => raw5714step0 (permutation31 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5714step0 permutation31 permutation20
    _ = injectiveMoment H node1202 := by rfl

def raw5715 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -2, 1]]

theorem canonical5715 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5715 = injectiveMoment H node819 := by
  rfl

def raw5716 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 1, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw5716step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical5716 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5716 = injectiveMoment H node1203 := by
  calc
    injectiveMoment H raw5716 = injectiveMoment H raw5716step0 := by
      have heq : raw5716step0 = (fun i j => raw5716 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5716 permutation11 permutation11
    _ = injectiveMoment H node1203 := by rfl

def raw5717 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw5717step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![0, 1, 0, -1], ![3, -2, -1, 0]]

def raw5717step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical5717 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5717 = injectiveMoment H node1202 := by
  calc
    injectiveMoment H raw5717 = injectiveMoment H raw5717step0 := by
      have heq : raw5717step0 = raw5717.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5717).symm
    injectiveMoment H raw5717step0 = injectiveMoment H raw5717step1 := by
      have heq : raw5717step1 = (fun i j => raw5717step0 (permutation31 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5717step0 permutation31 permutation26
    _ = injectiveMoment H node1202 := by rfl

def raw5718 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw5718step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![3, -2, -1]]

def raw5718step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical5718 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5718 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw5718 = injectiveMoment H raw5718step0 := by
      have heq : raw5718step0 = raw5718.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5718).symm
    injectiveMoment H raw5718step0 = injectiveMoment H raw5718step1 := by
      have heq : raw5718step1 = (fun i j => raw5718step0 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5718step0 permutation28 permutation6
    _ = injectiveMoment H node181 := by rfl

def raw5719 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 2, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw5719step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

theorem canonical5719 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5719 = injectiveMoment H node816 := by
  calc
    injectiveMoment H raw5719 = injectiveMoment H raw5719step0 := by
      have heq : raw5719step0 = (fun i j => raw5719 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5719 permutation11 permutation9
    _ = injectiveMoment H node816 := by rfl

def raw5720 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 2, -3], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw5720step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-2, 1, 1, 0], ![0, 2, -1, -1], ![3, -3, 0, 0]]

def raw5720step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, -1, 0]]

theorem canonical5720 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5720 = injectiveMoment H node1063 := by
  calc
    injectiveMoment H raw5720 = injectiveMoment H raw5720step0 := by
      have heq : raw5720step0 = raw5720.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5720).symm
    injectiveMoment H raw5720step0 = injectiveMoment H raw5720step1 := by
      have heq : raw5720step1 = (fun i j => raw5720step0 (permutation26 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5720step0 permutation26 permutation31
    _ = injectiveMoment H node1063 := by rfl

def raw5721 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 2, -3], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def raw5721step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -2, 1]]

theorem canonical5721 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5721 = injectiveMoment H node819 := by
  calc
    injectiveMoment H raw5721 = injectiveMoment H raw5721step0 := by
      have heq : raw5721step0 = (fun i j => raw5721 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5721 permutation11 permutation9
    _ = injectiveMoment H node819 := by rfl

def raw5722 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 2, -3], ![1, 1, -2, 0]]

def raw5722step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 2, -2], ![3, -3, 0]]

def raw5722step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

theorem canonical5722 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5722 = injectiveMoment H node215 := by
  calc
    injectiveMoment H raw5722 = injectiveMoment H raw5722step0 := by
      have heq : raw5722step0 = raw5722.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5722).symm
    injectiveMoment H raw5722step0 = injectiveMoment H raw5722step1 := by
      have heq : raw5722step1 = (fun i j => raw5722step0 (permutation26 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5722step0 permutation26 permutation7
    _ = injectiveMoment H node215 := by rfl

def raw5723 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 3, -4], ![1, 1, -3, 1]]

def raw5723step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 3, -3], ![3, -4, 1]]

def raw5723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![2, -1, -1], ![0, -3, 3], ![-3, 4, -1]]

def raw5723step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]

theorem canonical5723 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5723 = injectiveMoment H node87 := by
  calc
    injectiveMoment H raw5723 = injectiveMoment H raw5723step0 := by
      have heq : raw5723step0 = raw5723.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5723).symm
    injectiveMoment H raw5723step0 = injectiveMoment H raw5723step1 := by
      have heq : raw5723step1 = -raw5723step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5723step0).symm
    injectiveMoment H raw5723step1 = injectiveMoment H raw5723step2 := by
      have heq : raw5723step2 = (fun i j => raw5723step1 (permutation31 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5723step1 permutation31 permutation4
    _ = injectiveMoment H node87 := by rfl

def raw5724 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 2, -2, 0], ![1, 0, 2, -3]]

def raw5724step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -2, 2], ![3, 0, -3]]

def raw5724step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -2, 0]]

theorem canonical5724 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5724 = injectiveMoment H node204 := by
  calc
    injectiveMoment H raw5724 = injectiveMoment H raw5724step0 := by
      have heq : raw5724step0 = raw5724.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5724).symm
    injectiveMoment H raw5724step0 = injectiveMoment H raw5724step1 := by
      have heq : raw5724step1 = (fun i j => raw5724step0 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5724step0 permutation22 permutation5
    _ = injectiveMoment H node204 := by rfl

def raw5725 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw5725step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![3, -1, -2]]

def raw5725step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical5725 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5725 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw5725 = injectiveMoment H raw5725step0 := by
      have heq : raw5725step0 = raw5725.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5725).symm
    injectiveMoment H raw5725step0 = injectiveMoment H raw5725step1 := by
      have heq : raw5725step1 = (fun i j => raw5725step0 (permutation30 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5725step0 permutation30 permutation8
    _ = injectiveMoment H node185 := by rfl

def raw5726 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw5726step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 1, -1], ![3, -3, 0]]

def raw5726step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0]]

theorem canonical5726 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5726 = injectiveMoment H node292 := by
  calc
    injectiveMoment H raw5726 = injectiveMoment H raw5726step0 := by
      have heq : raw5726step0 = raw5726.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5726).symm
    injectiveMoment H raw5726step0 = injectiveMoment H raw5726step1 := by
      have heq : raw5726step1 = (fun i j => raw5726step0 (permutation24 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5726step0 permutation24 permutation7
    _ = injectiveMoment H node292 := by rfl

def raw5727 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw5727step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 2, -2], ![3, -4, 1]]

def raw5727step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

theorem canonical5727 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5727 = injectiveMoment H node201 := by
  calc
    injectiveMoment H raw5727 = injectiveMoment H raw5727step0 := by
      have heq : raw5727step0 = raw5727.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5727).symm
    injectiveMoment H raw5727step0 = injectiveMoment H raw5727step1 := by
      have heq : raw5727step1 = (fun i j => raw5727step0 (permutation23 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5727step0 permutation23 permutation7
    _ = injectiveMoment H node201 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

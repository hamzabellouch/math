import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw0step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]

def raw0step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

theorem canonical0 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw0 = injectiveMoment H node1379 := by
  calc
    injectiveMoment H raw0 = injectiveMoment H raw0step0 := by
      have heq : raw0step0 = -raw0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw0).symm
    injectiveMoment H raw0step0 = injectiveMoment H raw0step1 := by
      have heq : raw0step1 = (fun i j => raw0step0 (permutation171 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw0step0 permutation171 permutation8
    _ = injectiveMoment H node1379 := by rfl

def raw1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]

def raw1step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]

def raw1step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

theorem canonical1 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1 = injectiveMoment H node297 := by
  calc
    injectiveMoment H raw1 = injectiveMoment H raw1step0 := by
      have heq : raw1step0 = -raw1 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1).symm
    injectiveMoment H raw1step0 = injectiveMoment H raw1step1 := by
      have heq : raw1step1 = (fun i j => raw1step0 (permutation41 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1step0 permutation41 permutation8
    _ = injectiveMoment H node297 := by rfl

def raw2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]

def raw2step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]

def raw2step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

theorem canonical2 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2 = injectiveMoment H node1382 := by
  calc
    injectiveMoment H raw2 = injectiveMoment H raw2step0 := by
      have heq : raw2step0 = -raw2 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2).symm
    injectiveMoment H raw2step0 = injectiveMoment H raw2step1 := by
      have heq : raw2step1 = (fun i j => raw2step0 (permutation175 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2step0 permutation175 permutation8
    _ = injectiveMoment H node1382 := by rfl

def raw3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]

def raw3step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]

def raw3step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

theorem canonical3 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3 = injectiveMoment H node301 := by
  calc
    injectiveMoment H raw3 = injectiveMoment H raw3step0 := by
      have heq : raw3step0 = -raw3 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3).symm
    injectiveMoment H raw3step0 = injectiveMoment H raw3step1 := by
      have heq : raw3step1 = (fun i j => raw3step0 (permutation39 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3step0 permutation39 permutation8
    _ = injectiveMoment H node301 := by rfl

def raw4 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]

def raw4step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]

def raw4step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

theorem canonical4 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4 = injectiveMoment H node299 := by
  calc
    injectiveMoment H raw4 = injectiveMoment H raw4step0 := by
      have heq : raw4step0 = -raw4 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4).symm
    injectiveMoment H raw4step0 = injectiveMoment H raw4step1 := by
      have heq : raw4step1 = (fun i j => raw4step0 (permutation41 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4step0 permutation41 permutation8
    _ = injectiveMoment H node299 := by rfl

def raw5 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]

def raw5step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]

def raw5step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]

theorem canonical5 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5 = injectiveMoment H node71 := by
  calc
    injectiveMoment H raw5 = injectiveMoment H raw5step0 := by
      have heq : raw5step0 = -raw5 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5).symm
    injectiveMoment H raw5step0 = injectiveMoment H raw5step1 := by
      have heq : raw5step1 = (fun i j => raw5step0 (permutation11 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5step0 permutation11 permutation8
    _ = injectiveMoment H node71 := by rfl

def raw6 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]

def raw6step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]

def raw6step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

theorem canonical6 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6 = injectiveMoment H node304 := by
  calc
    injectiveMoment H raw6 = injectiveMoment H raw6step0 := by
      have heq : raw6step0 = -raw6 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6).symm
    injectiveMoment H raw6step0 = injectiveMoment H raw6step1 := by
      have heq : raw6step1 = (fun i j => raw6step0 (permutation51 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6step0 permutation51 permutation8
    _ = injectiveMoment H node304 := by rfl

def raw7 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]

def raw7step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]

def raw7step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

theorem canonical7 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7 = injectiveMoment H node303 := by
  calc
    injectiveMoment H raw7 = injectiveMoment H raw7step0 := by
      have heq : raw7step0 = -raw7 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7).symm
    injectiveMoment H raw7step0 = injectiveMoment H raw7step1 := by
      have heq : raw7step1 = (fun i j => raw7step0 (permutation45 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7step0 permutation45 permutation8
    _ = injectiveMoment H node303 := by rfl

def raw8 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]

def raw8step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 0, 1], ![-4, 3, 1]]

def raw8step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]

theorem canonical8 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8 = injectiveMoment H node77 := by
  calc
    injectiveMoment H raw8 = injectiveMoment H raw8step0 := by
      have heq : raw8step0 = -raw8 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8).symm
    injectiveMoment H raw8step0 = injectiveMoment H raw8step1 := by
      have heq : raw8step1 = (fun i j => raw8step0 (permutation9 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8step0 permutation9 permutation8
    _ = injectiveMoment H node77 := by rfl

def raw9 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]

def raw9step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]

def raw9step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]

theorem canonical9 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9 = injectiveMoment H node73 := by
  calc
    injectiveMoment H raw9 = injectiveMoment H raw9step0 := by
      have heq : raw9step0 = -raw9 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9).symm
    injectiveMoment H raw9step0 = injectiveMoment H raw9step1 := by
      have heq : raw9step1 = (fun i j => raw9step0 (permutation11 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9step0 permutation11 permutation8
    _ = injectiveMoment H node73 := by rfl

def raw10 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]

def raw10step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]

def raw10step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]

theorem canonical10 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw10 = injectiveMoment H node78 := by
  calc
    injectiveMoment H raw10 = injectiveMoment H raw10step0 := by
      have heq : raw10step0 = -raw10 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw10).symm
    injectiveMoment H raw10step0 = injectiveMoment H raw10step1 := by
      have heq : raw10step1 = (fun i j => raw10step0 (permutation9 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10step0 permutation9 permutation8
    _ = injectiveMoment H node78 := by rfl

def raw11 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]

def raw11step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]

def raw11step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]

theorem canonical11 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw11 = injectiveMoment H node75 := by
  calc
    injectiveMoment H raw11 = injectiveMoment H raw11step0 := by
      have heq : raw11step0 = -raw11 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw11).symm
    injectiveMoment H raw11step0 = injectiveMoment H raw11step1 := by
      have heq : raw11step1 = (fun i j => raw11step0 (permutation13 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw11step0 permutation13 permutation8
    _ = injectiveMoment H node75 := by rfl

def raw12 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![5, -3, -2]]

def raw12step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 0, 5], ![2, 1, -3], ![3, -1, -2]]

def raw12step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 5, -5], ![1, -3, 2]]

theorem canonical12 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw12 = injectiveMoment H node60 := by
  calc
    injectiveMoment H raw12 = injectiveMoment H raw12step0 := by
      have heq : raw12step0 = raw12.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw12).symm
    injectiveMoment H raw12step0 = injectiveMoment H raw12step1 := by
      have heq : raw12step1 = (fun i j => raw12step0 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw12step0 permutation7 permutation6
    _ = injectiveMoment H node60 := by rfl

def raw13 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw13step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]

def raw13step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

theorem canonical13 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw13 = injectiveMoment H node1380 := by
  calc
    injectiveMoment H raw13 = injectiveMoment H raw13step0 := by
      have heq : raw13step0 = -raw13 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw13).symm
    injectiveMoment H raw13step0 = injectiveMoment H raw13step1 := by
      have heq : raw13step1 = (fun i j => raw13step0 (permutation151 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw13step0 permutation151 permutation8
    _ = injectiveMoment H node1380 := by rfl

def raw14 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]

def raw14step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]

def raw14step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical14 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw14 = injectiveMoment H node1438 := by
  calc
    injectiveMoment H raw14 = injectiveMoment H raw14step0 := by
      have heq : raw14step0 = -raw14 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw14).symm
    injectiveMoment H raw14step0 = injectiveMoment H raw14step1 := by
      have heq : raw14step1 = (fun i j => raw14step0 (permutation180 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw14step0 permutation180 permutation6
    _ = injectiveMoment H node1438 := by rfl

def raw15 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]

def raw15step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]

def raw15step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical15 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw15 = injectiveMoment H node389 := by
  calc
    injectiveMoment H raw15 = injectiveMoment H raw15step0 := by
      have heq : raw15step0 = -raw15 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw15).symm
    injectiveMoment H raw15step0 = injectiveMoment H raw15step1 := by
      have heq : raw15step1 = (fun i j => raw15step0 (permutation49 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw15step0 permutation49 permutation6
    _ = injectiveMoment H node389 := by rfl

def raw16 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]

def raw16step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]

def raw16step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

theorem canonical16 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw16 = injectiveMoment H node298 := by
  calc
    injectiveMoment H raw16 = injectiveMoment H raw16step0 := by
      have heq : raw16step0 = -raw16 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw16).symm
    injectiveMoment H raw16step0 = injectiveMoment H raw16step1 := by
      have heq : raw16step1 = (fun i j => raw16step0 (permutation34 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw16step0 permutation34 permutation8
    _ = injectiveMoment H node298 := by rfl

def raw17 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]

def raw17step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]

def raw17step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem canonical17 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw17 = injectiveMoment H node129 := by
  calc
    injectiveMoment H raw17 = injectiveMoment H raw17step0 := by
      have heq : raw17step0 = -raw17 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw17).symm
    injectiveMoment H raw17step0 = injectiveMoment H raw17step1 := by
      have heq : raw17step1 = (fun i j => raw17step0 (permutation13 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw17step0 permutation13 permutation6
    _ = injectiveMoment H node129 := by rfl

def raw18 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]

def raw18step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw18step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical18 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw18 = injectiveMoment H node387 := by
  calc
    injectiveMoment H raw18 = injectiveMoment H raw18step0 := by
      have heq : raw18step0 = -raw18 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw18).symm
    injectiveMoment H raw18step0 = injectiveMoment H raw18step1 := by
      have heq : raw18step1 = (fun i j => raw18step0 (permutation41 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw18step0 permutation41 permutation6
    _ = injectiveMoment H node387 := by rfl

def raw19 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]

def raw19step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]

def raw19step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

theorem canonical19 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw19 = injectiveMoment H node300 := by
  calc
    injectiveMoment H raw19 = injectiveMoment H raw19step0 := by
      have heq : raw19step0 = -raw19 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw19).symm
    injectiveMoment H raw19step0 = injectiveMoment H raw19step1 := by
      have heq : raw19step1 = (fun i j => raw19step0 (permutation37 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw19step0 permutation37 permutation8
    _ = injectiveMoment H node300 := by rfl

def raw20 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]

def raw20step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]

def raw20step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical20 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw20 = injectiveMoment H node123 := by
  calc
    injectiveMoment H raw20 = injectiveMoment H raw20step0 := by
      have heq : raw20step0 = -raw20 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw20).symm
    injectiveMoment H raw20step0 = injectiveMoment H raw20step1 := by
      have heq : raw20step1 = (fun i j => raw20step0 (permutation11 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw20step0 permutation11 permutation6
    _ = injectiveMoment H node123 := by rfl

def raw21 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]

def raw21step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-2, 2, 0], ![-2, -1, 3]]

def raw21step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]

theorem canonical21 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw21 = injectiveMoment H node70 := by
  calc
    injectiveMoment H raw21 = injectiveMoment H raw21step0 := by
      have heq : raw21step0 = -raw21 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw21).symm
    injectiveMoment H raw21step0 = injectiveMoment H raw21step1 := by
      have heq : raw21step1 = (fun i j => raw21step0 (permutation9 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw21step0 permutation9 permutation8
    _ = injectiveMoment H node70 := by rfl

def raw22 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]

def raw22step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]

def raw22step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical22 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw22 = injectiveMoment H node127 := by
  calc
    injectiveMoment H raw22 = injectiveMoment H raw22step0 := by
      have heq : raw22step0 = -raw22 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw22).symm
    injectiveMoment H raw22step0 = injectiveMoment H raw22step1 := by
      have heq : raw22step1 = (fun i j => raw22step0 (permutation13 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw22step0 permutation13 permutation6
    _ = injectiveMoment H node127 := by rfl

def raw23 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]

def raw23step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]

def raw23step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

theorem canonical23 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw23 = injectiveMoment H node119 := by
  calc
    injectiveMoment H raw23 = injectiveMoment H raw23step0 := by
      have heq : raw23step0 = -raw23 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw23).symm
    injectiveMoment H raw23step0 = injectiveMoment H raw23step1 := by
      have heq : raw23step1 = (fun i j => raw23step0 (permutation9 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw23step0 permutation9 permutation6
    _ = injectiveMoment H node119 := by rfl

def raw24 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]

def raw24step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]

def raw24step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]

theorem canonical24 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw24 = injectiveMoment H node76 := by
  calc
    injectiveMoment H raw24 = injectiveMoment H raw24step0 := by
      have heq : raw24step0 = -raw24 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw24).symm
    injectiveMoment H raw24step0 = injectiveMoment H raw24step1 := by
      have heq : raw24step1 = (fun i j => raw24step0 (permutation13 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw24step0 permutation13 permutation8
    _ = injectiveMoment H node76 := by rfl

def raw25 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]

def raw25step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]

def raw25step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical25 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw25 = injectiveMoment H node120 := by
  calc
    injectiveMoment H raw25 = injectiveMoment H raw25step0 := by
      have heq : raw25step0 = -raw25 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw25).symm
    injectiveMoment H raw25step0 = injectiveMoment H raw25step1 := by
      have heq : raw25step1 = (fun i j => raw25step0 (permutation10 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw25step0 permutation10 permutation6
    _ = injectiveMoment H node120 := by rfl

def raw26 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]

def raw26step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]

def raw26step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical26 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw26 = injectiveMoment H node124 := by
  calc
    injectiveMoment H raw26 = injectiveMoment H raw26step0 := by
      have heq : raw26step0 = -raw26 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw26).symm
    injectiveMoment H raw26step0 = injectiveMoment H raw26step1 := by
      have heq : raw26step1 = (fun i j => raw26step0 (permutation9 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw26step0 permutation9 permutation6
    _ = injectiveMoment H node124 := by rfl

def raw27 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]

def raw27step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 0, -2], ![3, -1, -2]]

def raw27step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -1, -4], ![-2, 0, 2], ![-3, 1, 2]]

def raw27step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 2, -2], ![1, 2, -3]]

theorem canonical27 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw27 = injectiveMoment H node48 := by
  calc
    injectiveMoment H raw27 = injectiveMoment H raw27step0 := by
      have heq : raw27step0 = raw27.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw27).symm
    injectiveMoment H raw27step0 = injectiveMoment H raw27step1 := by
      have heq : raw27step1 = -raw27step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw27step0).symm
    injectiveMoment H raw27step1 = injectiveMoment H raw27step2 := by
      have heq : raw27step2 = (fun i j => raw27step1 (permutation3 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw27step1 permutation3 permutation6
    _ = injectiveMoment H node48 := by rfl

def raw28 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]

def raw28step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, -1, 2], ![-2, 2, 0], ![-2, 1, 1]]

def raw28step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

theorem canonical28 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw28 = injectiveMoment H node74 := by
  calc
    injectiveMoment H raw28 = injectiveMoment H raw28step0 := by
      have heq : raw28step0 = -raw28 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw28).symm
    injectiveMoment H raw28step0 = injectiveMoment H raw28step1 := by
      have heq : raw28step1 = (fun i j => raw28step0 (permutation12 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw28step0 permutation12 permutation8
    _ = injectiveMoment H node74 := by rfl

def raw29 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![4, -3, -1]]

def raw29step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 1, -3], ![3, -2, -1]]

def raw29step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -3, 2], ![1, 4, -5]]

theorem canonical29 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw29 = injectiveMoment H node39 := by
  calc
    injectiveMoment H raw29 = injectiveMoment H raw29step0 := by
      have heq : raw29step0 = raw29.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw29).symm
    injectiveMoment H raw29step0 = injectiveMoment H raw29step1 := by
      have heq : raw29step1 = (fun i j => raw29step0 (permutation8 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw29step0 permutation8 permutation6
    _ = injectiveMoment H node39 := by rfl

def raw30 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]

def raw30step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-2, 2, 0], ![-3, 0, 3]]

def raw30step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![2, 0, -2]]

theorem canonical30 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw30 = injectiveMoment H node28 := by
  calc
    injectiveMoment H raw30 = injectiveMoment H raw30step0 := by
      have heq : raw30step0 = -raw30 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw30).symm
    injectiveMoment H raw30step0 = injectiveMoment H raw30step1 := by
      have heq : raw30step1 = (fun i j => raw30step0 (permutation4 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw30step0 permutation4 permutation6
    _ = injectiveMoment H node28 := by rfl

def raw31 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]

def raw31step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-2, 1, 1], ![-3, 1, 2]]

def raw31step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![1, 1, -2], ![1, 2, -3]]

theorem canonical31 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw31 = injectiveMoment H node30 := by
  calc
    injectiveMoment H raw31 = injectiveMoment H raw31step0 := by
      have heq : raw31step0 = -raw31 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw31).symm
    injectiveMoment H raw31step0 = injectiveMoment H raw31step1 := by
      have heq : raw31step1 = (fun i j => raw31step0 (permutation3 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw31step0 permutation3 permutation6
    _ = injectiveMoment H node30 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes51

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8800 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-3, 3, -2, 2], ![3, -2, 1, -2]]

def raw8800step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 3, -2], ![1, -2, 1], ![0, 2, -2]]

def raw8800step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 3, -3], ![1, 1, -2]]

theorem canonical8800 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8800 = injectiveMoment H node265 := by
  calc
    injectiveMoment H raw8800 = injectiveMoment H raw8800step0 := by
      have heq : raw8800step0 = raw8800.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8800).symm
    injectiveMoment H raw8800step0 = injectiveMoment H raw8800step1 := by
      have heq : raw8800step1 = (fun i j => raw8800step0 (permutation19 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8800step0 permutation19 permutation4
    _ = injectiveMoment H node265 := by rfl

def raw8801 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-3, 3, 1, -1], ![3, -2, -2, 1]]

def raw8801step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![-1, 3, -2], ![1, 1, -2], ![0, -1, 1]]

def raw8801step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1]]

theorem canonical8801 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8801 = injectiveMoment H node273 := by
  calc
    injectiveMoment H raw8801 = injectiveMoment H raw8801step0 := by
      have heq : raw8801step0 = raw8801.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8801).symm
    injectiveMoment H raw8801step0 = injectiveMoment H raw8801step1 := by
      have heq : raw8801step1 = (fun i j => raw8801step0 (permutation19 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8801step0 permutation19 permutation4
    _ = injectiveMoment H node273 := by rfl

def raw8802 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 1, 2], ![2, 2, -2, -2]]

def raw8802step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, -1, 2], ![1, 1, -2], ![0, 2, -2]]

def raw8802step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

theorem canonical8802 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8802 = injectiveMoment H node279 := by
  calc
    injectiveMoment H raw8802 = injectiveMoment H raw8802step0 := by
      have heq : raw8802step0 = raw8802.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8802).symm
    injectiveMoment H raw8802step0 = injectiveMoment H raw8802step1 := by
      have heq : raw8802step1 = (fun i j => raw8802step0 (permutation16 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8802step0 permutation16 permutation3
    _ = injectiveMoment H node279 := by rfl

def raw8803 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, -1, 2, 1], ![2, 2, -3, -1]]

def raw8803step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, -1, 2], ![1, 2, -3], ![0, 1, -1]]

def raw8803step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-1, -2, 3], ![0, -1, 1]]

def raw8803step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

theorem canonical8803 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8803 = injectiveMoment H node268 := by
  calc
    injectiveMoment H raw8803 = injectiveMoment H raw8803step0 := by
      have heq : raw8803step0 = raw8803.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8803).symm
    injectiveMoment H raw8803step0 = injectiveMoment H raw8803step1 := by
      have heq : raw8803step1 = -raw8803step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8803step0).symm
    injectiveMoment H raw8803step1 = injectiveMoment H raw8803step2 := by
      have heq : raw8803step2 = (fun i j => raw8803step1 (permutation25 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8803step1 permutation25 permutation3
    _ = injectiveMoment H node268 := by rfl

def raw8804 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 2, -2, 2], ![2, -1, 1, -2]]

def raw8804step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 2, -1], ![1, -2, 1], ![0, 2, -2]]

def raw8804step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

theorem canonical8804 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8804 = injectiveMoment H node279 := by
  calc
    injectiveMoment H raw8804 = injectiveMoment H raw8804step0 := by
      have heq : raw8804step0 = raw8804.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8804).symm
    injectiveMoment H raw8804step0 = injectiveMoment H raw8804step1 := by
      have heq : raw8804step1 = (fun i j => raw8804step0 (permutation19 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8804step0 permutation19 permutation4
    _ = injectiveMoment H node279 := by rfl

def raw8805 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 2, 1, -1], ![2, -1, -2, 1]]

def raw8805step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 2, -1], ![1, 1, -2], ![0, -1, 1]]

def raw8805step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

theorem canonical8805 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8805 = injectiveMoment H node288 := by
  calc
    injectiveMoment H raw8805 = injectiveMoment H raw8805step0 := by
      have heq : raw8805step0 = raw8805.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8805).symm
    injectiveMoment H raw8805step0 = injectiveMoment H raw8805step1 := by
      have heq : raw8805step1 = (fun i j => raw8805step0 (permutation19 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8805step0 permutation19 permutation4
    _ = injectiveMoment H node288 := by rfl

def raw8806 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 3, -2, 1], ![2, -2, 1, -1]]

def raw8806step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 3, -2], ![1, -2, 1], ![0, 1, -1]]

def raw8806step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

theorem canonical8806 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8806 = injectiveMoment H node268 := by
  calc
    injectiveMoment H raw8806 = injectiveMoment H raw8806step0 := by
      have heq : raw8806step0 = raw8806.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8806).symm
    injectiveMoment H raw8806step0 = injectiveMoment H raw8806step1 := by
      have heq : raw8806step1 = (fun i j => raw8806step0 (permutation19 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8806step0 permutation19 permutation4
    _ = injectiveMoment H node268 := by rfl

def raw8807 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 3, 1, -2], ![2, -2, -2, 2]]

def raw8807step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 3, -2], ![1, 1, -2], ![0, -2, 2]]

def raw8807step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1]]

theorem canonical8807 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8807 = injectiveMoment H node274 := by
  calc
    injectiveMoment H raw8807 = injectiveMoment H raw8807step0 := by
      have heq : raw8807step0 = raw8807.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8807).symm
    injectiveMoment H raw8807step0 = injectiveMoment H raw8807step1 := by
      have heq : raw8807step1 = (fun i j => raw8807step0 (permutation16 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8807step0 permutation16 permutation4
    _ = injectiveMoment H node274 := by rfl

def raw8808 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -2, 2, 1], ![1, 3, -3, -1]]

def raw8808step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -2, 3], ![1, 2, -3], ![0, 1, -1]]

def raw8808step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3]]

theorem canonical8808 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8808 = injectiveMoment H node267 := by
  calc
    injectiveMoment H raw8808 = injectiveMoment H raw8808step0 := by
      have heq : raw8808step0 = raw8808.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8808).symm
    injectiveMoment H raw8808step0 = injectiveMoment H raw8808step1 := by
      have heq : raw8808step1 = (fun i j => raw8808step0 (permutation16 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8808step0 permutation16 permutation3
    _ = injectiveMoment H node267 := by rfl

def raw8809 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 1, 1], ![1, 2, -2, -1]]

def raw8809step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![1, 1, -2], ![0, 1, -1]]

def raw8809step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical8809 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8809 = injectiveMoment H node283 := by
  calc
    injectiveMoment H raw8809 = injectiveMoment H raw8809step0 := by
      have heq : raw8809step0 = raw8809.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8809).symm
    injectiveMoment H raw8809step0 = injectiveMoment H raw8809step1 := by
      have heq : raw8809step1 = (fun i j => raw8809step0 (permutation16 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8809step0 permutation16 permutation3
    _ = injectiveMoment H node283 := by rfl

def raw8810 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, -1, 3, -1], ![1, 2, -4, 1]]

def raw8810step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, -1, 2], ![1, 3, -4], ![0, -1, 1]]

def raw8810step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, 1, -2], ![-1, -3, 4], ![0, 1, -1]]

def raw8810step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical8810 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8810 = injectiveMoment H node253 := by
  calc
    injectiveMoment H raw8810 = injectiveMoment H raw8810step0 := by
      have heq : raw8810step0 = raw8810.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8810).symm
    injectiveMoment H raw8810step0 = injectiveMoment H raw8810step1 := by
      have heq : raw8810step1 = -raw8810step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8810step0).symm
    injectiveMoment H raw8810step1 = injectiveMoment H raw8810step2 := by
      have heq : raw8810step2 = (fun i j => raw8810step1 (permutation22 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8810step1 permutation22 permutation3
    _ = injectiveMoment H node253 := by rfl

def raw8811 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, -1, 2], ![0, 2, 2, -4], ![1, -1, -2, 2]]

def raw8811step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 2, 2, -4], ![1, -1, -2, 2]]

theorem canonical8811 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8811 = injectiveMoment H node1243 := by
  calc
    injectiveMoment H raw8811 = injectiveMoment H raw8811step0 := by
      have heq : raw8811step0 = (fun i j => raw8811 (permutation15 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8811 permutation15 permutation9
    _ = injectiveMoment H node1243 := by rfl

def raw8812 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def raw8812step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -1, 0], ![1, 0, -1, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 2, -2]]

def raw8812step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical8812 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8812 = injectiveMoment H node2448 := by
  calc
    injectiveMoment H raw8812 = injectiveMoment H raw8812step0 := by
      have heq : raw8812step0 = -raw8812 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8812).symm
    injectiveMoment H raw8812step0 = injectiveMoment H raw8812step1 := by
      have heq : raw8812step1 = (fun i j => raw8812step0 (permutation131 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8812step0 permutation131 permutation13
    _ = injectiveMoment H node2448 := by rfl

def raw8813 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, 1, 0], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def raw8813step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![1, 1, 0, -2], ![0, 0, -2, 2]]

def raw8813step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, -2, 1], ![-1, -1, 0, 2], ![0, 0, 2, -2]]

def raw8813step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem canonical8813 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8813 = injectiveMoment H node1053 := by
  calc
    injectiveMoment H raw8813 = injectiveMoment H raw8813step0 := by
      have heq : raw8813step0 = raw8813.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8813).symm
    injectiveMoment H raw8813step0 = injectiveMoment H raw8813step1 := by
      have heq : raw8813step1 = -raw8813step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8813step0).symm
    injectiveMoment H raw8813step1 = injectiveMoment H raw8813step2 := by
      have heq : raw8813step2 = (fun i j => raw8813step1 (permutation26 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8813step1 permutation26 permutation15
    _ = injectiveMoment H node1053 := by rfl

def raw8814 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, 1, 0], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def raw8814step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![1, 1, 1, -3], ![0, 0, -3, 3]]

def raw8814step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, -2, 1], ![-1, -1, -1, 3], ![0, 0, 3, -3]]

def raw8814step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem canonical8814 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8814 = injectiveMoment H node977 := by
  calc
    injectiveMoment H raw8814 = injectiveMoment H raw8814step0 := by
      have heq : raw8814step0 = raw8814.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8814).symm
    injectiveMoment H raw8814step0 = injectiveMoment H raw8814step1 := by
      have heq : raw8814step1 = -raw8814step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8814step0).symm
    injectiveMoment H raw8814step1 = injectiveMoment H raw8814step2 := by
      have heq : raw8814step2 = (fun i j => raw8814step1 (permutation26 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8814step1 permutation26 permutation15
    _ = injectiveMoment H node977 := by rfl

def raw8815 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def raw8815step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 0, 2, -1], ![1, 2, 0, -3], ![0, -1, -2, 3]]

def raw8815step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, 0, -2, 1], ![-1, -2, 0, 3], ![0, 1, 2, -3]]

def raw8815step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -2, 1]]

theorem canonical8815 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8815 = injectiveMoment H node819 := by
  calc
    injectiveMoment H raw8815 = injectiveMoment H raw8815step0 := by
      have heq : raw8815step0 = raw8815.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8815).symm
    injectiveMoment H raw8815step0 = injectiveMoment H raw8815step1 := by
      have heq : raw8815step1 = -raw8815step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8815step0).symm
    injectiveMoment H raw8815step1 = injectiveMoment H raw8815step2 := by
      have heq : raw8815step2 = (fun i j => raw8815step1 (permutation22 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8815step1 permutation22 permutation9
    _ = injectiveMoment H node819 := by rfl

def raw8816 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 1, -3, 3], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw8816step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![1, -3, 1, 1], ![0, 3, -2, -1]]

def raw8816step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![1, -1, -1, 1], ![-1, 3, -1, -1], ![0, -3, 2, 1]]

def raw8816step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, 1, -1, -1]]

theorem canonical8816 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8816 = injectiveMoment H node933 := by
  calc
    injectiveMoment H raw8816 = injectiveMoment H raw8816step0 := by
      have heq : raw8816step0 = raw8816.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8816).symm
    injectiveMoment H raw8816step0 = injectiveMoment H raw8816step1 := by
      have heq : raw8816step1 = -raw8816step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8816step0).symm
    injectiveMoment H raw8816step1 = injectiveMoment H raw8816step2 := by
      have heq : raw8816step2 = (fun i j => raw8816step1 (permutation22 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8816step1 permutation22 permutation14
    _ = injectiveMoment H node933 := by rfl

def raw8817 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 1, -3, 3], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw8817step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![1, -3, 2, 0], ![0, 3, -3, 0]]

def raw8817step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical8817 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8817 = injectiveMoment H node1103 := by
  calc
    injectiveMoment H raw8817 = injectiveMoment H raw8817step0 := by
      have heq : raw8817step0 = raw8817.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8817).symm
    injectiveMoment H raw8817step0 = injectiveMoment H raw8817step1 := by
      have heq : raw8817step1 = (fun i j => raw8817step0 (permutation19 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8817step0 permutation19 permutation14
    _ = injectiveMoment H node1103 := by rfl

def raw8818 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 1, -2, 2], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def raw8818step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![1, -2, 2, -1], ![0, 2, -3, 1]]

def raw8818step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -1, 2, -2]]

theorem canonical8818 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8818 = injectiveMoment H node1122 := by
  calc
    injectiveMoment H raw8818 = injectiveMoment H raw8818step0 := by
      have heq : raw8818step0 = raw8818.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8818).symm
    injectiveMoment H raw8818step0 = injectiveMoment H raw8818step1 := by
      have heq : raw8818step1 = (fun i j => raw8818step0 (permutation19 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8818step0 permutation19 permutation14
    _ = injectiveMoment H node1122 := by rfl

def raw8819 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 1, 0, 0], ![1, 0, -1, 0]]

def raw8819step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![1, 0, -1]]

def raw8819step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical8819 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8819 = injectiveMoment H node64 := by
  calc
    injectiveMoment H raw8819 = injectiveMoment H raw8819step0 := by
      have hz : ∀ i, raw8819 i (permutation27 0) = 0 := by decide +kernel
      have heq : raw8819step0 = (fun i j => raw8819 i (permutation27 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8819 permutation27 hz
    injectiveMoment H raw8819step0 = injectiveMoment H raw8819step1 := by
      have heq : raw8819step1 = (fun i j => raw8819step0 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8819step0 permutation5 permutation4
    _ = injectiveMoment H node64 := by rfl

def raw8820 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 2, -2, 1], ![1, -1, 1, -1]]

def raw8820step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 2, -1], ![1, -2, 1], ![0, 1, -1]]

def raw8820step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical8820 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8820 = injectiveMoment H node283 := by
  calc
    injectiveMoment H raw8820 = injectiveMoment H raw8820step0 := by
      have heq : raw8820step0 = raw8820.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8820).symm
    injectiveMoment H raw8820step0 = injectiveMoment H raw8820step1 := by
      have heq : raw8820step1 = (fun i j => raw8820step0 (permutation19 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8820step0 permutation19 permutation4
    _ = injectiveMoment H node283 := by rfl

def raw8821 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-1, 2, 1, -2], ![1, -1, -2, 2]]

def raw8821step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![0, -2, 2]]

def raw8821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

theorem canonical8821 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8821 = injectiveMoment H node288 := by
  calc
    injectiveMoment H raw8821 = injectiveMoment H raw8821step0 := by
      have heq : raw8821step0 = raw8821.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8821).symm
    injectiveMoment H raw8821step0 = injectiveMoment H raw8821step1 := by
      have heq : raw8821step1 = (fun i j => raw8821step0 (permutation16 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8821step0 permutation16 permutation4
    _ = injectiveMoment H node288 := by rfl

def raw8822 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, -2, 3], ![0, 2, 1, -3]]

def raw8822step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![-1, -1, 2], ![1, -2, 1], ![0, 3, -3]]

def raw8822step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![1, -2, 1], ![0, 3, -3]]

def raw8822step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

theorem canonical8822 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8822 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw8822 = injectiveMoment H raw8822step0 := by
      have heq : raw8822step0 = raw8822.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8822).symm
    injectiveMoment H raw8822step0 = injectiveMoment H raw8822step1 := by
      have hz : ∀ j, raw8822step0 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8822step1 = (fun i j => raw8822step0 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8822step0 permutation9 hz
    injectiveMoment H raw8822step1 = injectiveMoment H raw8822step2 := by
      have heq : raw8822step2 = (fun i j => raw8822step1 (permutation4 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8822step1 permutation4 permutation3
    _ = injectiveMoment H node63 := by rfl

def raw8823 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-2, 2, 0, 0], ![2, 0, 2, -4]]

def raw8823step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 1, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, 0, 0], ![-2, 0, -2, 4]]

def raw8823step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 0, 0]]

theorem canonical8823 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8823 = injectiveMoment H node3119 := by
  calc
    injectiveMoment H raw8823 = injectiveMoment H raw8823step0 := by
      have heq : raw8823step0 = -raw8823 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8823).symm
    injectiveMoment H raw8823step0 = injectiveMoment H raw8823step1 := by
      have heq : raw8823step1 = (fun i j => raw8823step0 (permutation363 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8823step0 permutation363 permutation9
    _ = injectiveMoment H node3119 := by rfl

def raw8824 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, 1, 1, -4]]

def raw8824step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 1, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![2, 0, -1, -1], ![-2, -1, -1, 4]]

def raw8824step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

theorem canonical8824 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8824 = injectiveMoment H node2909 := by
  calc
    injectiveMoment H raw8824 = injectiveMoment H raw8824step0 := by
      have heq : raw8824step0 = -raw8824 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8824).symm
    injectiveMoment H raw8824step0 = injectiveMoment H raw8824step1 := by
      have heq : raw8824step1 = (fun i j => raw8824step0 (permutation383 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8824step0 permutation383 permutation9
    _ = injectiveMoment H node2909 := by rfl

def raw8825 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 1, 0, 1], ![2, 0, 2, -4]]

def raw8825step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 1, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![2, -1, 0, -1], ![-2, 0, -2, 4]]

def raw8825step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, 0, -1]]

theorem canonical8825 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8825 = injectiveMoment H node3110 := by
  calc
    injectiveMoment H raw8825 = injectiveMoment H raw8825step0 := by
      have heq : raw8825step0 = -raw8825 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8825).symm
    injectiveMoment H raw8825step0 = injectiveMoment H raw8825step1 := by
      have heq : raw8825step1 = (fun i j => raw8825step0 (permutation383 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8825step0 permutation383 permutation9
    _ = injectiveMoment H node3110 := by rfl

def raw8826 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 2, 1, -4]]

def raw8826step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 1, -2], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![2, 0, -1, -1], ![-1, -2, -1, 4]]

def raw8826step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem canonical8826 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8826 = injectiveMoment H node2917 := by
  calc
    injectiveMoment H raw8826 = injectiveMoment H raw8826step0 := by
      have heq : raw8826step0 = -raw8826 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8826).symm
    injectiveMoment H raw8826step0 = injectiveMoment H raw8826step1 := by
      have heq : raw8826step1 = (fun i j => raw8826step0 (permutation387 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8826step0 permutation387 permutation15
    _ = injectiveMoment H node2917 := by rfl

def raw8827 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, 1, 2, -4]]

def raw8827step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

theorem canonical8827 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8827 = injectiveMoment H node3271 := by
  calc
    injectiveMoment H raw8827 = injectiveMoment H raw8827step0 := by
      have heq : raw8827step0 = (fun i j => raw8827 (permutation277 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8827 permutation277 permutation9
    _ = injectiveMoment H node3271 := by rfl

def raw8828 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, 0, 2], ![2, 0, 2, -4]]

def raw8828step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 1, -2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![2, 0, 0, -2], ![-2, 0, -2, 4]]

def raw8828step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

theorem canonical8828 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8828 = injectiveMoment H node3104 := by
  calc
    injectiveMoment H raw8828 = injectiveMoment H raw8828step0 := by
      have heq : raw8828step0 = -raw8828 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8828).symm
    injectiveMoment H raw8828step0 = injectiveMoment H raw8828step1 := by
      have heq : raw8828step1 = (fun i j => raw8828step0 (permutation363 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8828step0 permutation363 permutation9
    _ = injectiveMoment H node3104 := by rfl

def raw8829 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, 1, 2, -4]]

def raw8829step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

theorem canonical8829 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8829 = injectiveMoment H node3158 := by
  calc
    injectiveMoment H raw8829 = injectiveMoment H raw8829step0 := by
      have heq : raw8829step0 = (fun i j => raw8829 (permutation277 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8829 permutation277 permutation9
    _ = injectiveMoment H node3158 := by rfl

def raw8830 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 2, 2, -4]]

def raw8830step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 1, -2], ![-1, 0, 1, 0], ![-1, 0, 1, 0], ![2, 0, 0, -2], ![0, -2, -2, 4]]

def raw8830step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem canonical8830 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8830 = injectiveMoment H node3108 := by
  calc
    injectiveMoment H raw8830 = injectiveMoment H raw8830step0 := by
      have heq : raw8830step0 = -raw8830 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8830).symm
    injectiveMoment H raw8830step0 = injectiveMoment H raw8830step1 := by
      have heq : raw8830step1 = (fun i j => raw8830step0 (permutation366 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8830step0 permutation366 permutation15
    _ = injectiveMoment H node3108 := by rfl

def raw8831 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, 0, -1, 1], ![-1, 2, 2, -3], ![1, -1, -2, 2]]

def raw8831step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![1, -1, 2, -2], ![0, 1, -3, 2]]

def raw8831step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 0, -2, 1], ![-1, 1, -2, 2], ![0, -1, 3, -2]]

def raw8831step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

theorem canonical8831 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8831 = injectiveMoment H node1216 := by
  calc
    injectiveMoment H raw8831 = injectiveMoment H raw8831step0 := by
      have heq : raw8831step0 = raw8831.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8831).symm
    injectiveMoment H raw8831step0 = injectiveMoment H raw8831step1 := by
      have heq : raw8831step1 = -raw8831step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8831step0).symm
    injectiveMoment H raw8831step1 = injectiveMoment H raw8831step2 := by
      have heq : raw8831step2 = (fun i j => raw8831step1 (permutation27 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8831step1 permutation27 permutation16
    _ = injectiveMoment H node1216 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

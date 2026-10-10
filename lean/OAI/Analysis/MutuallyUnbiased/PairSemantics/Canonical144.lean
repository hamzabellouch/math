import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes31

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4608 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -2, 2, -1], ![1, 0, 1, -2]]

theorem canonical4608 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4608 = injectiveMoment H node684 := by
  rfl

def raw4609 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw4609step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, -2, 3, 0], ![2, 1, -2, -1]]

def raw4609step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 2, 0], ![1, 2, -3, 0], ![-2, -1, 2, 1]]

def raw4609step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, -1, -2, 2]]

theorem canonical4609 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4609 = injectiveMoment H node1310 := by
  calc
    injectiveMoment H raw4609 = injectiveMoment H raw4609step0 := by
      have heq : raw4609step0 = raw4609.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4609).symm
    injectiveMoment H raw4609step0 = injectiveMoment H raw4609step1 := by
      have heq : raw4609step1 = -raw4609step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4609step0).symm
    injectiveMoment H raw4609step1 = injectiveMoment H raw4609step2 := by
      have heq : raw4609step2 = (fun i j => raw4609step1 (permutation9 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4609step1 permutation9 permutation29
    _ = injectiveMoment H node1310 := by rfl

def raw4610 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw4610step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-1, -2, 0, 3], ![2, 1, 0, -3]]

def raw4610step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![1, 2, 0, -3], ![-2, -1, 0, 3]]

def raw4610step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, -1, -1, 1]]

theorem canonical4610 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4610 = injectiveMoment H node1308 := by
  calc
    injectiveMoment H raw4610 = injectiveMoment H raw4610step0 := by
      have heq : raw4610step0 = raw4610.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4610).symm
    injectiveMoment H raw4610step0 = injectiveMoment H raw4610step1 := by
      have heq : raw4610step1 = -raw4610step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4610step0).symm
    injectiveMoment H raw4610step1 = injectiveMoment H raw4610step2 := by
      have heq : raw4610step2 = (fun i j => raw4610step1 (permutation14 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4610step1 permutation14 permutation23
    _ = injectiveMoment H node1308 := by rfl

def raw4611 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem canonical4611 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4611 = injectiveMoment H node685 := by
  rfl

def raw4612 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -1, 2, -2], ![1, -1, 1, -1]]

def raw4612step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem canonical4612 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4612 = injectiveMoment H node685 := by
  calc
    injectiveMoment H raw4612 = injectiveMoment H raw4612step0 := by
      have heq : raw4612step0 = (fun i j => raw4612 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4612 permutation10 permutation9
    _ = injectiveMoment H node685 := by rfl

def raw4613 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -1, 0], ![1, -2, -1, 2], ![1, 0, 3, -4]]

def raw4613step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, -1, -1, 3], ![2, 0, 2, -4]]

def raw4613step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 1, -2, 0]]

theorem canonical4613 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4613 = injectiveMoment H node927 := by
  calc
    injectiveMoment H raw4613 = injectiveMoment H raw4613step0 := by
      have heq : raw4613step0 = raw4613.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4613).symm
    injectiveMoment H raw4613step0 = injectiveMoment H raw4613step1 := by
      have heq : raw4613step1 = (fun i j => raw4613step0 (permutation22 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4613step0 permutation22 permutation15
    _ = injectiveMoment H node927 := by rfl

def raw4614 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 2, -3]]

def raw4614step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, -1, 0, 2], ![2, 0, 1, -3]]

def raw4614step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem canonical4614 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4614 = injectiveMoment H node1277 := by
  calc
    injectiveMoment H raw4614 = injectiveMoment H raw4614step0 := by
      have heq : raw4614step0 = raw4614.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4614).symm
    injectiveMoment H raw4614step0 = injectiveMoment H raw4614step1 := by
      have heq : raw4614step1 = (fun i j => raw4614step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4614step0 permutation22 permutation17
    _ = injectiveMoment H node1277 := by rfl

def raw4615 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 1, -2]]

def raw4615step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, -1, 1, 1], ![2, 0, 0, -2]]

def raw4615step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 2, 0], ![1, 1, -1, -1], ![-2, 0, 0, 2]]

def raw4615step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

theorem canonical4615 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4615 = injectiveMoment H node1309 := by
  calc
    injectiveMoment H raw4615 = injectiveMoment H raw4615step0 := by
      have heq : raw4615step0 = raw4615.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4615).symm
    injectiveMoment H raw4615step0 = injectiveMoment H raw4615step1 := by
      have heq : raw4615step1 = -raw4615step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4615step0).symm
    injectiveMoment H raw4615step1 = injectiveMoment H raw4615step2 := by
      have heq : raw4615step2 = (fun i j => raw4615step1 (permutation16 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4615step1 permutation16 permutation20
    _ = injectiveMoment H node1309 := by rfl

def raw4616 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw4616step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, -1, 2, 0], ![2, 0, -1, -1]]

def raw4616step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem canonical4616 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4616 = injectiveMoment H node1244 := by
  calc
    injectiveMoment H raw4616 = injectiveMoment H raw4616step0 := by
      have heq : raw4616step0 = raw4616.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4616).symm
    injectiveMoment H raw4616step0 = injectiveMoment H raw4616step1 := by
      have heq : raw4616step1 = (fun i j => raw4616step0 (permutation25 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4616step0 permutation25 permutation19
    _ = injectiveMoment H node1244 := by rfl

def raw4617 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def raw4617step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-1, -1, -1, 3], ![2, 0, 1, -3]]

def raw4617step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 1, -1]]

theorem canonical4617 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4617 = injectiveMoment H node984 := by
  calc
    injectiveMoment H raw4617 = injectiveMoment H raw4617step0 := by
      have heq : raw4617step0 = raw4617.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4617).symm
    injectiveMoment H raw4617step0 = injectiveMoment H raw4617step1 := by
      have heq : raw4617step1 = (fun i j => raw4617step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4617step0 permutation22 permutation17
    _ = injectiveMoment H node984 := by rfl

def raw4618 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw4618step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-1, -1, 0, 2], ![2, 0, 0, -2]]

def raw4618step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 1, -1]]

theorem canonical4618 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4618 = injectiveMoment H node1263 := by
  calc
    injectiveMoment H raw4618 = injectiveMoment H raw4618step0 := by
      have heq : raw4618step0 = raw4618.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4618).symm
    injectiveMoment H raw4618step0 = injectiveMoment H raw4618step1 := by
      have heq : raw4618step1 = (fun i j => raw4618step0 (permutation25 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4618step0 permutation25 permutation17
    _ = injectiveMoment H node1263 := by rfl

def raw4619 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw4619step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-1, -1, 1, 1], ![2, 0, -1, -1]]

def raw4619step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

theorem canonical4619 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4619 = injectiveMoment H node1360 := by
  calc
    injectiveMoment H raw4619 = injectiveMoment H raw4619step0 := by
      have heq : raw4619step0 = raw4619.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4619).symm
    injectiveMoment H raw4619step0 = injectiveMoment H raw4619step1 := by
      have heq : raw4619step1 = (fun i j => raw4619step0 (permutation25 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4619step0 permutation25 permutation18
    _ = injectiveMoment H node1360 := by rfl

def raw4620 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw4620step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, 0, 2, -1], ![2, -1, -1, 0]]

def raw4620step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -2, 1]]

theorem canonical4620 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4620 = injectiveMoment H node1247 := by
  calc
    injectiveMoment H raw4620 = injectiveMoment H raw4620step0 := by
      have heq : raw4620step0 = raw4620.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4620).symm
    injectiveMoment H raw4620step0 = injectiveMoment H raw4620step1 := by
      have heq : raw4620step1 = (fun i j => raw4620step0 (permutation31 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4620step0 permutation31 permutation20
    _ = injectiveMoment H node1247 := by rfl

def raw4621 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -2, 1]]

def raw4621step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, 0, 3, -2], ![2, -1, -2, 1]]

def raw4621step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 2, 0], ![1, 0, -3, 2], ![-2, 1, 2, -1]]

def raw4621step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

theorem canonical4621 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4621 = injectiveMoment H node1248 := by
  calc
    injectiveMoment H raw4621 = injectiveMoment H raw4621step0 := by
      have heq : raw4621step0 = raw4621.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4621).symm
    injectiveMoment H raw4621step0 = injectiveMoment H raw4621step1 := by
      have heq : raw4621step1 = -raw4621step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4621step0).symm
    injectiveMoment H raw4621step1 = injectiveMoment H raw4621step2 := by
      have heq : raw4621step2 = (fun i j => raw4621step1 (permutation15 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4621step1 permutation15 permutation19
    _ = injectiveMoment H node1248 := by rfl

def raw4622 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw4622step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, 1, 1, -1], ![2, -2, 0, 0]]

def raw4622step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 2, 0], ![1, -1, -1, 1], ![-2, 2, 0, 0]]

def raw4622step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem canonical4622 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4622 = injectiveMoment H node1058 := by
  calc
    injectiveMoment H raw4622 = injectiveMoment H raw4622step0 := by
      have heq : raw4622step0 = raw4622.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4622).symm
    injectiveMoment H raw4622step0 = injectiveMoment H raw4622step1 := by
      have heq : raw4622step1 = -raw4622step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4622step0).symm
    injectiveMoment H raw4622step1 = injectiveMoment H raw4622step2 := by
      have heq : raw4622step2 = (fun i j => raw4622step1 (permutation13 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4622step1 permutation13 permutation32
    _ = injectiveMoment H node1058 := by rfl

def raw4623 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -2, 1]]

theorem canonical4623 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4623 = injectiveMoment H node686 := by
  rfl

def raw4624 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def raw4624step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

theorem canonical4624 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4624 = injectiveMoment H node514 := by
  calc
    injectiveMoment H raw4624 = injectiveMoment H raw4624step0 := by
      have heq : raw4624step0 = (fun i j => raw4624 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4624 permutation9 permutation11
    _ = injectiveMoment H node514 := by rfl

def raw4625 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 2, -3], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def raw4625step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, 2, 0, -1], ![2, -3, 1, 0]]

def raw4625step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 2, 0], ![1, -2, 0, 1], ![-2, 3, -1, 0]]

def raw4625step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, 0, -2, 1]]

theorem canonical4625 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4625 = injectiveMoment H node1016 := by
  calc
    injectiveMoment H raw4625 = injectiveMoment H raw4625step0 := by
      have heq : raw4625step0 = raw4625.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4625).symm
    injectiveMoment H raw4625step0 = injectiveMoment H raw4625step1 := by
      have heq : raw4625step1 = -raw4625step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4625step0).symm
    injectiveMoment H raw4625step1 = injectiveMoment H raw4625step2 := by
      have heq : raw4625step2 = (fun i j => raw4625step1 (permutation13 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4625step1 permutation13 permutation32
    _ = injectiveMoment H node1016 := by rfl

def raw4626 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 0, -2, 1]]

def raw4626step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, 2, 1, -2], ![2, -3, 0, 1]]

def raw4626step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -2, 2, -1], ![1, 1, 0, -2]]

theorem canonical4626 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4626 = injectiveMoment H node617 := by
  calc
    injectiveMoment H raw4626 = injectiveMoment H raw4626step0 := by
      have heq : raw4626step0 = raw4626.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4626).symm
    injectiveMoment H raw4626step0 = injectiveMoment H raw4626step1 := by
      have heq : raw4626step1 = (fun i j => raw4626step0 (permutation20 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4626step0 permutation20 permutation26
    _ = injectiveMoment H node617 := by rfl

def raw4627 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def raw4627step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-1, 2, -1, 0], ![2, -3, 1, 0]]

def raw4627step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![1, -2, 1, 0], ![-2, 3, -1, 0]]

def raw4627step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 1, -1, -1]]

theorem canonical4627 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4627 = injectiveMoment H node1013 := by
  calc
    injectiveMoment H raw4627 = injectiveMoment H raw4627step0 := by
      have heq : raw4627step0 = raw4627.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4627).symm
    injectiveMoment H raw4627step0 = injectiveMoment H raw4627step1 := by
      have heq : raw4627step1 = -raw4627step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4627step0).symm
    injectiveMoment H raw4627step1 = injectiveMoment H raw4627step2 := by
      have heq : raw4627step2 = (fun i j => raw4627step1 (permutation14 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4627step1 permutation14 permutation32
    _ = injectiveMoment H node1013 := by rfl

def raw4628 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 3, -4], ![1, -2, -1, 2], ![1, 0, -1, 0]]

def raw4628step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, 3, -1, -1], ![2, -4, 2, 0]]

def raw4628step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 1, -2, 0]]

theorem canonical4628 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4628 = injectiveMoment H node927 := by
  calc
    injectiveMoment H raw4628 = injectiveMoment H raw4628step0 := by
      have heq : raw4628step0 = raw4628.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4628).symm
    injectiveMoment H raw4628step0 = injectiveMoment H raw4628step1 := by
      have heq : raw4628step1 = (fun i j => raw4628step0 (permutation24 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4628step0 permutation24 permutation31
    _ = injectiveMoment H node927 := by rfl

def raw4629 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -2, 1]]

def raw4629step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![-1, 3, 0, -2], ![2, -4, 1, 1]]

def raw4629step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![1, 1, -2, 0], ![1, 1, 2, -4]]

theorem canonical4629 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4629 = injectiveMoment H node586 := by
  calc
    injectiveMoment H raw4629 = injectiveMoment H raw4629step0 := by
      have heq : raw4629step0 = raw4629.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4629).symm
    injectiveMoment H raw4629step0 = injectiveMoment H raw4629step1 := by
      have heq : raw4629step1 = (fun i j => raw4629step0 (permutation23 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4629step0 permutation23 permutation31
    _ = injectiveMoment H node586 := by rfl

def raw4630 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 3, -4], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def raw4630step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![-1, 3, -2, 0], ![2, -4, 2, 0]]

def raw4630step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -2, -1, 3], ![0, 2, 2, -4], ![1, 1, -2, 0]]

theorem canonical4630 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4630 = injectiveMoment H node1089 := by
  calc
    injectiveMoment H raw4630 = injectiveMoment H raw4630step0 := by
      have heq : raw4630step0 = raw4630.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4630).symm
    injectiveMoment H raw4630step0 = injectiveMoment H raw4630step1 := by
      have heq : raw4630step1 = (fun i j => raw4630step0 (permutation18 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4630step0 permutation18 permutation31
    _ = injectiveMoment H node1089 := by rfl

def raw4631 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, -1, 1]]

theorem canonical4631 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4631 = injectiveMoment H node687 := by
  rfl

def raw4632 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![1, -2, -1, 2], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw4632step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![-1, -1, 3, -1], ![2, 2, -4, 0]]

def raw4632step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 1, -2, 0]]

theorem canonical4632 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4632 = injectiveMoment H node927 := by
  calc
    injectiveMoment H raw4632 = injectiveMoment H raw4632step0 := by
      have heq : raw4632step0 = raw4632.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4632).symm
    injectiveMoment H raw4632step0 = injectiveMoment H raw4632step1 := by
      have heq : raw4632step1 = (fun i j => raw4632step0 (permutation24 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4632step0 permutation24 permutation29
    _ = injectiveMoment H node927 := by rfl

def raw4633 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![1, -2, 2, -1], ![0, 0, -2, 2], ![1, 1, 1, -3]]

def raw4633step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, -2, 2, -1], ![1, 1, 1, -3]]

theorem canonical4633 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4633 = injectiveMoment H node682 := by
  calc
    injectiveMoment H raw4633 = injectiveMoment H raw4633step0 := by
      have heq : raw4633step0 = (fun i j => raw4633 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4633 permutation11 permutation9
    _ = injectiveMoment H node682 := by rfl

def raw4634 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![1, -2, 3, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw4634step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![-1, 3, -2, 0], ![2, -2, 1, -1]]

def raw4634step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![-1, 2, -1, 0], ![1, -3, 2, 0], ![-2, 2, -1, 1]]

def raw4634step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, -1, -2, 2]]

theorem canonical4634 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4634 = injectiveMoment H node1310 := by
  calc
    injectiveMoment H raw4634 = injectiveMoment H raw4634step0 := by
      have heq : raw4634step0 = raw4634.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4634).symm
    injectiveMoment H raw4634step0 = injectiveMoment H raw4634step1 := by
      have heq : raw4634step1 = -raw4634step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4634step0).symm
    injectiveMoment H raw4634step1 = injectiveMoment H raw4634step2 := by
      have heq : raw4634step2 = (fun i j => raw4634step1 (permutation9 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4634step1 permutation9 permutation31
    _ = injectiveMoment H node1310 := by rfl

def raw4635 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![1, -1, -2, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw4635step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -1, 1, -1], ![-1, -2, 3, 0], ![2, 2, -4, 0]]

def raw4635step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -2, -1, 3], ![0, 2, 2, -4], ![1, 1, -2, 0]]

theorem canonical4635 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4635 = injectiveMoment H node1089 := by
  calc
    injectiveMoment H raw4635 = injectiveMoment H raw4635step0 := by
      have heq : raw4635step0 = raw4635.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4635).symm
    injectiveMoment H raw4635step0 = injectiveMoment H raw4635step1 := by
      have heq : raw4635step1 = (fun i j => raw4635step0 (permutation18 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4635step0 permutation18 permutation29
    _ = injectiveMoment H node1089 := by rfl

def raw4636 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![1, -1, 2, -2], ![0, 1, -2, 1], ![1, -1, 1, -1]]

def raw4636step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem canonical4636 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4636 = injectiveMoment H node685 := by
  calc
    injectiveMoment H raw4636 = injectiveMoment H raw4636step0 := by
      have heq : raw4636step0 = (fun i j => raw4636 (permutation12 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4636 permutation12 permutation9
    _ = injectiveMoment H node685 := by rfl

def raw4637 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![1, -1, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0]]

def raw4637step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -1, 1, -1], ![-1, 3, -2, 0], ![2, -3, 1, 0]]

def raw4637step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![-1, 1, -1, 1], ![1, -3, 2, 0], ![-2, 3, -1, 0]]

def raw4637step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, -1, -1, 1]]

theorem canonical4637 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4637 = injectiveMoment H node1308 := by
  calc
    injectiveMoment H raw4637 = injectiveMoment H raw4637step0 := by
      have heq : raw4637step0 = raw4637.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4637).symm
    injectiveMoment H raw4637step0 = injectiveMoment H raw4637step1 := by
      have heq : raw4637step1 = -raw4637step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4637step0).symm
    injectiveMoment H raw4637step1 = injectiveMoment H raw4637step2 := by
      have heq : raw4637step2 = (fun i j => raw4637step1 (permutation14 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4637step1 permutation14 permutation31
    _ = injectiveMoment H node1308 := by rfl

def raw4638 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![1, 0, -2, 1], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def raw4638step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -2, 1]]

theorem canonical4638 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4638 = injectiveMoment H node686 := by
  calc
    injectiveMoment H raw4638 = injectiveMoment H raw4638step0 := by
      have heq : raw4638step0 = (fun i j => raw4638 (permutation12 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4638 permutation12 permutation9
    _ = injectiveMoment H node686 := by rfl

def raw4639 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, -1, 3], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw4639step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

theorem canonical4639 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4639 = injectiveMoment H node1986 := by
  calc
    injectiveMoment H raw4639 = injectiveMoment H raw4639step0 := by
      have heq : raw4639step0 = (fun i j => raw4639 (permutation72 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4639 permutation72 permutation15
    _ = injectiveMoment H node1986 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

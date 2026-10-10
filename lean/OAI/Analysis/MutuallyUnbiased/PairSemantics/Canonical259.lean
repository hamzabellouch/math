import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes51

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8288 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, 1, 1, -2], ![-1, 1, 2, -2], ![1, -1, 0, 0]]

def raw8288step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![-3, 1, 2, 0], ![4, -2, -2, 0]]

def raw8288step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, -1, -1, 1], ![3, -1, -2, 0], ![-4, 2, 2, 0]]

def raw8288step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, -1, -1, 1]]

theorem canonical8288 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8288 = injectiveMoment H node1298 := by
  calc
    injectiveMoment H raw8288 = injectiveMoment H raw8288step0 := by
      have heq : raw8288step0 = raw8288.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8288).symm
    injectiveMoment H raw8288step0 = injectiveMoment H raw8288step1 := by
      have heq : raw8288step1 = -raw8288step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8288step0).symm
    injectiveMoment H raw8288step1 = injectiveMoment H raw8288step2 := by
      have heq : raw8288step2 = (fun i j => raw8288step1 (permutation12 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8288step1 permutation12 permutation30
    _ = injectiveMoment H node1298 := by rfl

def raw8289 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -3, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![0, -1, 1, 0]]

def raw8289step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![1, 1, -2], ![1, 1, -2], ![-1, 1, 0]]

def raw8289step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

theorem canonical8289 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8289 = injectiveMoment H node244 := by
  calc
    injectiveMoment H raw8289 = injectiveMoment H raw8289step0 := by
      have hz : ∀ i, raw8289 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8289step0 = (fun i j => raw8289 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8289 permutation9 hz
    injectiveMoment H raw8289step0 = injectiveMoment H raw8289step1 := by
      have heq : raw8289step1 = (fun i j => raw8289step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8289step0 permutation13 permutation3
    _ = injectiveMoment H node244 := by rfl

def raw8290 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, -2, 3], ![-1, 0, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw8290step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 2, -3], ![1, 0, -2, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0]]

def raw8290step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -2, 0, 1]]

theorem canonical8290 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8290 = injectiveMoment H node2819 := by
  calc
    injectiveMoment H raw8290 = injectiveMoment H raw8290step0 := by
      have heq : raw8290step0 = -raw8290 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8290).symm
    injectiveMoment H raw8290step0 = injectiveMoment H raw8290step1 := by
      have heq : raw8290step1 = (fun i j => raw8290step0 (permutation143 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8290step0 permutation143 permutation11
    _ = injectiveMoment H node2819 := by rfl

def raw8291 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -2, 3], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw8291step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 2, -3], ![1, 0, -2, 1], ![0, -2, 0, 2], ![-1, 1, 0, 0]]

def raw8291step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, 0, 1]]

theorem canonical8291 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8291 = injectiveMoment H node1301 := by
  calc
    injectiveMoment H raw8291 = injectiveMoment H raw8291step0 := by
      have heq : raw8291step0 = -raw8291 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8291).symm
    injectiveMoment H raw8291step0 = injectiveMoment H raw8291step1 := by
      have heq : raw8291step1 = (fun i j => raw8291step0 (permutation31 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8291step0 permutation31 permutation11
    _ = injectiveMoment H node1301 := by rfl

def raw8292 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -2, 3], ![-1, 1, -1, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def raw8292step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 2, -3], ![1, -1, 1, -1], ![0, -1, -1, 2], ![-1, 1, -2, 2]]

def raw8292step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, -1, 1, -1]]

theorem canonical8292 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8292 = injectiveMoment H node1332 := by
  calc
    injectiveMoment H raw8292 = injectiveMoment H raw8292step0 := by
      have heq : raw8292step0 = -raw8292 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8292).symm
    injectiveMoment H raw8292step0 = injectiveMoment H raw8292step1 := by
      have heq : raw8292step1 = (fun i j => raw8292step0 (permutation31 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8292step0 permutation31 permutation9
    _ = injectiveMoment H node1332 := by rfl

def raw8293 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -2, 3], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw8293step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 2, -3], ![1, -1, -1, 1], ![0, -1, -1, 2], ![-1, 1, 0, 0]]

def raw8293step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, -1, -1, 1]]

theorem canonical8293 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8293 = injectiveMoment H node1299 := by
  calc
    injectiveMoment H raw8293 = injectiveMoment H raw8293step0 := by
      have heq : raw8293step0 = -raw8293 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8293).symm
    injectiveMoment H raw8293step0 = injectiveMoment H raw8293step1 := by
      have heq : raw8293step1 = (fun i j => raw8293step0 (permutation31 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8293step0 permutation31 permutation11
    _ = injectiveMoment H node1299 := by rfl

def raw8294 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -2, 3], ![-1, 2, 3, -4], ![1, -1, -1, 1]]

def raw8294step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 2, -1], ![-2, 3, -1], ![3, -4, 1]]

def raw8294step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, -2, 1], ![2, -3, 1], ![-3, 4, -1]]

def raw8294step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![1, 1, -2], ![1, 2, -3]]

theorem canonical8294 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8294 = injectiveMoment H node241 := by
  calc
    injectiveMoment H raw8294 = injectiveMoment H raw8294step0 := by
      have heq : raw8294step0 = raw8294.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8294).symm
    injectiveMoment H raw8294step0 = injectiveMoment H raw8294step1 := by
      have heq : raw8294step1 = -raw8294step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8294step0).symm
    injectiveMoment H raw8294step1 = injectiveMoment H raw8294step2 := by
      have heq : raw8294step2 = (fun i j => raw8294step1 (permutation27 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8294step1 permutation27 permutation7
    _ = injectiveMoment H node241 := by rfl

def raw8295 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, -1, 2, -1], ![0, 2, 0, -2]]

def raw8295step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![2, 0, -2]]

def raw8295step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

theorem canonical8295 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8295 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw8295 = injectiveMoment H raw8295step0 := by
      have hz : ∀ i, raw8295 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8295step0 = (fun i j => raw8295 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8295 permutation9 hz
    injectiveMoment H raw8295step0 = injectiveMoment H raw8295step1 := by
      have heq : raw8295step1 = (fun i j => raw8295step0 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8295step0 permutation4 permutation5
    _ = injectiveMoment H node36 := by rfl

def raw8296 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, -1, 3, -2], ![0, 2, -1, -1]]

def raw8296step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 2, -3], ![0, 1, -3, 2], ![0, -2, 1, 1]]

def raw8296step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -3, 2], ![-2, 1, 1]]

def raw8296step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![1, 2, -3]]

theorem canonical8296 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8296 = injectiveMoment H node43 := by
  calc
    injectiveMoment H raw8296 = injectiveMoment H raw8296step0 := by
      have heq : raw8296step0 = -raw8296 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8296).symm
    injectiveMoment H raw8296step0 = injectiveMoment H raw8296step1 := by
      have hz : ∀ i, raw8296step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8296step1 = (fun i j => raw8296step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8296step0 permutation9 hz
    injectiveMoment H raw8296step1 = injectiveMoment H raw8296step2 := by
      have heq : raw8296step2 = (fun i j => raw8296step1 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8296step1 permutation8 permutation3
    _ = injectiveMoment H node43 := by rfl

def raw8297 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def raw8297step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 2, -3], ![0, 0, -1, 1], ![1, -1, -1, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0]]

def raw8297step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

theorem canonical8297 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8297 = injectiveMoment H node2813 := by
  calc
    injectiveMoment H raw8297 = injectiveMoment H raw8297step0 := by
      have heq : raw8297step0 = -raw8297 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8297).symm
    injectiveMoment H raw8297step0 = injectiveMoment H raw8297step1 := by
      have heq : raw8297step1 = (fun i j => raw8297step0 (permutation137 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8297step0 permutation137 permutation11
    _ = injectiveMoment H node2813 := by rfl

def raw8298 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, -1, 0, 0]]

def raw8298step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![-2, 1, 1, 0], ![3, -1, -2, 0]]

def raw8298step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical8298 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8298 = injectiveMoment H node1206 := by
  calc
    injectiveMoment H raw8298 = injectiveMoment H raw8298step0 := by
      have heq : raw8298step0 = raw8298.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8298).symm
    injectiveMoment H raw8298step0 = injectiveMoment H raw8298step1 := by
      have heq : raw8298step1 = (fun i j => raw8298step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8298step0 permutation29 permutation20
    _ = injectiveMoment H node1206 := by rfl

def raw8299 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-1, 1, 1, -1], ![1, -1, 0, 0]]

def raw8299step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 2, -3], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, -1, -1, 1], ![-1, 1, 0, 0]]

def raw8299step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

theorem canonical8299 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8299 = injectiveMoment H node2813 := by
  calc
    injectiveMoment H raw8299 = injectiveMoment H raw8299step0 := by
      have heq : raw8299step0 = -raw8299 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8299).symm
    injectiveMoment H raw8299step0 = injectiveMoment H raw8299step1 := by
      have heq : raw8299step1 = (fun i j => raw8299step0 (permutation135 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8299step0 permutation135 permutation11
    _ = injectiveMoment H node2813 := by rfl

def raw8300 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, -1, 1, 0]]

def raw8300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0]]

def raw8300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8300 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8300 = injectiveMoment H node570 := by
  calc
    injectiveMoment H raw8300 = injectiveMoment H raw8300step0 := by
      have hz : ∀ i, raw8300 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8300step0 = (fun i j => raw8300 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8300 permutation9 hz
    injectiveMoment H raw8300step0 = injectiveMoment H raw8300step1 := by
      have heq : raw8300step1 = (fun i j => raw8300step0 (permutation42 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8300step0 permutation42 permutation5
    _ = injectiveMoment H node570 := by rfl

def raw8301 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, -1, 1, 0]]

def raw8301step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![2, 0, -2], ![-1, 1, 0]]

def raw8301step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8301 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8301 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw8301 = injectiveMoment H raw8301step0 := by
      have hz : ∀ i, raw8301 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8301step0 = (fun i j => raw8301 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8301 permutation9 hz
    injectiveMoment H raw8301step0 = injectiveMoment H raw8301step1 := by
      have heq : raw8301step1 = (fun i j => raw8301step0 (permutation12 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8301step0 permutation12 permutation5
    _ = injectiveMoment H node185 := by rfl

def raw8302 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, 0, 4, -4], ![0, 1, -2, 1]]

def raw8302step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

theorem canonical8302 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8302 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw8302 = injectiveMoment H raw8302step0 := by
      have hz : ∀ i, raw8302 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8302step0 = (fun i j => raw8302 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8302 permutation9 hz
    _ = injectiveMoment H node59 := by rfl

def raw8303 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, 1, 0, -1], ![-1, 1, 2, -2], ![1, -1, 0, 0]]

def raw8303step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 1, 1, -1], ![-2, 0, 2, 0], ![3, -1, -2, 0]]

def raw8303step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 1, -1]]

theorem canonical8303 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8303 = injectiveMoment H node1220 := by
  calc
    injectiveMoment H raw8303 = injectiveMoment H raw8303step0 := by
      have heq : raw8303step0 = raw8303.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8303).symm
    injectiveMoment H raw8303step0 = injectiveMoment H raw8303step1 := by
      have heq : raw8303step1 = (fun i j => raw8303step0 (permutation31 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8303step0 permutation31 permutation20
    _ = injectiveMoment H node1220 := by rfl

def raw8304 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![0, -1, 1, 0]]

def raw8304step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![-1, 1, 0]]

def raw8304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical8304 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8304 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw8304 = injectiveMoment H raw8304step0 := by
      have hz : ∀ i, raw8304 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8304step0 = (fun i j => raw8304 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8304 permutation9 hz
    injectiveMoment H raw8304step0 = injectiveMoment H raw8304step1 := by
      have heq : raw8304step1 = (fun i j => raw8304step0 (permutation10 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8304step0 permutation10 permutation5
    _ = injectiveMoment H node181 := by rfl

def raw8305 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, 1, 3, -4], ![0, 0, -1, 1]]

def raw8305step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 2, -3], ![0, -1, -3, 4], ![0, 0, 1, -1]]

def raw8305step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![-1, -3, 4], ![0, 1, -1]]

def raw8305step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![1, 2, -3]]

theorem canonical8305 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8305 = injectiveMoment H node51 := by
  calc
    injectiveMoment H raw8305 = injectiveMoment H raw8305step0 := by
      have heq : raw8305step0 = -raw8305 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8305).symm
    injectiveMoment H raw8305step0 = injectiveMoment H raw8305step1 := by
      have hz : ∀ i, raw8305step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8305step1 = (fun i j => raw8305step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8305step0 permutation9 hz
    injectiveMoment H raw8305step1 = injectiveMoment H raw8305step2 := by
      have heq : raw8305step2 = (fun i j => raw8305step1 (permutation6 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8305step1 permutation6 permutation3
    _ = injectiveMoment H node51 := by rfl

def raw8306 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -2, 3], ![0, 2, 2, -4], ![0, -1, 0, 1]]

def raw8306step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 2, -1], ![-2, 2, 0], ![3, -4, 1]]

def raw8306step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![-3, 4, -1]]

def raw8306step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -2, 1], ![2, -2, 0], ![-3, 4, -1]]

def raw8306step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

theorem canonical8306 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8306 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw8306 = injectiveMoment H raw8306step0 := by
      have heq : raw8306step0 = raw8306.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8306).symm
    injectiveMoment H raw8306step0 = injectiveMoment H raw8306step1 := by
      have heq : raw8306step1 = -raw8306step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8306step0).symm
    injectiveMoment H raw8306step1 = injectiveMoment H raw8306step2 := by
      have hz : ∀ j, raw8306step1 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8306step2 = (fun i j => raw8306step1 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8306step1 permutation9 hz
    injectiveMoment H raw8306step2 = injectiveMoment H raw8306step3 := by
      have heq : raw8306step3 = (fun i j => raw8306step2 (permutation8 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8306step2 permutation8 permutation7
    _ = injectiveMoment H node52 := by rfl

def raw8307 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -1, 2], ![-1, -1, 0, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8307step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical8307 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8307 = injectiveMoment H node998 := by
  calc
    injectiveMoment H raw8307 = injectiveMoment H raw8307step0 := by
      have heq : raw8307step0 = (fun i j => raw8307 (permutation15 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8307 permutation15 permutation9
    _ = injectiveMoment H node998 := by rfl

def raw8308 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -1, 2], ![-1, -1, 1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8308step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical8308 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8308 = injectiveMoment H node1099 := by
  calc
    injectiveMoment H raw8308 = injectiveMoment H raw8308step0 := by
      have heq : raw8308step0 = (fun i j => raw8308 (permutation15 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8308 permutation15 permutation9
    _ = injectiveMoment H node1099 := by rfl

def raw8309 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -1, 2], ![-1, 1, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0]]

def raw8309step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 3, -2, 0], ![2, -3, 1, 0]]

def raw8309step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem canonical8309 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8309 = injectiveMoment H node1094 := by
  calc
    injectiveMoment H raw8309 = injectiveMoment H raw8309step0 := by
      have heq : raw8309step0 = raw8309.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8309).symm
    injectiveMoment H raw8309step0 = injectiveMoment H raw8309step1 := by
      have heq : raw8309step1 = (fun i j => raw8309step0 (permutation18 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8309step0 permutation18 permutation28
    _ = injectiveMoment H node1094 := by rfl

def raw8310 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -1, 2], ![-1, 2, 2, -3], ![1, -1, -1, 1]]

def raw8310step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 2, -1], ![-1, 2, -1], ![2, -3, 1]]

def raw8310step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![-2, 3, -1]]

def raw8310step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical8310 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8310 = injectiveMoment H node175 := by
  calc
    injectiveMoment H raw8310 = injectiveMoment H raw8310step0 := by
      have heq : raw8310step0 = raw8310.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8310).symm
    injectiveMoment H raw8310step0 = injectiveMoment H raw8310step1 := by
      have heq : raw8310step1 = -raw8310step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8310step0).symm
    injectiveMoment H raw8310step1 = injectiveMoment H raw8310step2 := by
      have heq : raw8310step2 = (fun i j => raw8310step1 (permutation27 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8310step1 permutation27 permutation4
    _ = injectiveMoment H node175 := by rfl

def raw8311 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, -1, -1, 2], ![0, 2, 2, -4]]

def raw8311step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 1, 1, -2], ![0, -2, -2, 4]]

def raw8311step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-2, -2, 4]]

def raw8311step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 1, -2], ![1, 1, -2]]

theorem canonical8311 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8311 = injectiveMoment H node35 := by
  calc
    injectiveMoment H raw8311 = injectiveMoment H raw8311step0 := by
      have heq : raw8311step0 = -raw8311 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8311).symm
    injectiveMoment H raw8311step0 = injectiveMoment H raw8311step1 := by
      have hz : ∀ i, raw8311step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8311step1 = (fun i j => raw8311step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8311step0 permutation9 hz
    injectiveMoment H raw8311step1 = injectiveMoment H raw8311step2 := by
      have heq : raw8311step2 = (fun i j => raw8311step1 (permutation7 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8311step1 permutation7 permutation3
    _ = injectiveMoment H node35 := by rfl

def raw8312 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, -1, 0, 1], ![-1, 2, 2, -3], ![1, 0, -1, 0]]

def raw8312step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 2, 0], ![-1, 0, 2, -1], ![2, 1, -3, 0]]

def raw8312step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 0, -2, 1], ![-2, -1, 3, 0]]

def raw8312step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical8312 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8312 = injectiveMoment H node1198 := by
  calc
    injectiveMoment H raw8312 = injectiveMoment H raw8312step0 := by
      have heq : raw8312step0 = raw8312.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8312).symm
    injectiveMoment H raw8312step0 = injectiveMoment H raw8312step1 := by
      have heq : raw8312step1 = -raw8312step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8312step0).symm
    injectiveMoment H raw8312step1 = injectiveMoment H raw8312step2 := by
      have heq : raw8312step2 = (fun i j => raw8312step1 (permutation28 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8312step1 permutation28 permutation19
    _ = injectiveMoment H node1198 := by rfl

def raw8313 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 2, 2, -4], ![0, 0, -1, 1]]

def raw8313step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 1, 0, -1], ![0, -2, -2, 4], ![0, 0, 1, -1]]

def raw8313step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, -2, 4], ![0, 1, -1]]

def raw8313step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical8313 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8313 = injectiveMoment H node150 := by
  calc
    injectiveMoment H raw8313 = injectiveMoment H raw8313step0 := by
      have heq : raw8313step0 = -raw8313 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8313).symm
    injectiveMoment H raw8313step0 = injectiveMoment H raw8313step1 := by
      have hz : ∀ i, raw8313step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8313step1 = (fun i j => raw8313step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8313step0 permutation9 hz
    injectiveMoment H raw8313step1 = injectiveMoment H raw8313step2 := by
      have heq : raw8313step2 = (fun i j => raw8313step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8313step1 permutation26 permutation3
    _ = injectiveMoment H node150 := by rfl

def raw8314 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, -1, 1, 0], ![-1, 2, 1, -2], ![1, 0, -1, 0]]

def raw8314step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, -1, 2, 0], ![-1, 1, 1, -1], ![2, 0, -2, 0]]

def raw8314step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

theorem canonical8314 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8314 = injectiveMoment H node1265 := by
  calc
    injectiveMoment H raw8314 = injectiveMoment H raw8314step0 := by
      have heq : raw8314step0 = raw8314.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8314).symm
    injectiveMoment H raw8314step0 = injectiveMoment H raw8314step1 := by
      have heq : raw8314step1 = (fun i j => raw8314step0 (permutation19 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8314step0 permutation19 permutation19
    _ = injectiveMoment H node1265 := by rfl

def raw8315 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![0, 0, -1, 1]]

def raw8315step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 1, -1, 0], ![0, -2, -1, 3], ![0, 0, 1, -1]]

def raw8315step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-2, -1, 3], ![0, 1, -1]]

def raw8315step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical8315 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8315 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw8315 = injectiveMoment H raw8315step0 := by
      have heq : raw8315step0 = -raw8315 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8315).symm
    injectiveMoment H raw8315step0 = injectiveMoment H raw8315step1 := by
      have hz : ∀ i, raw8315step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8315step1 = (fun i j => raw8315step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8315step0 permutation9 hz
    injectiveMoment H raw8315step1 = injectiveMoment H raw8315step2 := by
      have heq : raw8315step2 = (fun i j => raw8315step1 (permutation26 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8315step1 permutation26 permutation3
    _ = injectiveMoment H node181 := by rfl

def raw8316 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, -1, 2, -1], ![0, 2, -1, -1]]

def raw8316step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 1, -2, 1], ![0, -2, 1, 1]]

def raw8316step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![1, -2, 1], ![-2, 1, 1]]

def raw8316step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical8316 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8316 = injectiveMoment H node44 := by
  calc
    injectiveMoment H raw8316 = injectiveMoment H raw8316step0 := by
      have heq : raw8316step0 = -raw8316 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8316).symm
    injectiveMoment H raw8316step0 = injectiveMoment H raw8316step1 := by
      have hz : ∀ i, raw8316step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8316step1 = (fun i j => raw8316step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8316step0 permutation9 hz
    injectiveMoment H raw8316step1 = injectiveMoment H raw8316step2 := by
      have heq : raw8316step2 = (fun i j => raw8316step1 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8316step1 permutation8 permutation3
    _ = injectiveMoment H node44 := by rfl

def raw8317 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, -1, 3, -2], ![0, 2, -2, 0]]

def raw8317step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![2, -2, 0]]

def raw8317step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

theorem canonical8317 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8317 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw8317 = injectiveMoment H raw8317step0 := by
      have hz : ∀ i, raw8317 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8317step0 = (fun i j => raw8317 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8317 permutation9 hz
    injectiveMoment H raw8317step0 = injectiveMoment H raw8317step1 := by
      have heq : raw8317step1 = (fun i j => raw8317step0 (permutation6 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8317step0 permutation6 permutation7
    _ = injectiveMoment H node36 := by rfl

def raw8318 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 0, 2, 0], ![1, 2, 1, -4]]

def raw8318step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, 1, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![2, 0, -2, 0], ![-1, -2, -1, 4]]

def raw8318step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical8318 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8318 = injectiveMoment H node2931 := by
  calc
    injectiveMoment H raw8318 = injectiveMoment H raw8318step0 := by
      have heq : raw8318step0 = -raw8318 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8318).symm
    injectiveMoment H raw8318step0 = injectiveMoment H raw8318step1 := by
      have heq : raw8318step1 = (fun i j => raw8318step0 (permutation342 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8318step0 permutation342 permutation15
    _ = injectiveMoment H node2931 := by rfl

def raw8319 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 1, 1, 0], ![1, 1, 2, -4]]

def raw8319step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

theorem canonical8319 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8319 = injectiveMoment H node3300 := by
  calc
    injectiveMoment H raw8319 = injectiveMoment H raw8319step0 := by
      have heq : raw8319step0 = (fun i j => raw8319 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8319 permutation258 permutation9
    _ = injectiveMoment H node3300 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

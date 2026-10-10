import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8000 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0]]

def raw8000step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

theorem canonical8000 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8000 = injectiveMoment H node269 := by
  calc
    injectiveMoment H raw8000 = injectiveMoment H raw8000step0 := by
      have heq : raw8000step0 = (fun i j => raw8000 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8000 permutation23 permutation4
    _ = injectiveMoment H node269 := by rfl

def raw8001 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1]]

def raw8001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical8001 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8001 = injectiveMoment H node1293 := by
  calc
    injectiveMoment H raw8001 = injectiveMoment H raw8001step0 := by
      have heq : raw8001step0 = (fun i j => raw8001 (permutation112 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8001 permutation112 permutation4
    _ = injectiveMoment H node1293 := by rfl

def raw8002 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0]]

def raw8002step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

def raw8002step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical8002 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8002 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw8002 = injectiveMoment H raw8002step0 := by
      have hz : ∀ j, raw8002 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw8002step0 = (fun i j => raw8002 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8002 permutation128 hz
    injectiveMoment H raw8002step0 = injectiveMoment H raw8002step1 := by
      have hz : ∀ i, raw8002step0 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8002step1 = (fun i j => raw8002step0 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8002step0 permutation3 hz
    _ = injectiveMoment H node26 := by rfl

def raw8003 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0]]

def raw8003step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -3, 3], ![0, 1, -1], ![0, 2, -2]]

def raw8003step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical8003 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8003 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw8003 = injectiveMoment H raw8003step0 := by
      have hz : ∀ j, raw8003 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw8003step0 = (fun i j => raw8003 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8003 permutation27 hz
    injectiveMoment H raw8003step0 = injectiveMoment H raw8003step1 := by
      have hz : ∀ i, raw8003step0 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8003step1 = (fun i j => raw8003step0 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8003step0 permutation3 hz
    _ = injectiveMoment H node10 := by rfl

def raw8004 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, 1, -1], ![0, 3, -3], ![0, -1, 1]]

def raw8004step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![3, -3], ![-1, 1]]

def raw8004step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]

theorem canonical8004 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8004 = injectiveMoment H node24 := by
  calc
    injectiveMoment H raw8004 = injectiveMoment H raw8004step0 := by
      have hz : ∀ i, raw8004 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8004step0 = (fun i j => raw8004 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8004 permutation3 hz
    injectiveMoment H raw8004step0 = injectiveMoment H raw8004step1 := by
      have heq : raw8004step1 = (fun i j => raw8004step0 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8004step0 permutation13 permutation1
    _ = injectiveMoment H node24 := by rfl

def raw8005 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, -3, 3], ![0, 3, -3]]

def raw8005step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]

theorem canonical8005 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8005 = injectiveMoment H node3 := by
  calc
    injectiveMoment H raw8005 = injectiveMoment H raw8005step0 := by
      have hz : ∀ i, raw8005 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8005step0 = (fun i j => raw8005 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8005 permutation3 hz
    _ = injectiveMoment H node3 := by rfl

def raw8006 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -3, 3], ![0, 3, -3], ![0, 0, 0]]

def raw8006step0 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, -3, 3], ![0, 3, -3]]

def raw8006step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]

theorem canonical8006 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8006 = injectiveMoment H node3 := by
  calc
    injectiveMoment H raw8006 = injectiveMoment H raw8006step0 := by
      have hz : ∀ j, raw8006 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw8006step0 = (fun i j => raw8006 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8006 permutation7 hz
    injectiveMoment H raw8006step0 = injectiveMoment H raw8006step1 := by
      have hz : ∀ i, raw8006step0 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8006step1 = (fun i j => raw8006step0 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8006step0 permutation3 hz
    _ = injectiveMoment H node3 := by rfl

def raw8007 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -3, 3], ![0, 4, -4], ![0, -1, 1]]

def raw8007step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![4, -4], ![-1, 1]]

def raw8007step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]

theorem canonical8007 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8007 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw8007 = injectiveMoment H raw8007step0 := by
      have hz : ∀ i, raw8007 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8007step0 = (fun i j => raw8007 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8007 permutation3 hz
    injectiveMoment H raw8007step0 = injectiveMoment H raw8007step1 := by
      have heq : raw8007step1 = (fun i j => raw8007step0 (permutation6 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8007step0 permutation6 permutation2
    _ = injectiveMoment H node8 := by rfl

def raw8008 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -2, 4], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw8008step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 2, -4], ![1, 0, -1, 0], ![0, 0, -1, 1], ![0, -2, 0, 2], ![-1, 0, 0, 1]]

def raw8008step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical8008 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8008 = injectiveMoment H node2739 := by
  calc
    injectiveMoment H raw8008 = injectiveMoment H raw8008step0 := by
      have heq : raw8008step0 = -raw8008 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8008).symm
    injectiveMoment H raw8008step0 = injectiveMoment H raw8008step1 := by
      have heq : raw8008step1 = (fun i j => raw8008step0 (permutation149 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8008step0 permutation149 permutation9
    _ = injectiveMoment H node2739 := by rfl

def raw8009 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -2, 4], ![-1, 0, 1, 0], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def raw8009step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 2, 0], ![-2, 1, 1, 0], ![4, 0, -3, -1]]

def raw8009step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem canonical8009 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8009 = injectiveMoment H node1178 := by
  calc
    injectiveMoment H raw8009 = injectiveMoment H raw8009step0 := by
      have heq : raw8009step0 = raw8009.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8009).symm
    injectiveMoment H raw8009step0 = injectiveMoment H raw8009step1 := by
      have heq : raw8009step1 = (fun i j => raw8009step0 (permutation30 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8009step0 permutation30 permutation30
    _ = injectiveMoment H node1178 := by rfl

def raw8010 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -2, 4], ![-1, 0, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw8010step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 2, -4], ![1, 0, -2, 1], ![0, 0, -1, 1], ![0, -2, 0, 2], ![-1, 0, 1, 0]]

def raw8010step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical8010 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8010 = injectiveMoment H node2804 := by
  calc
    injectiveMoment H raw8010 = injectiveMoment H raw8010step0 := by
      have heq : raw8010step0 = -raw8010 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8010).symm
    injectiveMoment H raw8010step0 = injectiveMoment H raw8010step1 := by
      have heq : raw8010step1 = (fun i j => raw8010step0 (permutation149 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8010step0 permutation149 permutation9
    _ = injectiveMoment H node2804 := by rfl

def raw8011 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -2, 4], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw8011step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 2, -4], ![1, 0, -2, 1], ![0, -1, -1, 2], ![-1, -1, 1, 1]]

def raw8011step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical8011 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8011 = injectiveMoment H node1100 := by
  calc
    injectiveMoment H raw8011 = injectiveMoment H raw8011step0 := by
      have heq : raw8011step0 = -raw8011 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8011).symm
    injectiveMoment H raw8011step0 = injectiveMoment H raw8011step1 := by
      have heq : raw8011step1 = (fun i j => raw8011step0 (permutation31 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8011step0 permutation31 permutation9
    _ = injectiveMoment H node1100 := by rfl

def raw8012 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -2, 4], ![-1, 0, 3, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw8012step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 2, -4], ![1, 0, -3, 2], ![0, -2, 0, 2], ![-1, 0, 1, 0]]

def raw8012step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 2, 2, -4], ![1, 0, -3, 2]]

theorem canonical8012 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8012 = injectiveMoment H node1297 := by
  calc
    injectiveMoment H raw8012 = injectiveMoment H raw8012step0 := by
      have heq : raw8012step0 = -raw8012 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8012).symm
    injectiveMoment H raw8012step0 = injectiveMoment H raw8012step1 := by
      have heq : raw8012step1 = (fun i j => raw8012step0 (permutation31 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8012step0 permutation31 permutation9
    _ = injectiveMoment H node1297 := by rfl

def raw8013 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw8013step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 2, -4], ![0, 0, -1, 1], ![1, 0, -1, 0], ![0, -2, 0, 2], ![-1, 0, 0, 1]]

def raw8013step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical8013 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8013 = injectiveMoment H node2739 := by
  calc
    injectiveMoment H raw8013 = injectiveMoment H raw8013step0 := by
      have heq : raw8013step0 = -raw8013 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8013).symm
    injectiveMoment H raw8013step0 = injectiveMoment H raw8013step1 := by
      have heq : raw8013step1 = (fun i j => raw8013step0 (permutation147 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8013step0 permutation147 permutation9
    _ = injectiveMoment H node2739 := by rfl

def raw8014 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 1, -1], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def raw8014step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 2, -4], ![0, 0, -1, 1], ![1, 0, -2, 1], ![0, -2, 0, 2], ![-1, 0, 1, 0]]

def raw8014step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical8014 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8014 = injectiveMoment H node2804 := by
  calc
    injectiveMoment H raw8014 = injectiveMoment H raw8014step0 := by
      have heq : raw8014step0 = -raw8014 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8014).symm
    injectiveMoment H raw8014step0 = injectiveMoment H raw8014step1 := by
      have heq : raw8014step1 = (fun i j => raw8014step0 (permutation147 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8014step0 permutation147 permutation9
    _ = injectiveMoment H node2804 := by rfl

def raw8015 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, 0, 0, -1]]

def raw8015step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 2, 0], ![-2, 1, 1, 0], ![4, -1, -2, -1]]

def raw8015step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical8015 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8015 = injectiveMoment H node914 := by
  calc
    injectiveMoment H raw8015 = injectiveMoment H raw8015step0 := by
      have heq : raw8015step0 = raw8015.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8015).symm
    injectiveMoment H raw8015step0 = injectiveMoment H raw8015step1 := by
      have heq : raw8015step1 = (fun i j => raw8015step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8015step0 permutation29 permutation20
    _ = injectiveMoment H node914 := by rfl

def raw8016 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![1, 0, 0, -1]]

def raw8016step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 2, -4], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 0, 1], ![-1, 0, 0, 1]]

def raw8016step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical8016 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8016 = injectiveMoment H node2749 := by
  calc
    injectiveMoment H raw8016 = injectiveMoment H raw8016step0 := by
      have heq : raw8016step0 = -raw8016 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8016).symm
    injectiveMoment H raw8016step0 = injectiveMoment H raw8016step1 := by
      have heq : raw8016step1 = (fun i j => raw8016step0 (permutation135 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8016step0 permutation135 permutation11
    _ = injectiveMoment H node2749 := by rfl

def raw8017 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, 0, -1, 0]]

def raw8017step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 2, -4], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, -1, 2], ![-1, 0, 1, 0]]

def raw8017step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -2, -1, 2]]

theorem canonical8017 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8017 = injectiveMoment H node2820 := by
  calc
    injectiveMoment H raw8017 = injectiveMoment H raw8017step0 := by
      have heq : raw8017step0 = -raw8017 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8017).symm
    injectiveMoment H raw8017step0 = injectiveMoment H raw8017step1 := by
      have heq : raw8017step1 = (fun i j => raw8017step0 (permutation135 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8017step0 permutation135 permutation9
    _ = injectiveMoment H node2820 := by rfl

def raw8018 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![0, 0, 0, 0]]

def raw8018step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2]]

def raw8018step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical8018 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8018 = injectiveMoment H node145 := by
  calc
    injectiveMoment H raw8018 = injectiveMoment H raw8018step0 := by
      have hz : ∀ j, raw8018 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw8018step0 = (fun i j => raw8018 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8018 permutation128 hz
    injectiveMoment H raw8018step0 = injectiveMoment H raw8018step1 := by
      have hz : ∀ i, raw8018step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8018step1 = (fun i j => raw8018step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8018step0 permutation9 hz
    _ = injectiveMoment H node145 := by rfl

def raw8019 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![0, 0, 0, 0]]

def raw8019step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 0, 0], ![-2, 0, 2, 0], ![-2, 1, 1, 0], ![4, -1, -3, 0]]

def raw8019step1 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![-2, 1, 1, 0], ![4, -1, -3, 0]]

def raw8019step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![4, -1, -3]]

def raw8019step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

theorem canonical8019 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8019 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw8019 = injectiveMoment H raw8019step0 := by
      have heq : raw8019step0 = raw8019.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8019).symm
    injectiveMoment H raw8019step0 = injectiveMoment H raw8019step1 := by
      have hz : ∀ j, raw8019step0 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8019step1 = (fun i j => raw8019step0 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8019step0 permutation9 hz
    injectiveMoment H raw8019step1 = injectiveMoment H raw8019step2 := by
      have hz : ∀ i, raw8019step1 i (permutation27 0) = 0 := by decide +kernel
      have heq : raw8019step2 = (fun i j => raw8019step1 i (permutation27 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8019step1 permutation27 hz
    injectiveMoment H raw8019step2 = injectiveMoment H raw8019step3 := by
      have heq : raw8019step3 = (fun i j => raw8019step2 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8019step2 permutation7 permutation6
    _ = injectiveMoment H node52 := by rfl

def raw8020 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 2, -2], ![-1, 2, 1, -2], ![1, 0, -1, 0]]

def raw8020step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 2, -4], ![0, 0, -2, 2], ![1, -2, -1, 2], ![-1, 0, 1, 0]]

def raw8020step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, -1, 2]]

theorem canonical8020 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8020 = injectiveMoment H node1302 := by
  calc
    injectiveMoment H raw8020 = injectiveMoment H raw8020step0 := by
      have heq : raw8020step0 = -raw8020 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8020).symm
    injectiveMoment H raw8020step0 = injectiveMoment H raw8020step1 := by
      have heq : raw8020step1 = (fun i j => raw8020step0 (permutation29 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8020step0 permutation29 permutation9
    _ = injectiveMoment H node1302 := by rfl

def raw8021 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 2, -2], ![0, 2, 0, -2]]

def raw8021step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]

theorem canonical8021 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8021 = injectiveMoment H node31 := by
  calc
    injectiveMoment H raw8021 = injectiveMoment H raw8021step0 := by
      have hz : ∀ i, raw8021 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8021step0 = (fun i j => raw8021 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8021 permutation9 hz
    _ = injectiveMoment H node31 := by rfl

def raw8022 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![0, 0, 0, 0]]

def raw8022step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 2, -2], ![0, 2, 0, -2]]

def raw8022step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]

theorem canonical8022 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8022 = injectiveMoment H node31 := by
  calc
    injectiveMoment H raw8022 = injectiveMoment H raw8022step0 := by
      have hz : ∀ j, raw8022 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw8022step0 = (fun i j => raw8022 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8022 permutation27 hz
    injectiveMoment H raw8022step0 = injectiveMoment H raw8022step1 := by
      have hz : ∀ i, raw8022step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8022step1 = (fun i j => raw8022step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8022step0 permutation9 hz
    _ = injectiveMoment H node31 := by rfl

def raw8023 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 0, 3, -3], ![0, 2, -1, -1]]

def raw8023step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

theorem canonical8023 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8023 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw8023 = injectiveMoment H raw8023step0 := by
      have hz : ∀ i, raw8023 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8023step0 = (fun i j => raw8023 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8023 permutation9 hz
    _ = injectiveMoment H node32 := by rfl

def raw8024 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, -2, 4], ![0, 1, 1, -2], ![0, 1, 1, -2]]

def raw8024step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 1, -2], ![1, 1, -2]]

theorem canonical8024 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8024 = injectiveMoment H node35 := by
  calc
    injectiveMoment H raw8024 = injectiveMoment H raw8024step0 := by
      have hz : ∀ i, raw8024 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8024step0 = (fun i j => raw8024 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8024 permutation9 hz
    _ = injectiveMoment H node35 := by rfl

def raw8025 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw8025step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 1, -3], ![1, 0, -1, 0], ![0, 0, -1, 1], ![0, -2, 1, 1], ![-1, 0, 0, 1]]

def raw8025step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical8025 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8025 = injectiveMoment H node2742 := by
  calc
    injectiveMoment H raw8025 = injectiveMoment H raw8025step0 := by
      have heq : raw8025step0 = -raw8025 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8025).symm
    injectiveMoment H raw8025step0 = injectiveMoment H raw8025step1 := by
      have heq : raw8025step1 = (fun i j => raw8025step0 (permutation149 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8025step0 permutation149 permutation9
    _ = injectiveMoment H node2742 := by rfl

def raw8026 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![-1, 0, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def raw8026step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 2, 0], ![-1, 1, 1, -1], ![3, 0, -3, 0]]

def raw8026step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -1, 0, 0]]

theorem canonical8026 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8026 = injectiveMoment H node1345 := by
  calc
    injectiveMoment H raw8026 = injectiveMoment H raw8026step0 := by
      have heq : raw8026step0 = raw8026.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8026).symm
    injectiveMoment H raw8026step0 = injectiveMoment H raw8026step1 := by
      have heq : raw8026step1 = (fun i j => raw8026step0 (permutation24 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8026step0 permutation24 permutation29
    _ = injectiveMoment H node1345 := by rfl

def raw8027 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8027step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 1, -3], ![1, 0, -2, 1], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 0, 0, 1]]

def raw8027step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical8027 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8027 = injectiveMoment H node2750 := by
  calc
    injectiveMoment H raw8027 = injectiveMoment H raw8027step0 := by
      have heq : raw8027step0 = -raw8027 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8027).symm
    injectiveMoment H raw8027step0 = injectiveMoment H raw8027step1 := by
      have heq : raw8027step1 = (fun i j => raw8027step0 (permutation149 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8027step0 permutation149 permutation9
    _ = injectiveMoment H node2750 := by rfl

def raw8028 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![-1, 0, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw8028step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 1, -3], ![1, 0, -2, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0]]

def raw8028step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical8028 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8028 = injectiveMoment H node2812 := by
  calc
    injectiveMoment H raw8028 = injectiveMoment H raw8028step0 := by
      have heq : raw8028step0 = -raw8028 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8028).symm
    injectiveMoment H raw8028step0 = injectiveMoment H raw8028step1 := by
      have heq : raw8028step1 = (fun i j => raw8028step0 (permutation143 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8028step0 permutation143 permutation9
    _ = injectiveMoment H node2812 := by rfl

def raw8029 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def raw8029step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 1, -3], ![1, 0, -2, 1], ![0, -1, -1, 2], ![-1, -1, 2, 0]]

def raw8029step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![1, 0, 1, -2]]

theorem canonical8029 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8029 = injectiveMoment H node1007 := by
  calc
    injectiveMoment H raw8029 = injectiveMoment H raw8029step0 := by
      have heq : raw8029step0 = -raw8029 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8029).symm
    injectiveMoment H raw8029step0 = injectiveMoment H raw8029step1 := by
      have heq : raw8029step1 = (fun i j => raw8029step0 (permutation31 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8029step0 permutation31 permutation10
    _ = injectiveMoment H node1007 := by rfl

def raw8030 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![-1, 0, 3, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw8030step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 1, -3], ![1, 0, -3, 2], ![0, -1, 2, -1], ![-1, -1, 0, 2]]

def raw8030step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, 0, -3, 2]]

theorem canonical8030 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8030 = injectiveMoment H node1011 := by
  calc
    injectiveMoment H raw8030 = injectiveMoment H raw8030step0 := by
      have heq : raw8030step0 = -raw8030 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8030).symm
    injectiveMoment H raw8030step0 = injectiveMoment H raw8030step1 := by
      have heq : raw8030step1 = (fun i j => raw8030step0 (permutation31 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8030step0 permutation31 permutation9
    _ = injectiveMoment H node1011 := by rfl

def raw8031 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![-1, 1, -1, 1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw8031step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem canonical8031 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8031 = injectiveMoment H node1094 := by
  calc
    injectiveMoment H raw8031 = injectiveMoment H raw8031step0 := by
      have heq : raw8031step0 = (fun i j => raw8031 (permutation15 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8031 permutation15 permutation11
    _ = injectiveMoment H node1094 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

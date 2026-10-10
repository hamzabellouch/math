import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes35

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4704 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw4704step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

theorem canonical4704 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4704 = injectiveMoment H node1639 := by
  calc
    injectiveMoment H raw4704 = injectiveMoment H raw4704step0 := by
      have heq : raw4704step0 = (fun i j => raw4704 (permutation71 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4704 permutation71 permutation29
    _ = injectiveMoment H node1639 := by rfl

def raw4705 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, -2, 2], ![1, 0, -1, 0]]

theorem canonical4705 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4705 = injectiveMoment H node2265 := by
  rfl

def raw4706 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -2, 1]]

theorem canonical4706 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4706 = injectiveMoment H node2266 := by
  rfl

def raw4707 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -3, 2]]

theorem canonical4707 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4707 = injectiveMoment H node2267 := by
  rfl

def raw4708 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, -1, -3, 3], ![1, 1, 0, -2]]

def raw4708step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![0, 3, -3, 0], ![1, -2, 3, -2]]

def raw4708step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![1, -2, 0, 1], ![1, 1, -1, -1]]

theorem canonical4708 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4708 = injectiveMoment H node675 := by
  calc
    injectiveMoment H raw4708 = injectiveMoment H raw4708step0 := by
      have heq : raw4708step0 = raw4708.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4708).symm
    injectiveMoment H raw4708step0 = injectiveMoment H raw4708step1 := by
      have heq : raw4708step1 = (fun i j => raw4708step0 (permutation31 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4708step0 permutation31 permutation27
    _ = injectiveMoment H node675 := by rfl

def raw4709 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, -1, -2, 2], ![1, 1, -1, -1]]

theorem canonical4709 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4709 = injectiveMoment H node690 := by
  rfl

def raw4710 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 1, -2, 0]]

def raw4710step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]

theorem canonical4710 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4710 = injectiveMoment H node490 := by
  calc
    injectiveMoment H raw4710 = injectiveMoment H raw4710step0 := by
      have heq : raw4710step0 = (fun i j => raw4710 (permutation20 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4710 permutation20 permutation29
    _ = injectiveMoment H node490 := by rfl

def raw4711 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def raw4711step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![0, 3, 0, -3], ![1, -2, 0, 1]]

def raw4711step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -2, 0, 1]]

theorem canonical4711 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4711 = injectiveMoment H node1352 := by
  calc
    injectiveMoment H raw4711 = injectiveMoment H raw4711step0 := by
      have heq : raw4711step0 = raw4711.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4711).symm
    injectiveMoment H raw4711step0 = injectiveMoment H raw4711step1 := by
      have heq : raw4711step1 = (fun i j => raw4711step0 (permutation18 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4711step0 permutation18 permutation21
    _ = injectiveMoment H node1352 := by rfl

def raw4712 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, 0, -3, 2], ![1, 0, 0, -1]]

def raw4712step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem canonical4712 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4712 = injectiveMoment H node1231 := by
  calc
    injectiveMoment H raw4712 = injectiveMoment H raw4712step0 := by
      have heq : raw4712step0 = (fun i j => raw4712 (permutation20 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4712 permutation20 permutation16
    _ = injectiveMoment H node1231 := by rfl

def raw4713 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, 0, -2, 1], ![1, 0, -1, 0]]

def raw4713step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical4713 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4713 = injectiveMoment H node801 := by
  calc
    injectiveMoment H raw4713 = injectiveMoment H raw4713step0 := by
      have heq : raw4713step0 = (fun i j => raw4713 (permutation20 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4713 permutation20 permutation19
    _ = injectiveMoment H node801 := by rfl

def raw4714 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, 0, -1, 0], ![1, 0, -2, 1]]

def raw4714step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical4714 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4714 = injectiveMoment H node801 := by
  calc
    injectiveMoment H raw4714 = injectiveMoment H raw4714step0 := by
      have heq : raw4714step0 = (fun i j => raw4714 (permutation18 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4714 permutation18 permutation19
    _ = injectiveMoment H node801 := by rfl

def raw4715 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, 0, 0, -1], ![1, 0, -3, 2]]

def raw4715step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem canonical4715 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4715 = injectiveMoment H node1231 := by
  calc
    injectiveMoment H raw4715 = injectiveMoment H raw4715step0 := by
      have heq : raw4715step0 = (fun i j => raw4715 (permutation18 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4715 permutation18 permutation16
    _ = injectiveMoment H node1231 := by rfl

def raw4716 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, 1, -2, 0], ![1, -1, -1, 1]]

def raw4716step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]

theorem canonical4716 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4716 = injectiveMoment H node490 := by
  calc
    injectiveMoment H raw4716 = injectiveMoment H raw4716step0 := by
      have heq : raw4716step0 = (fun i j => raw4716 (permutation18 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4716 permutation18 permutation29
    _ = injectiveMoment H node490 := by rfl

def raw4717 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

theorem canonical4717 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4717 = injectiveMoment H node2268 := by
  rfl

def raw4718 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![0, 1, 0, -1], ![2, -2, 3, -3]]

def raw4718step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, -3, 0, 3], ![1, 3, -1, -3]]

def raw4718step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, 3, 0, -3], ![-1, -3, 1, 3]]

def raw4718step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, 0, -2], ![1, -1, -3, 3]]

theorem canonical4718 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4718 = injectiveMoment H node1068 := by
  calc
    injectiveMoment H raw4718 = injectiveMoment H raw4718step0 := by
      have heq : raw4718step0 = raw4718.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4718).symm
    injectiveMoment H raw4718step0 = injectiveMoment H raw4718step1 := by
      have heq : raw4718step1 = -raw4718step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4718step0).symm
    injectiveMoment H raw4718step1 = injectiveMoment H raw4718step2 := by
      have heq : raw4718step2 = (fun i j => raw4718step1 (permutation17 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4718step1 permutation17 permutation21
    _ = injectiveMoment H node1068 := by rfl

def raw4719 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![0, 1, 1, -2], ![2, -2, 2, -2]]

def raw4719step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, -3, 1, 2], ![1, 3, -2, -2]]

def raw4719step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![1, -2, 3, -2], ![1, 1, 0, -2]]

theorem canonical4719 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4719 = injectiveMoment H node611 := by
  calc
    injectiveMoment H raw4719 = injectiveMoment H raw4719step0 := by
      have heq : raw4719step0 = raw4719.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4719).symm
    injectiveMoment H raw4719step0 = injectiveMoment H raw4719step1 := by
      have heq : raw4719step1 = (fun i j => raw4719step0 (permutation12 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4719step0 permutation12 permutation11
    _ = injectiveMoment H node611 := by rfl

def raw4720 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical4720 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4720 = injectiveMoment H node2269 := by
  rfl

def raw4721 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![0, 1, 3, -4], ![2, -2, 0, 0]]

theorem canonical4721 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4721 = injectiveMoment H node691 := by
  rfl

def raw4722 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![1, -2, 1, 0], ![1, 1, 2, -4]]

theorem canonical4722 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4722 = injectiveMoment H node692 := by
  rfl

def raw4723 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw4723step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem canonical4723 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4723 = injectiveMoment H node1356 := by
  calc
    injectiveMoment H raw4723 = injectiveMoment H raw4723step0 := by
      have heq : raw4723step0 = (fun i j => raw4723 (permutation24 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4723 permutation24 permutation15
    _ = injectiveMoment H node1356 := by rfl

def raw4724 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![1, 0, 3, -4], ![1, -1, 0, 0]]

def raw4724step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem canonical4724 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4724 = injectiveMoment H node1356 := by
  calc
    injectiveMoment H raw4724 = injectiveMoment H raw4724step0 := by
      have heq : raw4724step0 = (fun i j => raw4724 (permutation30 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4724 permutation30 permutation15
    _ = injectiveMoment H node1356 := by rfl

def raw4725 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

theorem canonical4725 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4725 = injectiveMoment H node2270 := by
  rfl

def raw4726 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, -1, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

theorem canonical4726 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4726 = injectiveMoment H node2271 := by
  rfl

def raw4727 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw4727step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![1, 0, 0, 1, -2], ![0, -2, 0, 0, 2], ![1, 2, 0, -1, -2]]

def raw4727step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, 0, -2], ![-1, 0, 0, -1, 2], ![0, 2, 0, 0, -2], ![-1, -2, 0, 1, 2]]

def raw4727step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, 2, 0, -2], ![-1, -2, 1, 2]]

def raw4727step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical4727 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4727 = injectiveMoment H node1059 := by
  calc
    injectiveMoment H raw4727 = injectiveMoment H raw4727step0 := by
      have heq : raw4727step0 = raw4727.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4727).symm
    injectiveMoment H raw4727step0 = injectiveMoment H raw4727step1 := by
      have heq : raw4727step1 = -raw4727step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4727step0).symm
    injectiveMoment H raw4727step1 = injectiveMoment H raw4727step2 := by
      have hz : ∀ i, raw4727step1 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw4727step2 = (fun i j => raw4727step1 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4727step1 permutation80 hz
    injectiveMoment H raw4727step2 = injectiveMoment H raw4727step3 := by
      have heq : raw4727step3 = (fun i j => raw4727step2 (permutation17 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4727step2 permutation17 permutation21
    _ = injectiveMoment H node1059 := by rfl

def raw4728 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

theorem canonical4728 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4728 = injectiveMoment H node2272 := by
  rfl

def raw4729 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw4729step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 2, -2], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-2, 2, -1, 1]]

def raw4729step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

theorem canonical4729 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4729 = injectiveMoment H node1840 := by
  calc
    injectiveMoment H raw4729 = injectiveMoment H raw4729step0 := by
      have heq : raw4729step0 = -raw4729 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4729).symm
    injectiveMoment H raw4729step0 = injectiveMoment H raw4729step1 := by
      have heq : raw4729step1 = (fun i j => raw4729step0 (permutation144 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4729step0 permutation144 permutation11
    _ = injectiveMoment H node1840 := by rfl

def raw4730 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 1, -1]]

theorem canonical4730 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4730 = injectiveMoment H node2273 := by
  rfl

def raw4731 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![2, -1, 0, -1]]

def raw4731step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical4731 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4731 = injectiveMoment H node1304 := by
  calc
    injectiveMoment H raw4731 = injectiveMoment H raw4731step0 := by
      have heq : raw4731step0 = (fun i j => raw4731 (permutation30 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4731 permutation30 permutation17
    _ = injectiveMoment H node1304 := by rfl

def raw4732 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

theorem canonical4732 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4732 = injectiveMoment H node2274 := by
  rfl

def raw4733 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

theorem canonical4733 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4733 = injectiveMoment H node2275 := by
  rfl

def raw4734 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![2, -2, 3, -3]]

def raw4734step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, -2, -1, 3], ![1, 2, 0, -3]]

def raw4734step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 1, -2]]

theorem canonical4734 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4734 = injectiveMoment H node794 := by
  calc
    injectiveMoment H raw4734 = injectiveMoment H raw4734step0 := by
      have heq : raw4734step0 = raw4734.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4734).symm
    injectiveMoment H raw4734step0 = injectiveMoment H raw4734step1 := by
      have heq : raw4734step1 = (fun i j => raw4734step0 (permutation22 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4734step0 permutation22 permutation23
    _ = injectiveMoment H node794 := by rfl

def raw4735 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw4735step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 2, -2], ![0, -1, 0, 1], ![-1, 2, -2, 1], ![-1, 0, 0, 1]]

def raw4735step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

theorem canonical4735 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4735 = injectiveMoment H node1839 := by
  calc
    injectiveMoment H raw4735 = injectiveMoment H raw4735step0 := by
      have heq : raw4735step0 = -raw4735 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4735).symm
    injectiveMoment H raw4735step0 = injectiveMoment H raw4735step1 := by
      have heq : raw4735step1 = (fun i j => raw4735step0 (permutation126 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4735step0 permutation126 permutation21
    _ = injectiveMoment H node1839 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6976 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def raw6976step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 1, -2], ![-3, 1, 1, 1], ![4, -1, -2, -1]]

def raw6976step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 1, -3]]

theorem canonical6976 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6976 = injectiveMoment H node453 := by
  calc
    injectiveMoment H raw6976 = injectiveMoment H raw6976step0 := by
      have heq : raw6976step0 = raw6976.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6976).symm
    injectiveMoment H raw6976step0 = injectiveMoment H raw6976step1 := by
      have heq : raw6976step1 = (fun i j => raw6976step0 (permutation27 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6976step0 permutation27 permutation24
    _ = injectiveMoment H node453 := by rfl

def raw6977 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical6977 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6977 = injectiveMoment H node2679 := by
  rfl

def raw6978 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 1, 2, -3], ![2, -2, 0, 0]]

def raw6978step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 1, -2], ![-3, 1, 2, 0], ![4, -1, -3, 0]]

def raw6978step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, 0, -2], ![0, -1, -1, 2], ![3, -1, -2, 0], ![-4, 1, 3, 0]]

def raw6978step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![0, 1, 3, -4], ![2, -1, -1, 0]]

theorem canonical6978 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6978 = injectiveMoment H node688 := by
  calc
    injectiveMoment H raw6978 = injectiveMoment H raw6978step0 := by
      have heq : raw6978step0 = raw6978.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6978).symm
    injectiveMoment H raw6978step0 = injectiveMoment H raw6978step1 := by
      have heq : raw6978step1 = -raw6978step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6978step0).symm
    injectiveMoment H raw6978step1 = injectiveMoment H raw6978step2 := by
      have heq : raw6978step2 = (fun i j => raw6978step1 (permutation12 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6978step1 permutation12 permutation30
    _ = injectiveMoment H node688 := by rfl

def raw6979 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw6979step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 3, -4], ![1, -1, -1, 1], ![-1, 1, -1, 1], ![-1, 0, -1, 2]]

def raw6979step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

theorem canonical6979 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6979 = injectiveMoment H node1341 := by
  calc
    injectiveMoment H raw6979 = injectiveMoment H raw6979step0 := by
      have heq : raw6979step0 = -raw6979 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6979).symm
    injectiveMoment H raw6979step0 = injectiveMoment H raw6979step1 := by
      have heq : raw6979step1 = (fun i j => raw6979step0 (permutation19 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6979step0 permutation19 permutation15
    _ = injectiveMoment H node1341 := by rfl

def raw6980 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![1, 0, 1, -2], ![1, -1, 1, -1]]

def raw6980step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 3, -4], ![1, -1, -1, 1], ![-1, 0, -1, 2], ![-1, 1, -1, 1]]

def raw6980step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

theorem canonical6980 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6980 = injectiveMoment H node1341 := by
  calc
    injectiveMoment H raw6980 = injectiveMoment H raw6980step0 := by
      have heq : raw6980step0 = -raw6980 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6980).symm
    injectiveMoment H raw6980step0 = injectiveMoment H raw6980step1 := by
      have heq : raw6980step1 = (fun i j => raw6980step0 (permutation17 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6980step0 permutation17 permutation15
    _ = injectiveMoment H node1341 := by rfl

def raw6981 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![1, 0, 2, -3], ![1, -1, 0, 0]]

def raw6981step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 3, -4], ![1, -1, -1, 1], ![-1, 0, -2, 3], ![-1, 1, 0, 0]]

def raw6981step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem canonical6981 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6981 = injectiveMoment H node1340 := by
  calc
    injectiveMoment H raw6981 = injectiveMoment H raw6981step0 := by
      have heq : raw6981step0 = -raw6981 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6981).symm
    injectiveMoment H raw6981step0 = injectiveMoment H raw6981step1 := by
      have heq : raw6981step1 = (fun i j => raw6981step0 (permutation17 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6981step0 permutation17 permutation15
    _ = injectiveMoment H node1340 := by rfl

def raw6982 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical6982 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6982 = injectiveMoment H node2680 := by
  rfl

def raw6983 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 2, -2], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def raw6983step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 1, -2], ![-3, 2, 1, 0], ![4, -2, -2, 0]]

def raw6983step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 0, 2, -3]]

theorem canonical6983 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6983 = injectiveMoment H node584 := by
  calc
    injectiveMoment H raw6983 = injectiveMoment H raw6983step0 := by
      have heq : raw6983step0 = raw6983.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6983).symm
    injectiveMoment H raw6983step0 = injectiveMoment H raw6983step1 := by
      have heq : raw6983step1 = (fun i j => raw6983step0 (permutation27 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6983step0 permutation27 permutation26
    _ = injectiveMoment H node584 := by rfl

def raw6984 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 2, -2], ![1, 0, 1, -2], ![1, -1, 0, 0]]

def raw6984step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, 0, -1], ![-3, 2, 1, 0], ![4, -2, -2, 0]]

def raw6984step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, -1, 0, 1], ![3, -2, -1, 0], ![-4, 2, 2, 0]]

def raw6984step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical6984 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6984 = injectiveMoment H node1095 := by
  calc
    injectiveMoment H raw6984 = injectiveMoment H raw6984step0 := by
      have heq : raw6984step0 = raw6984.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6984).symm
    injectiveMoment H raw6984step0 = injectiveMoment H raw6984step1 := by
      have heq : raw6984step1 = -raw6984step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6984step0).symm
    injectiveMoment H raw6984step1 = injectiveMoment H raw6984step2 := by
      have heq : raw6984step2 = (fun i j => raw6984step1 (permutation12 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6984step1 permutation12 permutation32
    _ = injectiveMoment H node1095 := by rfl

def raw6985 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem canonical6985 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6985 = injectiveMoment H node2681 := by
  rfl

def raw6986 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical6986 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6986 = injectiveMoment H node1164 := by
  rfl

def raw6987 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem canonical6987 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6987 = injectiveMoment H node1165 := by
  rfl

def raw6988 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 2, 0], ![1, 2, 1, -4]]

def raw6988step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![-3, 2, 1], ![4, 0, -4]]

def raw6988step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![3, -2, -1], ![-4, 0, 4]]

def raw6988step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 4, -4], ![2, -2, 0]]

theorem canonical6988 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6988 = injectiveMoment H node171 := by
  calc
    injectiveMoment H raw6988 = injectiveMoment H raw6988step0 := by
      have heq : raw6988step0 = raw6988.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6988).symm
    injectiveMoment H raw6988step0 = injectiveMoment H raw6988step1 := by
      have heq : raw6988step1 = -raw6988step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6988step0).symm
    injectiveMoment H raw6988step1 = injectiveMoment H raw6988step2 := by
      have heq : raw6988step2 = (fun i j => raw6988step1 (permutation22 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6988step1 permutation22 permutation6
    _ = injectiveMoment H node171 := by rfl

def raw6989 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 3, -1], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def raw6989step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![-3, 3, 0, 0], ![4, -1, -1, -2]]

def raw6989step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, 1, -2, 0]]

theorem canonical6989 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6989 = injectiveMoment H node780 := by
  calc
    injectiveMoment H raw6989 = injectiveMoment H raw6989step0 := by
      have heq : raw6989step0 = raw6989.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6989).symm
    injectiveMoment H raw6989step0 = injectiveMoment H raw6989step1 := by
      have heq : raw6989step1 = (fun i j => raw6989step0 (permutation31 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6989step0 permutation31 permutation26
    _ = injectiveMoment H node780 := by rfl

def raw6990 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 3, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw6990step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![-3, 3, 0, 0], ![4, -1, -2, -1]]

def raw6990step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical6990 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6990 = injectiveMoment H node781 := by
  calc
    injectiveMoment H raw6990 = injectiveMoment H raw6990step0 := by
      have heq : raw6990step0 = raw6990.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6990).symm
    injectiveMoment H raw6990step0 = injectiveMoment H raw6990step1 := by
      have heq : raw6990step1 = (fun i j => raw6990step0 (permutation32 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6990step0 permutation32 permutation32
    _ = injectiveMoment H node781 := by rfl

def raw6991 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem canonical6991 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6991 = injectiveMoment H node2684 := by
  rfl

def raw6992 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical6992 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6992 = injectiveMoment H node2685 := by
  rfl

def raw6993 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

theorem canonical6993 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6993 = injectiveMoment H node2686 := by
  rfl

def raw6994 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical6994 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6994 = injectiveMoment H node1168 := by
  rfl

def raw6995 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, -1, 2, -2]]

theorem canonical6995 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6995 = injectiveMoment H node1169 := by
  rfl

def raw6996 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

theorem canonical6996 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6996 = injectiveMoment H node2689 := by
  rfl

def raw6997 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical6997 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6997 = injectiveMoment H node1170 := by
  rfl

def raw6998 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical6998 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6998 = injectiveMoment H node1171 := by
  rfl

def raw6999 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

theorem canonical6999 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6999 = injectiveMoment H node1173 := by
  rfl

def raw7000 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def raw7000step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-3, 2, 1, 0], ![4, -1, -3, 0]]

def raw7000step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem canonical7000 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7000 = injectiveMoment H node1156 := by
  calc
    injectiveMoment H raw7000 = injectiveMoment H raw7000step0 := by
      have heq : raw7000step0 = raw7000.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7000).symm
    injectiveMoment H raw7000step0 = injectiveMoment H raw7000step1 := by
      have heq : raw7000step1 = (fun i j => raw7000step0 (permutation20 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7000step0 permutation20 permutation30
    _ = injectiveMoment H node1156 := by rfl

def raw7001 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![1, 1, 1, -3]]

def raw7001step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-3, 2, 1], ![4, -1, -3]]

def raw7001step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![3, -2, -1], ![-4, 1, 3]]

def raw7001step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical7001 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7001 = injectiveMoment H node173 := by
  calc
    injectiveMoment H raw7001 = injectiveMoment H raw7001step0 := by
      have heq : raw7001step0 = raw7001.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7001).symm
    injectiveMoment H raw7001step0 = injectiveMoment H raw7001step1 := by
      have heq : raw7001step1 = -raw7001step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7001step0).symm
    injectiveMoment H raw7001step1 = injectiveMoment H raw7001step2 := by
      have heq : raw7001step2 = (fun i j => raw7001step1 (permutation21 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7001step1 permutation21 permutation6
    _ = injectiveMoment H node173 := by rfl

def raw7002 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw7002step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![-3, 3, 0, 0], ![4, -2, -1, -1]]

def raw7002step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical7002 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7002 = injectiveMoment H node919 := by
  calc
    injectiveMoment H raw7002 = injectiveMoment H raw7002step0 := by
      have heq : raw7002step0 = raw7002.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7002).symm
    injectiveMoment H raw7002step0 = injectiveMoment H raw7002step1 := by
      have heq : raw7002step1 = (fun i j => raw7002step0 (permutation32 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7002step0 permutation32 permutation32
    _ = injectiveMoment H node919 := by rfl

def raw7003 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

theorem canonical7003 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7003 = injectiveMoment H node1175 := by
  rfl

def raw7004 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 3, -2], ![1, 1, 0, -2]]

def raw7004step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-3, 3, 0], ![4, -2, -2]]

def raw7004step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7004 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7004 = injectiveMoment H node155 := by
  calc
    injectiveMoment H raw7004 = injectiveMoment H raw7004step0 := by
      have heq : raw7004step0 = raw7004.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7004).symm
    injectiveMoment H raw7004step0 = injectiveMoment H raw7004step1 := by
      have heq : raw7004step1 = (fun i j => raw7004step0 (permutation32 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7004step0 permutation32 permutation8
    _ = injectiveMoment H node155 := by rfl

def raw7005 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw7005step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

theorem canonical7005 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7005 = injectiveMoment H node2689 := by
  calc
    injectiveMoment H raw7005 = injectiveMoment H raw7005step0 := by
      have heq : raw7005step0 = (fun i j => raw7005 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7005 permutation39 permutation9
    _ = injectiveMoment H node2689 := by rfl

def raw7006 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem canonical7006 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7006 = injectiveMoment H node2690 := by
  rfl

def raw7007 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, 1, 0]]

theorem canonical7007 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7007 = injectiveMoment H node2691 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI

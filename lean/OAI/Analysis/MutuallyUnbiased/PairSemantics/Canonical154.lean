import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes36

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]

def raw4928step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, -3, 5]]

def raw4928step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical4928 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4928 = injectiveMoment H node1436 := by
  calc
    injectiveMoment H raw4928 = injectiveMoment H raw4928step0 := by
      have heq : raw4928step0 = -raw4928 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4928).symm
    injectiveMoment H raw4928step0 = injectiveMoment H raw4928step1 := by
      have heq : raw4928step1 = (fun i j => raw4928step0 (permutation340 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4928step0 permutation340 permutation3
    _ = injectiveMoment H node1436 := by rfl

def raw4929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical4929 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4929 = injectiveMoment H node2304 := by
  rfl

def raw4930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical4930 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4930 = injectiveMoment H node2306 := by
  rfl

def raw4931 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

theorem canonical4931 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4931 = injectiveMoment H node707 := by
  rfl

def raw4932 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical4932 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4932 = injectiveMoment H node708 := by
  rfl

def raw4933 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical4933 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4933 = injectiveMoment H node709 := by
  rfl

def raw4934 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]

def raw4934step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical4934 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4934 = injectiveMoment H node227 := by
  calc
    injectiveMoment H raw4934 = injectiveMoment H raw4934step0 := by
      have hz : ∀ j, raw4934 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw4934step0 = (fun i j => raw4934 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4934 permutation80 hz
    _ = injectiveMoment H node227 := by rfl

def raw4935 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]

def raw4935step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical4935 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4935 = injectiveMoment H node230 := by
  calc
    injectiveMoment H raw4935 = injectiveMoment H raw4935step0 := by
      have hz : ∀ j, raw4935 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw4935step0 = (fun i j => raw4935 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4935 permutation80 hz
    _ = injectiveMoment H node230 := by rfl

def raw4936 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]

def raw4936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw4936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]

def raw4936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical4936 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4936 = injectiveMoment H node287 := by
  calc
    injectiveMoment H raw4936 = injectiveMoment H raw4936step0 := by
      have heq : raw4936step0 = -raw4936 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4936).symm
    injectiveMoment H raw4936step0 = injectiveMoment H raw4936step1 := by
      have hz : ∀ j, raw4936step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw4936step1 = (fun i j => raw4936step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4936step0 permutation80 hz
    injectiveMoment H raw4936step1 = injectiveMoment H raw4936step2 := by
      have heq : raw4936step2 = (fun i j => raw4936step1 (permutation12 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4936step1 permutation12 permutation6
    _ = injectiveMoment H node287 := by rfl

def raw4937 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]

def raw4937step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical4937 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4937 = injectiveMoment H node227 := by
  calc
    injectiveMoment H raw4937 = injectiveMoment H raw4937step0 := by
      have hz : ∀ j, raw4937 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw4937step0 = (fun i j => raw4937 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4937 permutation104 hz
    _ = injectiveMoment H node227 := by rfl

def raw4938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]

def raw4938step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 3, -1]]

def raw4938step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical4938 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4938 = injectiveMoment H node1880 := by
  calc
    injectiveMoment H raw4938 = injectiveMoment H raw4938step0 := by
      have heq : raw4938step0 = -raw4938 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4938).symm
    injectiveMoment H raw4938step0 = injectiveMoment H raw4938step1 := by
      have heq : raw4938step1 = (fun i j => raw4938step0 (permutation340 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4938step0 permutation340 permutation4
    _ = injectiveMoment H node1880 := by rfl

def raw4939 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def raw4939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]

def raw4939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical4939 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4939 = injectiveMoment H node655 := by
  calc
    injectiveMoment H raw4939 = injectiveMoment H raw4939step0 := by
      have heq : raw4939step0 = -raw4939 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4939).symm
    injectiveMoment H raw4939step0 = injectiveMoment H raw4939step1 := by
      have heq : raw4939step1 = (fun i j => raw4939step0 (permutation136 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4939step0 permutation136 permutation4
    _ = injectiveMoment H node655 := by rfl

def raw4940 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical4940 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4940 = injectiveMoment H node710 := by
  rfl

def raw4941 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical4941 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4941 = injectiveMoment H node711 := by
  rfl

def raw4942 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]

def raw4942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical4942 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4942 = injectiveMoment H node711 := by
  calc
    injectiveMoment H raw4942 = injectiveMoment H raw4942step0 := by
      have heq : raw4942step0 = (fun i j => raw4942 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4942 permutation34 permutation3
    _ = injectiveMoment H node711 := by rfl

def raw4943 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical4943 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4943 = injectiveMoment H node227 := by
  rfl

def raw4944 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -3, 2], ![1, 3, -4]]

theorem canonical4944 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4944 = injectiveMoment H node228 := by
  rfl

def raw4945 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical4945 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4945 = injectiveMoment H node229 := by
  rfl

def raw4946 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical4946 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4946 = injectiveMoment H node230 := by
  rfl

def raw4947 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def raw4947step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]

def raw4947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical4947 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4947 = injectiveMoment H node287 := by
  calc
    injectiveMoment H raw4947 = injectiveMoment H raw4947step0 := by
      have heq : raw4947step0 = -raw4947 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4947).symm
    injectiveMoment H raw4947step0 = injectiveMoment H raw4947step1 := by
      have heq : raw4947step1 = (fun i j => raw4947step0 (permutation12 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4947step0 permutation12 permutation6
    _ = injectiveMoment H node287 := by rfl

def raw4948 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]

def raw4948step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical4948 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4948 = injectiveMoment H node44 := by
  calc
    injectiveMoment H raw4948 = injectiveMoment H raw4948step0 := by
      have hz : ∀ j, raw4948 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw4948step0 = (fun i j => raw4948 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4948 permutation15 hz
    _ = injectiveMoment H node44 := by rfl

def raw4949 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]

def raw4949step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1]]

def raw4949step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1]]

def raw4949step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, 0, -1]]

theorem canonical4949 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4949 = injectiveMoment H node61 := by
  calc
    injectiveMoment H raw4949 = injectiveMoment H raw4949step0 := by
      have heq : raw4949step0 = -raw4949 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4949).symm
    injectiveMoment H raw4949step0 = injectiveMoment H raw4949step1 := by
      have hz : ∀ j, raw4949step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw4949step1 = (fun i j => raw4949step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4949step0 permutation15 hz
    injectiveMoment H raw4949step1 = injectiveMoment H raw4949step2 := by
      have heq : raw4949step2 = (fun i j => raw4949step1 (permutation4 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4949step1 permutation4 permutation6
    _ = injectiveMoment H node61 := by rfl

def raw4950 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![2, -1, -1]]

def raw4950step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![1, 0, -1]]

def raw4950step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

theorem canonical4950 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4950 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw4950 = injectiveMoment H raw4950step0 := by
      have heq : raw4950step0 = raw4950.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4950).symm
    injectiveMoment H raw4950step0 = injectiveMoment H raw4950step1 := by
      have hz : ∀ i, raw4950step0 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw4950step1 = (fun i j => raw4950step0 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4950step0 permutation5 hz
    _ = injectiveMoment H node11 := by rfl

def raw4951 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1]]

def raw4951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical4951 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4951 = injectiveMoment H node708 := by
  calc
    injectiveMoment H raw4951 = injectiveMoment H raw4951step0 := by
      have heq : raw4951step0 = (fun i j => raw4951 (permutation34 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4951 permutation34 permutation4
    _ = injectiveMoment H node708 := by rfl

def raw4952 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]

def raw4952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical4952 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4952 = injectiveMoment H node709 := by
  calc
    injectiveMoment H raw4952 = injectiveMoment H raw4952step0 := by
      have heq : raw4952step0 = (fun i j => raw4952 (permutation34 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4952 permutation34 permutation4
    _ = injectiveMoment H node709 := by rfl

def raw4953 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]

def raw4953step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical4953 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4953 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw4953 = injectiveMoment H raw4953step0 := by
      have heq : raw4953step0 = (fun i j => raw4953 (permutation10 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4953 permutation10 permutation4
    _ = injectiveMoment H node229 := by rfl

def raw4954 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def raw4954step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical4954 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4954 = injectiveMoment H node230 := by
  calc
    injectiveMoment H raw4954 = injectiveMoment H raw4954step0 := by
      have heq : raw4954step0 = (fun i j => raw4954 (permutation10 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4954 permutation10 permutation4
    _ = injectiveMoment H node230 := by rfl

def raw4955 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def raw4955step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]

def raw4955step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical4955 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4955 = injectiveMoment H node287 := by
  calc
    injectiveMoment H raw4955 = injectiveMoment H raw4955step0 := by
      have heq : raw4955step0 = -raw4955 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4955).symm
    injectiveMoment H raw4955step0 = injectiveMoment H raw4955step1 := by
      have heq : raw4955step1 = (fun i j => raw4955step0 (permutation12 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4955step0 permutation12 permutation8
    _ = injectiveMoment H node287 := by rfl

def raw4956 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![2, -2, 0]]

def raw4956step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-2, 2, 0]]

def raw4956step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]

theorem canonical4956 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4956 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4956 = injectiveMoment H raw4956step0 := by
      have heq : raw4956step0 = -raw4956 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4956).symm
    injectiveMoment H raw4956step0 = injectiveMoment H raw4956step1 := by
      have heq : raw4956step1 = (fun i j => raw4956step0 (permutation4 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4956step0 permutation4 permutation8
    _ = injectiveMoment H node62 := by rfl

def raw4957 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

def raw4957step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

theorem canonical4957 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4957 = injectiveMoment H node226 := by
  calc
    injectiveMoment H raw4957 = injectiveMoment H raw4957step0 := by
      have heq : raw4957step0 = (fun i j => raw4957 (permutation10 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4957 permutation10 permutation4
    _ = injectiveMoment H node226 := by rfl

def raw4958 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]

def raw4958step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical4958 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4958 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw4958 = injectiveMoment H raw4958step0 := by
      have heq : raw4958step0 = (fun i j => raw4958 (permutation19 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4958 permutation19 permutation7
    _ = injectiveMoment H node210 := by rfl

def raw4959 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 3, -3], ![1, -3, 2], ![1, -1, 0]]

def raw4959step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

theorem canonical4959 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4959 = injectiveMoment H node222 := by
  calc
    injectiveMoment H raw4959 = injectiveMoment H raw4959step0 := by
      have heq : raw4959step0 = (fun i j => raw4959 (permutation10 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4959 permutation10 permutation4
    _ = injectiveMoment H node222 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

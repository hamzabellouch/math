import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7072 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical7072 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7072 = injectiveMoment H node2702 := by
  rfl

def raw7073 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical7073 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7073 = injectiveMoment H node2703 := by
  rfl

def raw7074 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical7074 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7074 = injectiveMoment H node2704 := by
  rfl

def raw7075 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical7075 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7075 = injectiveMoment H node2705 := by
  rfl

def raw7076 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

theorem canonical7076 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7076 = injectiveMoment H node2706 := by
  rfl

def raw7077 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw7077step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical7077 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7077 = injectiveMoment H node2428 := by
  calc
    injectiveMoment H raw7077 = injectiveMoment H raw7077step0 := by
      have heq : raw7077step0 = (fun i j => raw7077 (permutation45 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7077 permutation45 permutation11
    _ = injectiveMoment H node2428 := by rfl

def raw7078 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical7078 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7078 = injectiveMoment H node1203 := by
  rfl

def raw7079 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

theorem canonical7079 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7079 = injectiveMoment H node2707 := by
  rfl

def raw7080 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical7080 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7080 = injectiveMoment H node1206 := by
  rfl

def raw7081 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw7081step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![-2, 2, 0, 0], ![3, -1, -1, -1]]

def raw7081step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical7081 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7081 = injectiveMoment H node974 := by
  calc
    injectiveMoment H raw7081 = injectiveMoment H raw7081step0 := by
      have heq : raw7081step0 = raw7081.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7081).symm
    injectiveMoment H raw7081step0 = injectiveMoment H raw7081step1 := by
      have heq : raw7081step1 = (fun i j => raw7081step0 (permutation32 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7081step0 permutation32 permutation32
    _ = injectiveMoment H node974 := by rfl

def raw7082 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical7082 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7082 = injectiveMoment H node1207 := by
  rfl

def raw7083 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

theorem canonical7083 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7083 = injectiveMoment H node1208 := by
  rfl

def raw7084 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def raw7084step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical7084 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7084 = injectiveMoment H node807 := by
  calc
    injectiveMoment H raw7084 = injectiveMoment H raw7084step0 := by
      have heq : raw7084step0 = (fun i j => raw7084 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7084 permutation11 permutation11
    _ = injectiveMoment H node807 := by rfl

def raw7085 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![1, 1, 0, -2]]

def raw7085step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-2, 2, 0], ![3, -1, -2]]

def raw7085step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7085 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7085 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw7085 = injectiveMoment H raw7085step0 := by
      have heq : raw7085step0 = raw7085.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7085).symm
    injectiveMoment H raw7085step0 = injectiveMoment H raw7085step1 := by
      have heq : raw7085step1 = (fun i j => raw7085step0 (permutation32 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7085step0 permutation32 permutation8
    _ = injectiveMoment H node185 := by rfl

def raw7086 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical7086 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7086 = injectiveMoment H node1211 := by
  rfl

def raw7087 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical7087 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7087 = injectiveMoment H node1212 := by
  rfl

def raw7088 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, 0, 0]]

theorem canonical7088 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7088 = injectiveMoment H node1214 := by
  rfl

def raw7089 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![1, 1, -1, -1]]

def raw7089step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-2, 3, -1], ![3, -2, -1]]

def raw7089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7089 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7089 = injectiveMoment H node263 := by
  calc
    injectiveMoment H raw7089 = injectiveMoment H raw7089step0 := by
      have heq : raw7089step0 = raw7089.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7089).symm
    injectiveMoment H raw7089step0 = injectiveMoment H raw7089step1 := by
      have heq : raw7089step1 = (fun i j => raw7089step0 (permutation25 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7089step0 permutation25 permutation7
    _ = injectiveMoment H node263 := by rfl

def raw7090 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 0, 0], ![1, 0, 2, -3]]

def raw7090step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![-2, 0, 2], ![3, 0, -3]]

def raw7090step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![3, 0, -3]]

def raw7090step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]

def raw7090step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical7090 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7090 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw7090 = injectiveMoment H raw7090step0 := by
      have heq : raw7090step0 = raw7090.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7090).symm
    injectiveMoment H raw7090step0 = injectiveMoment H raw7090step1 := by
      have hz : ∀ j, raw7090step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw7090step1 = (fun i j => raw7090step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7090step0 permutation15 hz
    injectiveMoment H raw7090step1 = injectiveMoment H raw7090step2 := by
      have hz : ∀ i, raw7090step1 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw7090step2 = (fun i j => raw7090step1 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7090step1 permutation5 hz
    injectiveMoment H raw7090step2 = injectiveMoment H raw7090step3 := by
      have heq : raw7090step3 = (fun i j => raw7090step2 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7090step2 permutation7 permutation2
    _ = injectiveMoment H node10 := by rfl

def raw7091 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw7091step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

theorem canonical7091 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7091 = injectiveMoment H node2707 := by
  calc
    injectiveMoment H raw7091 = injectiveMoment H raw7091step0 := by
      have heq : raw7091step0 = (fun i j => raw7091 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7091 permutation39 permutation9
    _ = injectiveMoment H node2707 := by rfl

def raw7092 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

theorem canonical7092 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7092 = injectiveMoment H node2708 := by
  rfl

def raw7093 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -2, 1, 0]]

theorem canonical7093 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7093 = injectiveMoment H node2709 := by
  rfl

def raw7094 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, 0, -1]]

def raw7094step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical7094 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7094 = injectiveMoment H node271 := by
  calc
    injectiveMoment H raw7094 = injectiveMoment H raw7094step0 := by
      have hz : ∀ i, raw7094 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7094step0 = (fun i j => raw7094 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7094 permutation15 hz
    _ = injectiveMoment H node271 := by rfl

def raw7095 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, 0, -1, 0]]

def raw7095step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical7095 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7095 = injectiveMoment H node272 := by
  calc
    injectiveMoment H raw7095 = injectiveMoment H raw7095step0 := by
      have hz : ∀ i, raw7095 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7095step0 = (fun i j => raw7095 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7095 permutation15 hz
    _ = injectiveMoment H node272 := by rfl

def raw7096 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def raw7096step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

theorem canonical7096 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7096 = injectiveMoment H node2420 := by
  calc
    injectiveMoment H raw7096 = injectiveMoment H raw7096step0 := by
      have heq : raw7096step0 = (fun i j => raw7096 (permutation41 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7096 permutation41 permutation11
    _ = injectiveMoment H node2420 := by rfl

def raw7097 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def raw7097step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-2, 1, 0, 1], ![3, -1, -1, -1]]

def raw7097step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical7097 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7097 = injectiveMoment H node969 := by
  calc
    injectiveMoment H raw7097 = injectiveMoment H raw7097step0 := by
      have heq : raw7097step0 = raw7097.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7097).symm
    injectiveMoment H raw7097step0 = injectiveMoment H raw7097step1 := by
      have heq : raw7097step1 = (fun i j => raw7097step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7097step0 permutation27 permutation18
    _ = injectiveMoment H node969 := by rfl

def raw7098 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw7098step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-2, 1, 1, 0], ![3, -1, -2, 0]]

def raw7098step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical7098 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7098 = injectiveMoment H node1202 := by
  calc
    injectiveMoment H raw7098 = injectiveMoment H raw7098step0 := by
      have heq : raw7098step0 = raw7098.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7098).symm
    injectiveMoment H raw7098step0 = injectiveMoment H raw7098step1 := by
      have heq : raw7098step1 = (fun i j => raw7098step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7098step0 permutation29 permutation20
    _ = injectiveMoment H node1202 := by rfl

def raw7099 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -2, 2, -1]]

def raw7099step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-2, 1, -1, 2], ![3, -1, -1, -1]]

def raw7099step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 2, -2]]

theorem canonical7099 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7099 = injectiveMoment H node971 := by
  calc
    injectiveMoment H raw7099 = injectiveMoment H raw7099step0 := by
      have heq : raw7099step0 = raw7099.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7099).symm
    injectiveMoment H raw7099step0 = injectiveMoment H raw7099step1 := by
      have heq : raw7099step1 = (fun i j => raw7099step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7099step0 permutation27 permutation18
    _ = injectiveMoment H node971 := by rfl

def raw7100 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, 1, 0]]

def raw7100step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![-2, 1, 0, 1], ![3, -1, -2, 0]]

def raw7100step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem canonical7100 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7100 = injectiveMoment H node802 := by
  calc
    injectiveMoment H raw7100 = injectiveMoment H raw7100step0 := by
      have heq : raw7100step0 = raw7100.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7100).symm
    injectiveMoment H raw7100step0 = injectiveMoment H raw7100step1 := by
      have heq : raw7100step1 = (fun i j => raw7100step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7100step0 permutation27 permutation18
    _ = injectiveMoment H node802 := by rfl

def raw7101 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![1, 0, 1, -2]]

def raw7101step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, 1, -2]]

theorem canonical7101 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7101 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw7101 = injectiveMoment H raw7101step0 := by
      have hz : ∀ i, raw7101 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7101step0 = (fun i j => raw7101 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7101 permutation15 hz
    _ = injectiveMoment H node56 := by rfl

def raw7102 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 0, 0, 0], ![1, 0, 0, -1]]

def raw7102step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![1, 0, 0, -1]]

def raw7102step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

theorem canonical7102 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7102 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw7102 = injectiveMoment H raw7102step0 := by
      have hz : ∀ j, raw7102 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw7102step0 = (fun i j => raw7102 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7102 permutation21 hz
    injectiveMoment H raw7102step0 = injectiveMoment H raw7102step1 := by
      have hz : ∀ i, raw7102step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7102step1 = (fun i j => raw7102step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7102step0 permutation15 hz
    _ = injectiveMoment H node57 := by rfl

def raw7103 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0]]

theorem canonical7103 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7103 = injectiveMoment H node1221 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI

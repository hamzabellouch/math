import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes51

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw9120 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, 2, -2]]

def raw9120step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

theorem canonical9120 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9120 = injectiveMoment H node3175 := by
  calc
    injectiveMoment H raw9120 = injectiveMoment H raw9120step0 := by
      have heq : raw9120step0 = (fun i j => raw9120 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9120 permutation258 permutation9
    _ = injectiveMoment H node3175 := by rfl

def raw9121 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, 1, 1], ![2, -2, 1, -1]]

def raw9121step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 1, -1]]

theorem canonical9121 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9121 = injectiveMoment H node3211 := by
  calc
    injectiveMoment H raw9121 = injectiveMoment H raw9121step0 := by
      have heq : raw9121step0 = (fun i j => raw9121 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9121 permutation258 permutation9
    _ = injectiveMoment H node3211 := by rfl

def raw9122 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 2, 1]]

def raw9122step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

theorem canonical9122 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9122 = injectiveMoment H node3073 := by
  calc
    injectiveMoment H raw9122 = injectiveMoment H raw9122step0 := by
      have heq : raw9122step0 = (fun i j => raw9122 (permutation333 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9122 permutation333 permutation10
    _ = injectiveMoment H node3073 := by rfl

def raw9123 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 1, 2], ![1, 1, 1, -3]]

def raw9123step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem canonical9123 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9123 = injectiveMoment H node3047 := by
  calc
    injectiveMoment H raw9123 = injectiveMoment H raw9123step0 := by
      have heq : raw9123step0 = (fun i j => raw9123 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9123 permutation258 permutation9
    _ = injectiveMoment H node3047 := by rfl

def raw9124 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, 2, 1]]

def raw9124step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical9124 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9124 = injectiveMoment H node3074 := by
  calc
    injectiveMoment H raw9124 = injectiveMoment H raw9124step0 := by
      have heq : raw9124step0 = (fun i j => raw9124 (permutation331 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9124 permutation331 permutation10
    _ = injectiveMoment H node3074 := by rfl

def raw9125 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, -1, 1, 0]]

def raw9125step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![-1, 1, 0]]

def raw9125step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical9125 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9125 = injectiveMoment H node294 := by
  calc
    injectiveMoment H raw9125 = injectiveMoment H raw9125step0 := by
      have hz : ∀ i, raw9125 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9125step0 = (fun i j => raw9125 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9125 permutation9 hz
    injectiveMoment H raw9125step0 = injectiveMoment H raw9125step1 := by
      have heq : raw9125step1 = (fun i j => raw9125step0 (permutation29 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9125step0 permutation29 permutation4
    _ = injectiveMoment H node294 := by rfl

def raw9126 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def raw9126step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 1, -2]]

theorem canonical9126 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9126 = injectiveMoment H node2981 := by
  calc
    injectiveMoment H raw9126 = injectiveMoment H raw9126step0 := by
      have heq : raw9126step0 = (fun i j => raw9126 (permutation258 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9126 permutation258 permutation9
    _ = injectiveMoment H node2981 := by rfl

def raw9127 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, 1, -1]]

def raw9127step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![2, 0, 0, -2], ![-2, 2, -1, 1]]

def raw9127step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 0, -2]]

theorem canonical9127 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9127 = injectiveMoment H node3089 := by
  calc
    injectiveMoment H raw9127 = injectiveMoment H raw9127step0 := by
      have heq : raw9127step0 = -raw9127 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9127).symm
    injectiveMoment H raw9127step0 = injectiveMoment H raw9127step1 := by
      have heq : raw9127step1 = (fun i j => raw9127step0 (permutation339 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9127step0 permutation339 permutation11
    _ = injectiveMoment H node3089 := by rfl

def raw9128 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 1, 1], ![2, -2, 0, 0]]

def raw9128step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

theorem canonical9128 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9128 = injectiveMoment H node3156 := by
  calc
    injectiveMoment H raw9128 = injectiveMoment H raw9128step0 := by
      have heq : raw9128step0 = (fun i j => raw9128 (permutation199 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9128 permutation199 permutation23
    _ = injectiveMoment H node3156 := by rfl

def raw9129 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 2, 0], ![2, -2, -1, 1]]

def raw9129step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 1, -1]]

theorem canonical9129 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9129 = injectiveMoment H node3182 := by
  calc
    injectiveMoment H raw9129 = injectiveMoment H raw9129step0 := by
      have heq : raw9129step0 = (fun i j => raw9129 (permutation277 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9129 permutation277 permutation10
    _ = injectiveMoment H node3182 := by rfl

def raw9130 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 2, 1]]

def raw9130step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

theorem canonical9130 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9130 = injectiveMoment H node3072 := by
  calc
    injectiveMoment H raw9130 = injectiveMoment H raw9130step0 := by
      have heq : raw9130step0 = (fun i j => raw9130 (permutation331 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9130 permutation331 permutation10
    _ = injectiveMoment H node3072 := by rfl

def raw9131 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 1, 2]]

def raw9131step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

theorem canonical9131 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9131 = injectiveMoment H node3048 := by
  calc
    injectiveMoment H raw9131 = injectiveMoment H raw9131step0 := by
      have heq : raw9131step0 = (fun i j => raw9131 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9131 permutation308 permutation9
    _ = injectiveMoment H node3048 := by rfl

def raw9132 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1], ![-2, -2, 2, 2]]

def raw9132step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical9132 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9132 = injectiveMoment H node2890 := by
  calc
    injectiveMoment H raw9132 = injectiveMoment H raw9132step0 := by
      have heq : raw9132step0 = (fun i j => raw9132 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9132 permutation308 permutation9
    _ = injectiveMoment H node2890 := by rfl

def raw9133 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-2, -2, 1, 3]]

def raw9133step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

theorem canonical9133 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9133 = injectiveMoment H node2882 := by
  calc
    injectiveMoment H raw9133 = injectiveMoment H raw9133step0 := by
      have heq : raw9133step0 = (fun i j => raw9133 (permutation308 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9133 permutation308 permutation9
    _ = injectiveMoment H node2882 := by rfl

def raw9134 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![1, -1, 1, -1]]

def raw9134step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical9134 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9134 = injectiveMoment H node3152 := by
  calc
    injectiveMoment H raw9134 = injectiveMoment H raw9134step0 := by
      have heq : raw9134step0 = (fun i j => raw9134 (permutation188 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9134 permutation188 permutation21
    _ = injectiveMoment H node3152 := by rfl

def raw9135 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 1, 0]]

def raw9135step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem canonical9135 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9135 = injectiveMoment H node3170 := by
  calc
    injectiveMoment H raw9135 = injectiveMoment H raw9135step0 := by
      have heq : raw9135step0 = (fun i j => raw9135 (permutation179 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9135 permutation179 permutation23
    _ = injectiveMoment H node3170 := by rfl

def raw9136 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, -2, 2, -1]]

def raw9136step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

theorem canonical9136 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9136 = injectiveMoment H node3262 := by
  calc
    injectiveMoment H raw9136 = injectiveMoment H raw9136step0 := by
      have heq : raw9136step0 = (fun i j => raw9136 (permutation334 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9136 permutation334 permutation16
    _ = injectiveMoment H node3262 := by rfl

def raw9137 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, -1, 2], ![1, -2, 2, -1]]

def raw9137step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

theorem canonical9137 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9137 = injectiveMoment H node3253 := by
  calc
    injectiveMoment H raw9137 = injectiveMoment H raw9137step0 := by
      have heq : raw9137step0 = (fun i j => raw9137 (permutation259 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9137 permutation259 permutation9
    _ = injectiveMoment H node3253 := by rfl

def raw9138 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![1, -2, 1, 0]]

def raw9138step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem canonical9138 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9138 = injectiveMoment H node3153 := by
  calc
    injectiveMoment H raw9138 = injectiveMoment H raw9138step0 := by
      have heq : raw9138step0 = (fun i j => raw9138 (permutation188 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9138 permutation188 permutation21
    _ = injectiveMoment H node3153 := by rfl

def raw9139 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 2, 1, -3]]

def raw9139step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![2, 0, 0, -2], ![0, -2, -1, 3]]

def raw9139step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

theorem canonical9139 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9139 = injectiveMoment H node2952 := by
  calc
    injectiveMoment H raw9139 = injectiveMoment H raw9139step0 := by
      have heq : raw9139step0 = -raw9139 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9139).symm
    injectiveMoment H raw9139step0 = injectiveMoment H raw9139step1 := by
      have heq : raw9139step1 = (fun i j => raw9139step0 (permutation349 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9139step0 permutation349 permutation17
    _ = injectiveMoment H node2952 := by rfl

def raw9140 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, -1, 2], ![-1, 2, 2, -3]]

def raw9140step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 1, 0, 0], ![1, 0, 1, -2], ![1, -2, -2, 3]]

def raw9140step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9140 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9140 = injectiveMoment H node3238 := by
  calc
    injectiveMoment H raw9140 = injectiveMoment H raw9140step0 := by
      have heq : raw9140step0 = -raw9140 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9140).symm
    injectiveMoment H raw9140step0 = injectiveMoment H raw9140step1 := by
      have heq : raw9140step1 = (fun i j => raw9140step0 (permutation335 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9140step0 permutation335 permutation15
    _ = injectiveMoment H node3238 := by rfl

def raw9141 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 1, 2], ![0, 2, 1, -3]]

def raw9141step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical9141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9141 = injectiveMoment H node3050 := by
  calc
    injectiveMoment H raw9141 = injectiveMoment H raw9141step0 := by
      have heq : raw9141step0 = (fun i j => raw9141 (permutation262 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9141 permutation262 permutation9
    _ = injectiveMoment H node3050 := by rfl

def raw9142 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![-1, 2, 2, -3]]

def raw9142step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, 0, -2], ![1, -2, -2, 3]]

def raw9142step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

theorem canonical9142 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9142 = injectiveMoment H node3228 := by
  calc
    injectiveMoment H raw9142 = injectiveMoment H raw9142step0 := by
      have heq : raw9142step0 = -raw9142 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9142).symm
    injectiveMoment H raw9142step0 = injectiveMoment H raw9142step1 := by
      have heq : raw9142step1 = (fun i j => raw9142step0 (permutation377 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9142step0 permutation377 permutation15
    _ = injectiveMoment H node3228 := by rfl

def raw9143 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 1, 1], ![-1, 2, 1, -2]]

def raw9143step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0], ![1, 1, -1, -1], ![1, -2, -1, 2]]

def raw9143step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical9143 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9143 = injectiveMoment H node3248 := by
  calc
    injectiveMoment H raw9143 = injectiveMoment H raw9143step0 := by
      have heq : raw9143step0 = -raw9143 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9143).symm
    injectiveMoment H raw9143step0 = injectiveMoment H raw9143step1 := by
      have heq : raw9143step1 = (fun i j => raw9143step0 (permutation377 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9143step0 permutation377 permutation15
    _ = injectiveMoment H node3248 := by rfl

def raw9144 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, 2, 1]]

def raw9144step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical9144 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9144 = injectiveMoment H node3075 := by
  calc
    injectiveMoment H raw9144 = injectiveMoment H raw9144step0 := by
      have heq : raw9144step0 = (fun i j => raw9144 (permutation335 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9144 permutation335 permutation10
    _ = injectiveMoment H node3075 := by rfl

def raw9145 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 2, 1, -2]]

def raw9145step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 1, 0, -2], ![1, -2, -1, 2]]

def raw9145step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem canonical9145 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9145 = injectiveMoment H node3028 := by
  calc
    injectiveMoment H raw9145 = injectiveMoment H raw9145step0 := by
      have heq : raw9145step0 = -raw9145 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9145).symm
    injectiveMoment H raw9145step0 = injectiveMoment H raw9145step1 := by
      have heq : raw9145step1 = (fun i j => raw9145step0 (permutation343 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9145step0 permutation343 permutation17
    _ = injectiveMoment H node3028 := by rfl

def raw9146 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 2, 2, -2]]

def raw9146step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, 2, -2], ![0, 0, -1, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![0, 1, 1, -2], ![2, -2, -2, 2]]

def raw9146step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical9146 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw9146 = injectiveMoment H node3309 := by
  calc
    injectiveMoment H raw9146 = injectiveMoment H raw9146step0 := by
      have heq : raw9146step0 = -raw9146 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw9146).symm
    injectiveMoment H raw9146step0 = injectiveMoment H raw9146step1 := by
      have heq : raw9146step1 = (fun i j => raw9146step0 (permutation377 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9146step0 permutation377 permutation15
    _ = injectiveMoment H node3309 := by rfl

def raw9147 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, 1, 2]]

def raw9147step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical9147 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9147 = injectiveMoment H node3049 := by
  calc
    injectiveMoment H raw9147 = injectiveMoment H raw9147step0 := by
      have heq : raw9147step0 = (fun i j => raw9147 (permutation312 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9147 permutation312 permutation9
    _ = injectiveMoment H node3049 := by rfl

def raw9148 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 2, -2], ![0, 0, 0, 0]]

def raw9148step0 : Matrix (Fin 2) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 2, -2]]

def raw9148step1 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, -2, 2], ![0, 2, -2]]

def raw9148step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]

theorem canonical9148 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9148 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw9148 = injectiveMoment H raw9148step0 := by
      have hz : ∀ j, raw9148 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw9148step0 = (fun i j => raw9148 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9148 permutation7 hz
    injectiveMoment H raw9148step0 = injectiveMoment H raw9148step1 := by
      have hz : ∀ i, raw9148step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw9148step1 = (fun i j => raw9148step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9148step0 permutation15 hz
    injectiveMoment H raw9148step1 = injectiveMoment H raw9148step2 := by
      have hz : ∀ i, raw9148step1 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw9148step2 = (fun i j => raw9148step1 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9148step1 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

def raw9149 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 3, -3], ![-1, 2, 0, -1], ![1, -2, -1, 2]]

def raw9149step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 0, -1], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -2, -1, 2]]

theorem canonical9149 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9149 = injectiveMoment H node1376 := by
  calc
    injectiveMoment H raw9149 = injectiveMoment H raw9149step0 := by
      have heq : raw9149step0 = (fun i j => raw9149 (permutation21 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9149 permutation21 permutation9
    _ = injectiveMoment H node1376 := by rfl

def raw9150 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![0, -1, -1, 2]]

def raw9150step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![-1, -1, 2]]

def raw9150step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

theorem canonical9150 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9150 = injectiveMoment H node280 := by
  calc
    injectiveMoment H raw9150 = injectiveMoment H raw9150step0 := by
      have hz : ∀ i, raw9150 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw9150step0 = (fun i j => raw9150 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw9150 permutation9 hz
    injectiveMoment H raw9150step0 = injectiveMoment H raw9150step1 := by
      have heq : raw9150step1 = (fun i j => raw9150step0 (permutation27 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9150step0 permutation27 permutation3
    _ = injectiveMoment H node280 := by rfl

def raw9151 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def raw9151step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical9151 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9151 = injectiveMoment H node3177 := by
  calc
    injectiveMoment H raw9151 = injectiveMoment H raw9151step0 := by
      have heq : raw9151step0 = (fun i j => raw9151 (permutation262 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9151 permutation262 permutation9
    _ = injectiveMoment H node3177 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

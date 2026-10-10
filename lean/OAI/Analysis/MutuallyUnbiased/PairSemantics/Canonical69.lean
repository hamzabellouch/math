import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw2208 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

theorem canonical2208 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2208 = injectiveMoment H node1754 := by
  rfl

def raw2209 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, 1, -3]]

theorem canonical2209 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2209 = injectiveMoment H node1755 := by
  rfl

def raw2210 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def raw2210step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical2210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2210 = injectiveMoment H node833 := by
  calc
    injectiveMoment H raw2210 = injectiveMoment H raw2210step0 := by
      have heq : raw2210step0 = (fun i j => raw2210 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2210 permutation10 permutation15
    _ = injectiveMoment H node833 := by rfl

def raw2211 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 1, -2]]

theorem canonical2211 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2211 = injectiveMoment H node1756 := by
  rfl

def raw2212 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

theorem canonical2212 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2212 = injectiveMoment H node1757 := by
  rfl

def raw2213 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem canonical2213 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2213 = injectiveMoment H node1758 := by
  rfl

def raw2214 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

theorem canonical2214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2214 = injectiveMoment H node1759 := by
  rfl

def raw2215 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 0, 0, -1]]

def raw2215step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical2215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2215 = injectiveMoment H node2432 := by
  calc
    injectiveMoment H raw2215 = injectiveMoment H raw2215step0 := by
      have heq : raw2215step0 = (fun i j => raw2215 (permutation38 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2215 permutation38 permutation15
    _ = injectiveMoment H node2432 := by rfl

def raw2216 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, 0, 1, -3]]

def raw2216step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 0, -1]]

theorem canonical2216 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2216 = injectiveMoment H node832 := by
  calc
    injectiveMoment H raw2216 = injectiveMoment H raw2216step0 := by
      have heq : raw2216step0 = (fun i j => raw2216 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2216 permutation10 permutation15
    _ = injectiveMoment H node832 := by rfl

def raw2217 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def raw2217step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

theorem canonical2217 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2217 = injectiveMoment H node1757 := by
  calc
    injectiveMoment H raw2217 = injectiveMoment H raw2217step0 := by
      have heq : raw2217step0 = (fun i j => raw2217 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2217 permutation35 permutation9
    _ = injectiveMoment H node1757 := by rfl

def raw2218 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw2218step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical2218 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2218 = injectiveMoment H node831 := by
  calc
    injectiveMoment H raw2218 = injectiveMoment H raw2218step0 := by
      have heq : raw2218step0 = (fun i j => raw2218 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2218 permutation10 permutation15
    _ = injectiveMoment H node831 := by rfl

def raw2219 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical2219 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2219 = injectiveMoment H node1760 := by
  rfl

def raw2220 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical2220 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2220 = injectiveMoment H node1761 := by
  rfl

def raw2221 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -1, 1, -2]]

theorem canonical2221 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2221 = injectiveMoment H node506 := by
  rfl

def raw2222 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw2222step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 0, 2, -2], ![0, -2, -1, 3], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw2222step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -1, 0]]

theorem canonical2222 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2222 = injectiveMoment H node1670 := by
  calc
    injectiveMoment H raw2222 = injectiveMoment H raw2222step0 := by
      have heq : raw2222step0 = -raw2222 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2222).symm
    injectiveMoment H raw2222step0 = injectiveMoment H raw2222step1 := by
      have heq : raw2222step1 = (fun i j => raw2222step0 (permutation100 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2222step0 permutation100 permutation17
    _ = injectiveMoment H node1670 := by rfl

def raw2223 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical2223 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2223 = injectiveMoment H node1762 := by
  rfl

def raw2224 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![2, -1, 0, -1]]

def raw2224step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 0, 2, -2], ![0, -2, -1, 3], ![-2, 1, 0, 1]]

def raw2224step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -2, 1]]

theorem canonical2224 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2224 = injectiveMoment H node496 := by
  calc
    injectiveMoment H raw2224 = injectiveMoment H raw2224step0 := by
      have heq : raw2224step0 = -raw2224 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2224).symm
    injectiveMoment H raw2224step0 = injectiveMoment H raw2224step1 := by
      have heq : raw2224step1 = (fun i j => raw2224step0 (permutation23 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2224step0 permutation23 permutation17
    _ = injectiveMoment H node496 := by rfl

def raw2225 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical2225 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2225 = injectiveMoment H node1763 := by
  rfl

def raw2226 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![2, -1, -1, 0]]

def raw2226step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![1, -2, 2, -1], ![2, 2, -4, 0]]

def raw2226step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![2, 0, 2, -4]]

theorem canonical2226 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2226 = injectiveMoment H node498 := by
  calc
    injectiveMoment H raw2226 = injectiveMoment H raw2226step0 := by
      have heq : raw2226step0 = raw2226.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2226).symm
    injectiveMoment H raw2226step0 = injectiveMoment H raw2226step1 := by
      have heq : raw2226step1 = (fun i j => raw2226step0 (permutation23 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2226step0 permutation23 permutation19
    _ = injectiveMoment H node498 := by rfl

def raw2227 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 2, 1, -4]]

def raw2227step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![1, -2, 0, 1], ![2, 2, 0, -4]]

def raw2227step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical2227 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2227 = injectiveMoment H node1234 := by
  calc
    injectiveMoment H raw2227 = injectiveMoment H raw2227step0 := by
      have heq : raw2227step0 = raw2227.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2227).symm
    injectiveMoment H raw2227step0 = injectiveMoment H raw2227step1 := by
      have heq : raw2227step1 = (fun i j => raw2227step0 (permutation18 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2227step0 permutation18 permutation23
    _ = injectiveMoment H node1234 := by rfl

def raw2228 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![1, -1, 1, -1], ![1, 2, 0, -3]]

def raw2228step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 0, 2, -2], ![-1, 1, -1, 1], ![-1, -2, 0, 3]]

def raw2228step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, -1, -2]]

theorem canonical2228 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2228 = injectiveMoment H node483 := by
  calc
    injectiveMoment H raw2228 = injectiveMoment H raw2228step0 := by
      have heq : raw2228step0 = -raw2228 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2228).symm
    injectiveMoment H raw2228step0 = injectiveMoment H raw2228step1 := by
      have heq : raw2228step1 = (fun i j => raw2228step0 (permutation30 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2228step0 permutation30 permutation15
    _ = injectiveMoment H node483 := by rfl

def raw2229 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw2229step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 1, 2, -4]]

theorem canonical2229 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2229 = injectiveMoment H node826 := by
  calc
    injectiveMoment H raw2229 = injectiveMoment H raw2229step0 := by
      have heq : raw2229step0 = (fun i j => raw2229 (permutation9 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2229 permutation9 permutation15
    _ = injectiveMoment H node826 := by rfl

def raw2230 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def raw2230step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 1, 1, -3]]

theorem canonical2230 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2230 = injectiveMoment H node827 := by
  calc
    injectiveMoment H raw2230 = injectiveMoment H raw2230step0 := by
      have heq : raw2230step0 = (fun i j => raw2230 (permutation9 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2230 permutation9 permutation15
    _ = injectiveMoment H node827 := by rfl

def raw2231 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def raw2231step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 1, 0, -2]]

theorem canonical2231 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2231 = injectiveMoment H node828 := by
  calc
    injectiveMoment H raw2231 = injectiveMoment H raw2231step0 := by
      have heq : raw2231step0 = (fun i j => raw2231 (permutation9 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2231 permutation9 permutation15
    _ = injectiveMoment H node828 := by rfl

def raw2232 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![1, 1, 0, -2], ![1, 0, 1, -2]]

def raw2232step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 1, 0, -2]]

theorem canonical2232 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2232 = injectiveMoment H node828 := by
  calc
    injectiveMoment H raw2232 = injectiveMoment H raw2232step0 := by
      have heq : raw2232step0 = (fun i j => raw2232 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2232 permutation10 permutation15
    _ = injectiveMoment H node828 := by rfl

def raw2233 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![1, 1, 2, -4], ![1, 0, -1, 0]]

def raw2233step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 1, 2, -4]]

theorem canonical2233 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2233 = injectiveMoment H node826 := by
  calc
    injectiveMoment H raw2233 = injectiveMoment H raw2233step0 := by
      have heq : raw2233step0 = (fun i j => raw2233 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2233 permutation10 permutation15
    _ = injectiveMoment H node826 := by rfl

def raw2234 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![1, 2, 0, -3], ![1, -1, 1, -1]]

def raw2234step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 0, 2, -2], ![-1, -2, 0, 3], ![-1, 1, -1, 1]]

def raw2234step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, -1, -2]]

theorem canonical2234 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2234 = injectiveMoment H node483 := by
  calc
    injectiveMoment H raw2234 = injectiveMoment H raw2234step0 := by
      have heq : raw2234step0 = -raw2234 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2234).symm
    injectiveMoment H raw2234step0 = injectiveMoment H raw2234step1 := by
      have heq : raw2234step1 = (fun i j => raw2234step0 (permutation24 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2234step0 permutation24 permutation15
    _ = injectiveMoment H node483 := by rfl

def raw2235 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, -1, 0, 1], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def raw2235step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical2235 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2235 = injectiveMoment H node2762 := by
  calc
    injectiveMoment H raw2235 = injectiveMoment H raw2235step0 := by
      have heq : raw2235step0 = (fun i j => raw2235 (permutation67 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2235 permutation67 permutation23
    _ = injectiveMoment H node2762 := by rfl

def raw2236 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def raw2236step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical2236 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2236 = injectiveMoment H node2437 := by
  calc
    injectiveMoment H raw2236 = injectiveMoment H raw2236step0 := by
      have heq : raw2236step0 = (fun i j => raw2236 (permutation34 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2236 permutation34 permutation15
    _ = injectiveMoment H node2437 := by rfl

def raw2237 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw2237step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical2237 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2237 = injectiveMoment H node2435 := by
  calc
    injectiveMoment H raw2237 = injectiveMoment H raw2237step0 := by
      have heq : raw2237step0 = (fun i j => raw2237 (permutation34 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2237 permutation34 permutation15
    _ = injectiveMoment H node2435 := by rfl

def raw2238 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, -1, 1, -2]]

def raw2238step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, -1, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -2, 0, 2], ![-2, 1, -1, 2]]

def raw2238step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 1, -2]]

theorem canonical2238 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw2238 = injectiveMoment H node1756 := by
  calc
    injectiveMoment H raw2238 = injectiveMoment H raw2238step0 := by
      have heq : raw2238step0 = -raw2238 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw2238).symm
    injectiveMoment H raw2238step0 = injectiveMoment H raw2238step1 := by
      have heq : raw2238step1 = (fun i j => raw2238step0 (permutation148 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2238step0 permutation148 permutation11
    _ = injectiveMoment H node1756 := by rfl

def raw2239 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw2239step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 1, 2, -4]]

theorem canonical2239 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2239 = injectiveMoment H node2433 := by
  calc
    injectiveMoment H raw2239 = injectiveMoment H raw2239step0 := by
      have heq : raw2239step0 = (fun i j => raw2239 (permutation33 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2239 permutation33 permutation15
    _ = injectiveMoment H node2433 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

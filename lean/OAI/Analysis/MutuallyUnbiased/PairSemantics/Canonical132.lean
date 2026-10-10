import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4224 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 0, -3, 3], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4224step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -3, 1], ![0, 0, 3, -3], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw4224step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 3, -3], ![0, 2, -3, 1], ![1, -1, 0, 0]]

theorem canonical4224 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4224 = injectiveMoment H node2763 := by
  calc
    injectiveMoment H raw4224 = injectiveMoment H raw4224step0 := by
      have heq : raw4224step0 = -raw4224 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4224).symm
    injectiveMoment H raw4224step0 = injectiveMoment H raw4224step1 := by
      have heq : raw4224step1 = (fun i j => raw4224step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4224step0 permutation100 permutation15
    _ = injectiveMoment H node2763 := by rfl

def raw4225 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 0, -3, 3], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4225step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -3, 1], ![0, 0, 3, -3], ![-1, 1, 0, 0], ![-1, -1, 0, 2]]

def raw4225step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -3, 1], ![1, -1, 0, 0]]

theorem canonical4225 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4225 = injectiveMoment H node1065 := by
  calc
    injectiveMoment H raw4225 = injectiveMoment H raw4225step0 := by
      have heq : raw4225step0 = -raw4225 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4225).symm
    injectiveMoment H raw4225step0 = injectiveMoment H raw4225step1 := by
      have heq : raw4225step1 = (fun i j => raw4225step0 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4225step0 permutation29 permutation15
    _ = injectiveMoment H node1065 := by rfl

def raw4226 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, -1, 2], ![1, 1, 0, -2]]

theorem canonical4226 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4226 = injectiveMoment H node2146 := by
  rfl

def raw4227 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw4227step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -3, 1], ![0, 0, 2, -2], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw4227step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

theorem canonical4227 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4227 = injectiveMoment H node2760 := by
  calc
    injectiveMoment H raw4227 = injectiveMoment H raw4227step0 := by
      have heq : raw4227step0 = -raw4227 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4227).symm
    injectiveMoment H raw4227step0 = injectiveMoment H raw4227step1 := by
      have heq : raw4227step1 = (fun i j => raw4227step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4227step0 permutation100 permutation15
    _ = injectiveMoment H node2760 := by rfl

def raw4228 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, -1, 2], ![1, 0, 0, -1]]

def raw4228step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, -3, 1], ![0, 0, 2, -2], ![0, -2, 0, 2], ![-1, 2, 1, -2], ![-1, 0, 0, 1]]

def raw4228step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, -3, 1], ![2, -1, 1, -2]]

theorem canonical4228 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4228 = injectiveMoment H node2008 := by
  calc
    injectiveMoment H raw4228 = injectiveMoment H raw4228step0 := by
      have heq : raw4228step0 = -raw4228 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4228).symm
    injectiveMoment H raw4228step0 = injectiveMoment H raw4228step1 := by
      have heq : raw4228step1 = (fun i j => raw4228step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4228step0 permutation100 permutation15
    _ = injectiveMoment H node2008 := by rfl

def raw4229 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 0, -2, 2], ![1, -2, -1, 2], ![1, 2, 0, -3]]

def raw4229step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -3, 1], ![0, 0, 2, -2], ![-1, 2, 1, -2], ![-1, -2, 0, 3]]

def raw4229step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -3, 1], ![2, -1, 1, -2]]

theorem canonical4229 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4229 = injectiveMoment H node480 := by
  calc
    injectiveMoment H raw4229 = injectiveMoment H raw4229step0 := by
      have heq : raw4229step0 = -raw4229 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4229).symm
    injectiveMoment H raw4229step0 = injectiveMoment H raw4229step1 := by
      have heq : raw4229step1 = (fun i j => raw4229step0 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4229step0 permutation29 permutation15
    _ = injectiveMoment H node480 := by rfl

def raw4230 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 0, -2, 2], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def raw4230step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -3, 1], ![0, 0, 2, -2], ![-1, 1, 1, -1], ![-1, -1, 0, 2]]

def raw4230step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

theorem canonical4230 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4230 = injectiveMoment H node1056 := by
  calc
    injectiveMoment H raw4230 = injectiveMoment H raw4230step0 := by
      have heq : raw4230step0 = -raw4230 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4230).symm
    injectiveMoment H raw4230step0 = injectiveMoment H raw4230step1 := by
      have heq : raw4230step1 = (fun i j => raw4230step0 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4230step0 permutation29 permutation15
    _ = injectiveMoment H node1056 := by rfl

def raw4231 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, -1, 2], ![1, 0, 0, -1]]

def raw4231step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

theorem canonical4231 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4231 = injectiveMoment H node1982 := by
  calc
    injectiveMoment H raw4231 = injectiveMoment H raw4231step0 := by
      have heq : raw4231step0 = (fun i j => raw4231 (permutation39 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4231 permutation39 permutation10
    _ = injectiveMoment H node1982 := by rfl

def raw4232 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 1, -2, 1], ![1, -2, -1, 2], ![1, 1, 0, -2]]

def raw4232step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 1, -2, 0]]

theorem canonical4232 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4232 = injectiveMoment H node598 := by
  calc
    injectiveMoment H raw4232 = injectiveMoment H raw4232step0 := by
      have heq : raw4232step0 = (fun i j => raw4232 (permutation9 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4232 permutation9 permutation10
    _ = injectiveMoment H node598 := by rfl

def raw4233 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, -2, 3], ![1, 0, 0, -1]]

def raw4233step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

theorem canonical4233 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4233 = injectiveMoment H node1980 := by
  calc
    injectiveMoment H raw4233 = injectiveMoment H raw4233step0 := by
      have heq : raw4233step0 = (fun i j => raw4233 (permutation39 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4233 permutation39 permutation10
    _ = injectiveMoment H node1980 := by rfl

def raw4234 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, -2, -2, 3], ![1, 0, 0, -1]]

def raw4234step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

theorem canonical4234 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4234 = injectiveMoment H node1980 := by
  calc
    injectiveMoment H raw4234 = injectiveMoment H raw4234step0 := by
      have heq : raw4234step0 = (fun i j => raw4234 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4234 permutation33 permutation10
    _ = injectiveMoment H node1980 := by rfl

def raw4235 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -3, 4], ![1, 0, 0, -1]]

theorem canonical4235 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4235 = injectiveMoment H node2147 := by
  rfl

def raw4236 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3], ![1, 0, -1, 0]]

def raw4236step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, 0, -1]]

theorem canonical4236 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4236 = injectiveMoment H node1977 := by
  calc
    injectiveMoment H raw4236 = injectiveMoment H raw4236step0 := by
      have heq : raw4236step0 = (fun i j => raw4236 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4236 permutation33 permutation10
    _ = injectiveMoment H node1977 := by rfl

def raw4237 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 1, 0, -1], ![1, -2, -3, 4], ![1, 1, 0, -2]]

def raw4237step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![3, 0, -3, 0], ![-1, -1, 4, -2]]

def raw4237step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem canonical4237 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4237 = injectiveMoment H node778 := by
  calc
    injectiveMoment H raw4237 = injectiveMoment H raw4237step0 := by
      have heq : raw4237step0 = raw4237.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4237).symm
    injectiveMoment H raw4237step0 = injectiveMoment H raw4237step1 := by
      have heq : raw4237step1 = (fun i j => raw4237step0 (permutation31 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4237step0 permutation31 permutation19
    _ = injectiveMoment H node778 := by rfl

def raw4238 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 1, 0, -1], ![1, -1, -3, 3], ![1, 0, 0, -1]]

def raw4238step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![3, 0, -3, 0], ![-1, -1, 3, -1]]

def raw4238step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem canonical4238 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4238 = injectiveMoment H node977 := by
  calc
    injectiveMoment H raw4238 = injectiveMoment H raw4238step0 := by
      have heq : raw4238step0 = raw4238.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4238).symm
    injectiveMoment H raw4238step0 = injectiveMoment H raw4238step1 := by
      have heq : raw4238step1 = (fun i j => raw4238step0 (permutation31 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4238step0 permutation31 permutation19
    _ = injectiveMoment H node977 := by rfl

def raw4239 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 2, 0, -2], ![1, -2, -3, 4], ![1, 0, 0, -1]]

def raw4239step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![3, 0, -3, 0], ![-1, -2, 4, -1]]

def raw4239step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 3, -3], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical4239 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4239 = injectiveMoment H node783 := by
  calc
    injectiveMoment H raw4239 = injectiveMoment H raw4239step0 := by
      have heq : raw4239step0 = raw4239.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4239).symm
    injectiveMoment H raw4239step0 = injectiveMoment H raw4239step1 := by
      have heq : raw4239step1 = (fun i j => raw4239step0 (permutation32 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4239step0 permutation32 permutation29
    _ = injectiveMoment H node783 := by rfl

def raw4240 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![1, -3, 1, 1], ![1, 3, -4, 0]]

def raw4240step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![3, 1, -4], ![-1, 1, 0]]

def raw4240step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 3, -3], ![-3, -1, 4], ![1, -1, 0]]

def raw4240step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]

theorem canonical4240 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4240 = injectiveMoment H node87 := by
  calc
    injectiveMoment H raw4240 = injectiveMoment H raw4240step0 := by
      have heq : raw4240step0 = raw4240.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4240).symm
    injectiveMoment H raw4240step0 = injectiveMoment H raw4240step1 := by
      have heq : raw4240step1 = -raw4240step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4240step0).symm
    injectiveMoment H raw4240step1 = injectiveMoment H raw4240step2 := by
      have heq : raw4240step2 = (fun i j => raw4240step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4240step1 permutation24 permutation3
    _ = injectiveMoment H node87 := by rfl

def raw4241 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![2, -3, 1, 0], ![0, 3, -4, 1]]

def raw4241step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -3, 3], ![3, 1, -4], ![-1, 0, 1]]

def raw4241step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![0, 3, -3], ![-3, -1, 4], ![1, 0, -1]]

def raw4241step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]

theorem canonical4241 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4241 = injectiveMoment H node88 := by
  calc
    injectiveMoment H raw4241 = injectiveMoment H raw4241step0 := by
      have heq : raw4241step0 = raw4241.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4241).symm
    injectiveMoment H raw4241step0 = injectiveMoment H raw4241step1 := by
      have heq : raw4241step1 = -raw4241step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4241step0).symm
    injectiveMoment H raw4241step1 = injectiveMoment H raw4241step2 := by
      have heq : raw4241step2 = (fun i j => raw4241step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4241step1 permutation24 permutation3
    _ = injectiveMoment H node88 := by rfl

def raw4242 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![2, -2, 1, -1], ![0, 2, -4, 2]]

def raw4242step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![3, 1, -4], ![-1, -1, 2]]

def raw4242step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![0, 2, -2], ![-3, -1, 4], ![1, 1, -2]]

def raw4242step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

theorem canonical4242 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4242 = injectiveMoment H node85 := by
  calc
    injectiveMoment H raw4242 = injectiveMoment H raw4242step0 := by
      have heq : raw4242step0 = raw4242.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4242).symm
    injectiveMoment H raw4242step0 = injectiveMoment H raw4242step1 := by
      have heq : raw4242step1 = -raw4242step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4242step0).symm
    injectiveMoment H raw4242step1 = injectiveMoment H raw4242step2 := by
      have heq : raw4242step2 = (fun i j => raw4242step1 (permutation24 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4242step1 permutation24 permutation3
    _ = injectiveMoment H node85 := by rfl

def raw4243 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -2, 2, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw4243step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -2, 1, 0], ![-3, 2, 1, 0], ![4, 0, -2, -2]]

def raw4243step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, 0, 0, -2]]

theorem canonical4243 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4243 = injectiveMoment H node401 := by
  calc
    injectiveMoment H raw4243 = injectiveMoment H raw4243step0 := by
      have heq : raw4243step0 = raw4243.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4243).symm
    injectiveMoment H raw4243step0 = injectiveMoment H raw4243step1 := by
      have heq : raw4243step1 = (fun i j => raw4243step0 (permutation30 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4243step0 permutation30 permutation32
    _ = injectiveMoment H node401 := by rfl

def raw4244 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

theorem canonical4244 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4244 = injectiveMoment H node2148 := by
  rfl

def raw4245 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical4245 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4245 = injectiveMoment H node2149 := by
  rfl

def raw4246 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical4246 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4246 = injectiveMoment H node2150 := by
  rfl

def raw4247 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical4247 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4247 = injectiveMoment H node2151 := by
  rfl

def raw4248 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def raw4248step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![-3, 2, 1, 0], ![4, -1, -2, -1]]

def raw4248step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, 0, -3]]

theorem canonical4248 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4248 = injectiveMoment H node460 := by
  calc
    injectiveMoment H raw4248 = injectiveMoment H raw4248step0 := by
      have heq : raw4248step0 = raw4248.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4248).symm
    injectiveMoment H raw4248step0 = injectiveMoment H raw4248step1 := by
      have heq : raw4248step1 = (fun i j => raw4248step0 (permutation27 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4248step0 permutation27 permutation24
    _ = injectiveMoment H node460 := by rfl

def raw4249 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw4249step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-3, 2, 0, 1], ![4, -1, 0, -3]]

def raw4249step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -3, 4], ![0, 2, 1, -3], ![1, 0, 1, -2]]

theorem canonical4249 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4249 = injectiveMoment H node1091 := by
  calc
    injectiveMoment H raw4249 = injectiveMoment H raw4249step0 := by
      have heq : raw4249step0 = raw4249.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4249).symm
    injectiveMoment H raw4249step0 = injectiveMoment H raw4249step1 := by
      have heq : raw4249step1 = (fun i j => raw4249step0 (permutation20 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4249step0 permutation20 permutation24
    _ = injectiveMoment H node1091 := by rfl

def raw4250 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def raw4250step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-3, 2, 1, 0], ![4, -1, -1, -2]]

def raw4250step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 1, 0, -2]]

theorem canonical4250 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4250 = injectiveMoment H node466 := by
  calc
    injectiveMoment H raw4250 = injectiveMoment H raw4250step0 := by
      have heq : raw4250step0 = raw4250.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4250).symm
    injectiveMoment H raw4250step0 = injectiveMoment H raw4250step1 := by
      have heq : raw4250step1 = (fun i j => raw4250step0 (permutation32 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4250step0 permutation32 permutation32
    _ = injectiveMoment H node466 := by rfl

def raw4251 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw4251step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-3, 2, 0, 1], ![4, -1, -1, -2]]

def raw4251step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, 0, -2]]

theorem canonical4251 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4251 = injectiveMoment H node762 := by
  calc
    injectiveMoment H raw4251 = injectiveMoment H raw4251step0 := by
      have heq : raw4251step0 = raw4251.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4251).symm
    injectiveMoment H raw4251step0 = injectiveMoment H raw4251step1 := by
      have heq : raw4251step1 = (fun i j => raw4251step0 (permutation30 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4251step0 permutation30 permutation26
    _ = injectiveMoment H node762 := by rfl

def raw4252 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![1, 0, 1, -2], ![1, 0, 0, -1]]

def raw4252step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-3, 2, 1, 0], ![4, -1, -2, -1]]

def raw4252step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, 0, -2]]

theorem canonical4252 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4252 = injectiveMoment H node762 := by
  calc
    injectiveMoment H raw4252 = injectiveMoment H raw4252step0 := by
      have heq : raw4252step0 = raw4252.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4252).symm
    injectiveMoment H raw4252step0 = injectiveMoment H raw4252step1 := by
      have heq : raw4252step1 = (fun i j => raw4252step0 (permutation30 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4252step0 permutation30 permutation32
    _ = injectiveMoment H node762 := by rfl

def raw4253 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical4253 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4253 = injectiveMoment H node2152 := by
  rfl

def raw4254 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 3, -2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw4254step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![-3, 3, 0, 0], ![4, -2, 0, -2]]

def raw4254step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![3, -3, 0, 0], ![-4, 2, 0, 2]]

def raw4254step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -3, 3], ![0, 2, 2, -4], ![1, -1, 1, -1]]

theorem canonical4254 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4254 = injectiveMoment H node1026 := by
  calc
    injectiveMoment H raw4254 = injectiveMoment H raw4254step0 := by
      have heq : raw4254step0 = raw4254.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4254).symm
    injectiveMoment H raw4254step0 = injectiveMoment H raw4254step1 := by
      have heq : raw4254step1 = -raw4254step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4254step0).symm
    injectiveMoment H raw4254step1 = injectiveMoment H raw4254step2 := by
      have heq : raw4254step2 = (fun i j => raw4254step1 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4254step1 permutation12 permutation26
    _ = injectiveMoment H node1026 := by rfl

def raw4255 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 3, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw4255step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, 0, 0], ![-3, 3, 0, 0], ![4, -2, -1, -1]]

def raw4255step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, 1, 0, -2]]

theorem canonical4255 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4255 = injectiveMoment H node905 := by
  calc
    injectiveMoment H raw4255 = injectiveMoment H raw4255step0 := by
      have heq : raw4255step0 = raw4255.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4255).symm
    injectiveMoment H raw4255step0 = injectiveMoment H raw4255step1 := by
      have heq : raw4255step1 = (fun i j => raw4255step0 (permutation30 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4255step0 permutation30 permutation26
    _ = injectiveMoment H node905 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

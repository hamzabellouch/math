import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw320 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]

theorem canonical320 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw320 = injectiveMoment H node18 := by
  rfl

def raw321 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 0, -1], ![1, 3, -4]]

def raw321step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 2, -1], ![-1, 0, 1], ![-1, -3, 4]]

def raw321step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]

theorem canonical321 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw321 = injectiveMoment H node80 := by
  calc
    injectiveMoment H raw321 = injectiveMoment H raw321step0 := by
      have heq : raw321step0 = -raw321 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw321).symm
    injectiveMoment H raw321step0 = injectiveMoment H raw321step1 := by
      have heq : raw321step1 = (fun i j => raw321step0 (permutation31 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw321step0 permutation31 permutation5
    _ = injectiveMoment H node80 := by rfl

def raw322 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]

theorem canonical322 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw322 = injectiveMoment H node89 := by
  rfl

def raw323 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 2, -3], ![1, 1, -2]]

def raw323step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]

theorem canonical323 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw323 = injectiveMoment H node89 := by
  calc
    injectiveMoment H raw323 = injectiveMoment H raw323step0 := by
      have heq : raw323step0 = (fun i j => raw323 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw323 permutation10 permutation3
    _ = injectiveMoment H node89 := by rfl

def raw324 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![2, 3, -5]]

def raw324step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![4, 1, -5]]

def raw324step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -3, 2], ![1, 4, -5]]

theorem canonical324 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw324 = injectiveMoment H node39 := by
  calc
    injectiveMoment H raw324 = injectiveMoment H raw324step0 := by
      have heq : raw324step0 = raw324.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw324).symm
    injectiveMoment H raw324step0 = injectiveMoment H raw324step1 := by
      have heq : raw324step1 = (fun i j => raw324step0 (permutation5 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw324step0 permutation5 permutation5
    _ = injectiveMoment H node39 := by rfl

def raw325 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

theorem canonical325 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw325 = injectiveMoment H node90 := by
  rfl

def raw326 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw326step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]

def raw326step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical326 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw326 = injectiveMoment H node173 := by
  calc
    injectiveMoment H raw326 = injectiveMoment H raw326step0 := by
      have heq : raw326step0 = -raw326 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw326).symm
    injectiveMoment H raw326step0 = injectiveMoment H raw326step1 := by
      have heq : raw326step1 = (fun i j => raw326step0 (permutation32 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw326step0 permutation32 permutation5
    _ = injectiveMoment H node173 := by rfl

def raw327 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]

def raw327step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

theorem canonical327 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw327 = injectiveMoment H node244 := by
  calc
    injectiveMoment H raw327 = injectiveMoment H raw327step0 := by
      have heq : raw327step0 = (fun i j => raw327 (permutation9 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw327 permutation9 permutation5
    _ = injectiveMoment H node244 := by rfl

def raw328 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]

def raw328step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![4, 0, -4]]

def raw328step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-4, 0, 4]]

def raw328step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

theorem canonical328 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw328 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw328 = injectiveMoment H raw328step0 := by
      have heq : raw328step0 = raw328.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw328).symm
    injectiveMoment H raw328step0 = injectiveMoment H raw328step1 := by
      have heq : raw328step1 = -raw328step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw328step0).symm
    injectiveMoment H raw328step1 = injectiveMoment H raw328step2 := by
      have heq : raw328step2 = (fun i j => raw328step1 (permutation4 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw328step1 permutation4 permutation6
    _ = injectiveMoment H node59 := by rfl

def raw329 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![1, -1, 0], ![1, 2, -3]]

def raw329step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-1, 1, 0], ![-1, -2, 3]]

def raw329step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical329 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw329 = injectiveMoment H node173 := by
  calc
    injectiveMoment H raw329 = injectiveMoment H raw329step0 := by
      have heq : raw329step0 = -raw329 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw329).symm
    injectiveMoment H raw329step0 = injectiveMoment H raw329step1 := by
      have heq : raw329step1 = (fun i j => raw329step0 (permutation30 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw329step0 permutation30 permutation5
    _ = injectiveMoment H node173 := by rfl

def raw330 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![1, -1, 0], ![1, 1, -2]]

def raw330step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

theorem canonical330 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw330 = injectiveMoment H node244 := by
  calc
    injectiveMoment H raw330 = injectiveMoment H raw330step0 := by
      have heq : raw330step0 = (fun i j => raw330 (permutation11 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw330 permutation11 permutation5
    _ = injectiveMoment H node244 := by rfl

def raw331 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![1, -2, 1], ![1, 1, -2]]

def raw331step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]

theorem canonical331 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw331 = injectiveMoment H node89 := by
  calc
    injectiveMoment H raw331 = injectiveMoment H raw331step0 := by
      have heq : raw331step0 = (fun i j => raw331 (permutation12 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw331 permutation12 permutation3
    _ = injectiveMoment H node89 := by rfl

def raw332 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![1, -1, 0], ![1, 0, -1]]

def raw332step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -2, 3], ![-1, 1, 0], ![-1, 0, 1]]

def raw332step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical332 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw332 = injectiveMoment H node173 := by
  calc
    injectiveMoment H raw332 = injectiveMoment H raw332step0 := by
      have heq : raw332step0 = -raw332 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw332).symm
    injectiveMoment H raw332step0 = injectiveMoment H raw332step1 := by
      have heq : raw332step1 = (fun i j => raw332step0 (permutation20 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw332step0 permutation20 permutation5
    _ = injectiveMoment H node173 := by rfl

def raw333 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]

def raw333step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -2, 3], ![-2, 1, 1]]

def raw333step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 3, -4]]

theorem canonical333 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw333 = injectiveMoment H node40 := by
  calc
    injectiveMoment H raw333 = injectiveMoment H raw333step0 := by
      have heq : raw333step0 = -raw333 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw333).symm
    injectiveMoment H raw333step0 = injectiveMoment H raw333step1 := by
      have heq : raw333step1 = (fun i j => raw333step0 (permutation6 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw333step0 permutation6 permutation5
    _ = injectiveMoment H node40 := by rfl

def raw334 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![1, -2, 1], ![1, 0, -1]]

def raw334step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -3, 4], ![-1, 2, -1], ![-1, 0, 1]]

def raw334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]

theorem canonical334 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw334 = injectiveMoment H node80 := by
  calc
    injectiveMoment H raw334 = injectiveMoment H raw334step0 := by
      have heq : raw334step0 = -raw334 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw334).symm
    injectiveMoment H raw334step0 = injectiveMoment H raw334step1 := by
      have heq : raw334step1 = (fun i j => raw334step0 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw334step0 permutation19 permutation5
    _ = injectiveMoment H node80 := by rfl

def raw335 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![2, -2, 0]]

def raw335step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![4, -4, 0]]

def raw335step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![2, -3, 1]]

theorem canonical335 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw335 = injectiveMoment H node38 := by
  calc
    injectiveMoment H raw335 = injectiveMoment H raw335step0 := by
      have heq : raw335step0 = raw335.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw335).symm
    injectiveMoment H raw335step0 = injectiveMoment H raw335step1 := by
      have heq : raw335step1 = (fun i j => raw335step0 (permutation6 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw335step0 permutation6 permutation7
    _ = injectiveMoment H node38 := by rfl

def raw336 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![2, -2, 0], ![1, 3, -4]]

def raw336step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![4, 0, -4]]

def raw336step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![2, -3, 1]]

theorem canonical336 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw336 = injectiveMoment H node38 := by
  calc
    injectiveMoment H raw336 = injectiveMoment H raw336step0 := by
      have heq : raw336step0 = raw336.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw336).symm
    injectiveMoment H raw336step0 = injectiveMoment H raw336step1 := by
      have heq : raw336step1 = (fun i j => raw336step0 (permutation6 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw336step0 permutation6 permutation5
    _ = injectiveMoment H node38 := by rfl

def raw337 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 0, 3], ![0, -2, 2, 0], ![3, 2, -2, -3]]

def raw337step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![3, 0, -3]]

def raw337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![2, 0, -2]]

theorem canonical337 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw337 = injectiveMoment H node192 := by
  calc
    injectiveMoment H raw337 = injectiveMoment H raw337step0 := by
      have heq : raw337step0 = raw337.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw337).symm
    injectiveMoment H raw337step0 = injectiveMoment H raw337step1 := by
      have heq : raw337step1 = (fun i j => raw337step0 (permutation16 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw337step0 permutation16 permutation5
    _ = injectiveMoment H node192 := by rfl

def raw338 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 0, 3], ![1, -2, 2, -1], ![2, 2, -2, -2]]

def raw338step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]

theorem canonical338 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw338 = injectiveMoment H node101 := by
  calc
    injectiveMoment H raw338 = injectiveMoment H raw338step0 := by
      have heq : raw338step0 = raw338.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw338).symm
    _ = injectiveMoment H node101 := by rfl

def raw339 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![-2, 2, 1, -1], ![5, -2, -2, -1]]

def raw339step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

theorem canonical339 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw339 = injectiveMoment H node74 := by
  calc
    injectiveMoment H raw339 = injectiveMoment H raw339step0 := by
      have heq : raw339step0 = raw339.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw339).symm
    _ = injectiveMoment H node74 := by rfl

def raw340 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![-1, 2, -2, 1], ![4, -2, 1, -3]]

def raw340step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

theorem canonical340 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw340 = injectiveMoment H node84 := by
  calc
    injectiveMoment H raw340 = injectiveMoment H raw340step0 := by
      have heq : raw340step0 = raw340.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw340).symm
    _ = injectiveMoment H node84 := by rfl

def raw341 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![-1, 2, 1, -2], ![4, -2, -2, 0]]

def raw341step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]

theorem canonical341 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw341 = injectiveMoment H node85 := by
  calc
    injectiveMoment H raw341 = injectiveMoment H raw341step0 := by
      have heq : raw341step0 = raw341.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw341).symm
    _ = injectiveMoment H node85 := by rfl

def raw342 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![-1, 3, -2, 0], ![4, -3, 1, -2]]

def raw342step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]

theorem canonical342 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw342 = injectiveMoment H node86 := by
  calc
    injectiveMoment H raw342 = injectiveMoment H raw342step0 := by
      have heq : raw342step0 = raw342.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw342).symm
    _ = injectiveMoment H node86 := by rfl

def raw343 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![0, -2, 1, 1], ![3, 2, -2, -3]]

def raw343step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]

def raw343step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

theorem canonical343 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw343 = injectiveMoment H node196 := by
  calc
    injectiveMoment H raw343 = injectiveMoment H raw343step0 := by
      have heq : raw343step0 = raw343.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw343).symm
    injectiveMoment H raw343step0 = injectiveMoment H raw343step1 := by
      have heq : raw343step1 = (fun i j => raw343step0 (permutation15 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw343step0 permutation15 permutation5
    _ = injectiveMoment H node196 := by rfl

def raw344 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![0, -2, 2, 0], ![3, 2, -3, -2]]

def raw344step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]

def raw344step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -2, 3], ![-2, 0, 2]]

def raw344step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

theorem canonical344 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw344 = injectiveMoment H node163 := by
  calc
    injectiveMoment H raw344 = injectiveMoment H raw344step0 := by
      have heq : raw344step0 = raw344.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw344).symm
    injectiveMoment H raw344step0 = injectiveMoment H raw344step1 := by
      have heq : raw344step1 = -raw344step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw344step0).symm
    injectiveMoment H raw344step1 = injectiveMoment H raw344step2 := by
      have heq : raw344step2 = (fun i j => raw344step1 (permutation25 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw344step1 permutation25 permutation5
    _ = injectiveMoment H node163 := by rfl

def raw345 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![0, -2, 3, -1], ![3, 2, -4, -1]]

def raw345step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 3, -4], ![2, -1, -1]]

def raw345step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -3, 4], ![-2, 1, 1]]

def raw345step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]

theorem canonical345 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw345 = injectiveMoment H node86 := by
  calc
    injectiveMoment H raw345 = injectiveMoment H raw345step0 := by
      have heq : raw345step0 = raw345.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw345).symm
    injectiveMoment H raw345step0 = injectiveMoment H raw345step1 := by
      have heq : raw345step1 = -raw345step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw345step0).symm
    injectiveMoment H raw345step1 = injectiveMoment H raw345step2 := by
      have heq : raw345step2 = (fun i j => raw345step1 (permutation22 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw345step1 permutation22 permutation5
    _ = injectiveMoment H node86 := by rfl

def raw346 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![0, 2, -2, 0], ![3, -2, 1, -2]]

def raw346step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def raw346step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]

def raw346step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

theorem canonical346 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw346 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw346 = injectiveMoment H raw346step0 := by
      have heq : raw346step0 = raw346.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw346).symm
    injectiveMoment H raw346step0 = injectiveMoment H raw346step1 := by
      have heq : raw346step1 = -raw346step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw346step0).symm
    injectiveMoment H raw346step1 = injectiveMoment H raw346step2 := by
      have heq : raw346step2 = (fun i j => raw346step1 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw346step1 permutation19 permutation5
    _ = injectiveMoment H node198 := by rfl

def raw347 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![0, 3, -2, -1], ![3, -3, 1, -1]]

def raw347step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]

theorem canonical347 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw347 = injectiveMoment H node98 := by
  calc
    injectiveMoment H raw347 = injectiveMoment H raw347step0 := by
      have heq : raw347step0 = raw347.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw347).symm
    _ = injectiveMoment H node98 := by rfl

def raw348 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![0, 4, -2, -2], ![3, -4, 1, 0]]

def raw348step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 4, -4], ![1, -2, 1], ![2, -2, 0]]

theorem canonical348 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw348 = injectiveMoment H node99 := by
  calc
    injectiveMoment H raw348 = injectiveMoment H raw348step0 := by
      have heq : raw348step0 = raw348.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw348).symm
    _ = injectiveMoment H node99 := by rfl

def raw349 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![1, -2, 1, 0], ![2, 2, -2, -2]]

def raw349step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]

def raw349step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

theorem canonical349 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw349 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw349 = injectiveMoment H raw349step0 := by
      have heq : raw349step0 = raw349.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw349).symm
    injectiveMoment H raw349step0 = injectiveMoment H raw349step1 := by
      have heq : raw349step1 = (fun i j => raw349step0 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw349step0 permutation19 permutation5
    _ = injectiveMoment H node212 := by rfl

def raw350 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![1, -2, 2, -1], ![2, 2, -3, -1]]

def raw350step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]

theorem canonical350 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw350 = injectiveMoment H node103 := by
  calc
    injectiveMoment H raw350 = injectiveMoment H raw350step0 := by
      have heq : raw350step0 = raw350.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw350).symm
    _ = injectiveMoment H node103 := by rfl

def raw351 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![1, -2, 3, -2], ![2, 2, -4, 0]]

def raw351step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 3, -4], ![2, -2, 0]]

theorem canonical351 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw351 = injectiveMoment H node104 := by
  calc
    injectiveMoment H raw351 = injectiveMoment H raw351step0 := by
      have heq : raw351step0 = raw351.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw351).symm
    _ = injectiveMoment H node104 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw10176 : Matrix (Fin 3) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-2, -3, 4, 1], ![0, 3, -4, 1]]

def raw10176step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![0, -3, 3], ![0, 4, -4], ![-2, 1, 1]]

def raw10176step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 3, -3], ![0, -4, 4], ![2, -1, -1]]

def raw10176step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![2, -1, -1]]

theorem canonical10176 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw10176 = injectiveMoment H node193 := by
  calc
    injectiveMoment H raw10176 = injectiveMoment H raw10176step0 := by
      have heq : raw10176step0 = raw10176.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10176).symm
    injectiveMoment H raw10176step0 = injectiveMoment H raw10176step1 := by
      have heq : raw10176step1 = -raw10176step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw10176step0).symm
    injectiveMoment H raw10176step1 = injectiveMoment H raw10176step2 := by
      have heq : raw10176step2 = (fun i j => raw10176step1 (permutation9 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10176step1 permutation9 permutation4
    _ = injectiveMoment H node193 := by rfl

def raw10177 : Matrix (Fin 3) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-2, -2, 3, 1], ![0, 2, -3, 1]]

def raw10177step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, 3, -3], ![-2, 1, 1]]

def raw10177step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 2, -2], ![0, -3, 3], ![2, -1, -1]]

def raw10177step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

theorem canonical10177 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw10177 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw10177 = injectiveMoment H raw10177step0 := by
      have heq : raw10177step0 = raw10177.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10177).symm
    injectiveMoment H raw10177step0 = injectiveMoment H raw10177step1 := by
      have heq : raw10177step1 = -raw10177step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw10177step0).symm
    injectiveMoment H raw10177step1 = injectiveMoment H raw10177step2 := by
      have heq : raw10177step2 = (fun i j => raw10177step1 (permutation9 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10177step1 permutation9 permutation4
    _ = injectiveMoment H node198 := by rfl

def raw10178 : Matrix (Fin 3) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, -3, 3, 1], ![-1, 3, -3, 1]]

def raw10178step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, -3, 3], ![0, 3, -3], ![-2, 1, 1]]

def raw10178step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 3, -3], ![2, -1, -1]]

theorem canonical10178 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10178 = injectiveMoment H node220 := by
  calc
    injectiveMoment H raw10178 = injectiveMoment H raw10178step0 := by
      have heq : raw10178step0 = raw10178.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10178).symm
    injectiveMoment H raw10178step0 = injectiveMoment H raw10178step1 := by
      have heq : raw10178step1 = (fun i j => raw10178step0 (permutation30 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10178step0 permutation30 permutation3
    _ = injectiveMoment H node220 := by rfl

def raw10179 : Matrix (Fin 3) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, -3, 4, 0], ![-1, 3, -4, 2]]

def raw10179step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, -3, 3], ![0, 4, -4], ![-2, 0, 2]]

def raw10179step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![2, -1, -1]]

theorem canonical10179 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10179 = injectiveMoment H node193 := by
  calc
    injectiveMoment H raw10179 = injectiveMoment H raw10179step0 := by
      have heq : raw10179step0 = raw10179.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10179).symm
    injectiveMoment H raw10179step0 = injectiveMoment H raw10179step1 := by
      have heq : raw10179step1 = (fun i j => raw10179step0 (permutation30 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10179step0 permutation30 permutation3
    _ = injectiveMoment H node193 := by rfl

def raw10180 : Matrix (Fin 3) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, -2, 3, 0], ![-1, 2, -3, 2]]

def raw10180step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, -2, 2], ![0, 3, -3], ![-2, 0, 2]]

def raw10180step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

theorem canonical10180 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10180 = injectiveMoment H node198 := by
  calc
    injectiveMoment H raw10180 = injectiveMoment H raw10180step0 := by
      have heq : raw10180step0 = raw10180.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10180).symm
    injectiveMoment H raw10180step0 = injectiveMoment H raw10180step1 := by
      have heq : raw10180step1 = (fun i j => raw10180step0 (permutation30 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10180step0 permutation30 permutation3
    _ = injectiveMoment H node198 := by rfl

def raw10181 : Matrix (Fin 3) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -3, 3, 0], ![-2, 3, -3, 2]]

def raw10181step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -3, 3], ![0, 3, -3], ![-2, 0, 2]]

def raw10181step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![2, 0, -2]]

theorem canonical10181 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10181 = injectiveMoment H node192 := by
  calc
    injectiveMoment H raw10181 = injectiveMoment H raw10181step0 := by
      have heq : raw10181step0 = raw10181.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10181).symm
    injectiveMoment H raw10181step0 = injectiveMoment H raw10181step1 := by
      have heq : raw10181step1 = (fun i j => raw10181step0 (permutation30 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10181step0 permutation30 permutation3
    _ = injectiveMoment H node192 := by rfl

def raw10182 : Matrix (Fin 3) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -2, 2, 0], ![-2, 2, -2, 2]]

def raw10182step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![0, 2, -2], ![-2, 0, 2]]

def raw10182step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

theorem canonical10182 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10182 = injectiveMoment H node197 := by
  calc
    injectiveMoment H raw10182 = injectiveMoment H raw10182step0 := by
      have heq : raw10182step0 = raw10182.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10182).symm
    injectiveMoment H raw10182step0 = injectiveMoment H raw10182step1 := by
      have heq : raw10182step1 = (fun i j => raw10182step0 (permutation30 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10182step0 permutation30 permutation3
    _ = injectiveMoment H node197 := by rfl

def raw10183 : Matrix (Fin 3) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -2, 3, -1], ![-2, 2, -3, 3]]

def raw10183step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![0, 3, -3], ![-2, -1, 3]]

def raw10183step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

theorem canonical10183 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10183 = injectiveMoment H node163 := by
  calc
    injectiveMoment H raw10183 = injectiveMoment H raw10183step0 := by
      have heq : raw10183step0 = raw10183.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10183).symm
    injectiveMoment H raw10183step0 = injectiveMoment H raw10183step1 := by
      have heq : raw10183step1 = (fun i j => raw10183step0 (permutation30 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10183step0 permutation30 permutation3
    _ = injectiveMoment H node163 := by rfl

def raw10184 : Matrix (Fin 3) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, -2, 2, -1], ![-3, 2, -2, 3]]

def raw10184step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![0, 2, -2], ![-2, -1, 3]]

def raw10184step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]

theorem canonical10184 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10184 = injectiveMoment H node162 := by
  calc
    injectiveMoment H raw10184 = injectiveMoment H raw10184step0 := by
      have heq : raw10184step0 = raw10184.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw10184).symm
    injectiveMoment H raw10184step0 = injectiveMoment H raw10184step1 := by
      have heq : raw10184step1 = (fun i j => raw10184step0 (permutation30 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10184step0 permutation30 permutation3
    _ = injectiveMoment H node162 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

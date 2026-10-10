import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes30

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3168 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

theorem canonical3168 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3168 = injectiveMoment H node1968 := by
  rfl

def raw3169 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

theorem canonical3169 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3169 = injectiveMoment H node1969 := by
  rfl

def raw3170 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem canonical3170 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3170 = injectiveMoment H node1970 := by
  rfl

def raw3171 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 3, -3]]

def raw3171step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-1, -2, 0, 3], ![3, 1, -1, -3]]

def raw3171step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![1, 2, 0, -3], ![-3, -1, 1, 3]]

def raw3171step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 1, -3], ![1, -1, -3, 3]]

theorem canonical3171 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3171 = injectiveMoment H node1060 := by
  calc
    injectiveMoment H raw3171 = injectiveMoment H raw3171step0 := by
      have heq : raw3171step0 = raw3171.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3171).symm
    injectiveMoment H raw3171step0 = injectiveMoment H raw3171step1 := by
      have heq : raw3171step1 = -raw3171step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3171step0).symm
    injectiveMoment H raw3171step1 = injectiveMoment H raw3171step2 := by
      have heq : raw3171step2 = (fun i j => raw3171step1 (permutation15 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3171step1 permutation15 permutation23
    _ = injectiveMoment H node1060 := by rfl

def raw3172 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 2, -2]]

theorem canonical3172 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3172 = injectiveMoment H node1971 := by
  rfl

def raw3173 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -2, 2, -2]]

theorem canonical3173 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3173 = injectiveMoment H node593 := by
  rfl

def raw3174 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical3174 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3174 = injectiveMoment H node1972 := by
  rfl

def raw3175 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, -1, 0, 0]]

def raw3175step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical3175 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3175 = injectiveMoment H node1972 := by
  calc
    injectiveMoment H raw3175 = injectiveMoment H raw3175step0 := by
      have heq : raw3175step0 = (fun i j => raw3175 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3175 permutation34 permutation9
    _ = injectiveMoment H node1972 := by rfl

def raw3176 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -2, 1, -1]]

theorem canonical3176 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3176 = injectiveMoment H node594 := by
  rfl

def raw3177 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical3177 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3177 = injectiveMoment H node1973 := by
  rfl

def raw3178 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

theorem canonical3178 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3178 = injectiveMoment H node595 := by
  rfl

def raw3179 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

theorem canonical3179 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3179 = injectiveMoment H node596 := by
  rfl

def raw3180 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -2, 3, -2], ![1, 1, 0, -2]]

theorem canonical3180 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3180 = injectiveMoment H node597 := by
  rfl

def raw3181 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw3181step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 2, -1], ![-1, 1, 0, 0], ![-1, 0, -3, 4]]

def raw3181step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 1, -3], ![1, -1, 0, 0]]

theorem canonical3181 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3181 = injectiveMoment H node1307 := by
  calc
    injectiveMoment H raw3181 = injectiveMoment H raw3181step0 := by
      have heq : raw3181step0 = -raw3181 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3181).symm
    injectiveMoment H raw3181step0 = injectiveMoment H raw3181step1 := by
      have heq : raw3181step1 = (fun i j => raw3181step0 (permutation19 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3181step0 permutation19 permutation15
    _ = injectiveMoment H node1307 := by rfl

def raw3182 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def raw3182step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 2, -1], ![-1, 1, -1, 1], ![-1, 0, -2, 3]]

def raw3182step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, -1, -1, 1]]

theorem canonical3182 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3182 = injectiveMoment H node1308 := by
  calc
    injectiveMoment H raw3182 = injectiveMoment H raw3182step0 := by
      have heq : raw3182step0 = -raw3182 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3182).symm
    injectiveMoment H raw3182step0 = injectiveMoment H raw3182step1 := by
      have heq : raw3182step1 = (fun i j => raw3182step0 (permutation19 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3182step0 permutation19 permutation15
    _ = injectiveMoment H node1308 := by rfl

def raw3183 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw3183step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 2, -1], ![-1, 1, -3, 3], ![-1, 0, 0, 1]]

def raw3183step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

theorem canonical3183 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3183 = injectiveMoment H node1312 := by
  calc
    injectiveMoment H raw3183 = injectiveMoment H raw3183step0 := by
      have heq : raw3183step0 = -raw3183 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3183).symm
    injectiveMoment H raw3183step0 = injectiveMoment H raw3183step1 := by
      have heq : raw3183step1 = (fun i j => raw3183step0 (permutation19 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3183step0 permutation19 permutation15
    _ = injectiveMoment H node1312 := by rfl

def raw3184 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, -1, 3, -3]]

def raw3184step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 2, -1], ![-1, 0, 0, 1], ![-1, 1, -3, 3]]

def raw3184step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

theorem canonical3184 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3184 = injectiveMoment H node1312 := by
  calc
    injectiveMoment H raw3184 = injectiveMoment H raw3184step0 := by
      have heq : raw3184step0 = -raw3184 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3184).symm
    injectiveMoment H raw3184step0 = injectiveMoment H raw3184step1 := by
      have heq : raw3184step1 = (fun i j => raw3184step0 (permutation17 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3184step0 permutation17 permutation15
    _ = injectiveMoment H node1312 := by rfl

def raw3185 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, -1, 2, -2]]

def raw3185step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 2, -1], ![-1, 0, -1, 2], ![-1, 1, -2, 2]]

def raw3185step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, -1, -2, 2]]

theorem canonical3185 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3185 = injectiveMoment H node1310 := by
  calc
    injectiveMoment H raw3185 = injectiveMoment H raw3185step0 := by
      have heq : raw3185step0 = -raw3185 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3185).symm
    injectiveMoment H raw3185step0 = injectiveMoment H raw3185step1 := by
      have heq : raw3185step1 = (fun i j => raw3185step0 (permutation17 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3185step0 permutation17 permutation15
    _ = injectiveMoment H node1310 := by rfl

def raw3186 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, 0, 2, -3], ![1, -1, 1, -1]]

def raw3186step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 2, -1], ![-1, 0, -2, 3], ![-1, 1, -1, 1]]

def raw3186step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, -1, -1, 1]]

theorem canonical3186 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3186 = injectiveMoment H node1308 := by
  calc
    injectiveMoment H raw3186 = injectiveMoment H raw3186step0 := by
      have heq : raw3186step0 = -raw3186 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3186).symm
    injectiveMoment H raw3186step0 = injectiveMoment H raw3186step1 := by
      have heq : raw3186step1 = (fun i j => raw3186step0 (permutation17 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3186step0 permutation17 permutation15
    _ = injectiveMoment H node1308 := by rfl

def raw3187 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, 0, 3, -4], ![1, -1, 0, 0]]

def raw3187step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, -1, 2, -1], ![-1, 0, -3, 4], ![-1, 1, 0, 0]]

def raw3187step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 1, -3], ![1, -1, 0, 0]]

theorem canonical3187 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3187 = injectiveMoment H node1307 := by
  calc
    injectiveMoment H raw3187 = injectiveMoment H raw3187step0 := by
      have heq : raw3187step0 = -raw3187 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3187).symm
    injectiveMoment H raw3187step0 = injectiveMoment H raw3187step1 := by
      have heq : raw3187step1 = (fun i j => raw3187step0 (permutation17 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3187step0 permutation17 permutation15
    _ = injectiveMoment H node1307 := by rfl

def raw3188 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

theorem canonical3188 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3188 = injectiveMoment H node1974 := by
  rfl

def raw3189 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 2, -3]]

theorem canonical3189 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3189 = injectiveMoment H node1975 := by
  rfl

def raw3190 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

theorem canonical3190 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3190 = injectiveMoment H node1976 := by
  rfl

def raw3191 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, 0, -1]]

theorem canonical3191 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3191 = injectiveMoment H node1977 := by
  rfl

def raw3192 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

theorem canonical3192 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3192 = injectiveMoment H node1978 := by
  rfl

def raw3193 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem canonical3193 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3193 = injectiveMoment H node1979 := by
  rfl

def raw3194 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 3, -3]]

def raw3194step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-1, -1, -1, 3], ![3, 0, 0, -3]]

def raw3194step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, 1, 0, -2]]

theorem canonical3194 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3194 = injectiveMoment H node956 := by
  calc
    injectiveMoment H raw3194 = injectiveMoment H raw3194step0 := by
      have heq : raw3194step0 = raw3194.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3194).symm
    injectiveMoment H raw3194step0 = injectiveMoment H raw3194step1 := by
      have heq : raw3194step1 = (fun i j => raw3194step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3194step0 permutation22 permutation17
    _ = injectiveMoment H node956 := by rfl

def raw3195 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, 1, -2]]

def raw3195step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem canonical3195 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3195 = injectiveMoment H node1636 := by
  calc
    injectiveMoment H raw3195 = injectiveMoment H raw3195step0 := by
      have heq : raw3195step0 = (fun i j => raw3195 (permutation33 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3195 permutation33 permutation11
    _ = injectiveMoment H node1636 := by rfl

def raw3196 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw3196step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

theorem canonical3196 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3196 = injectiveMoment H node1635 := by
  calc
    injectiveMoment H raw3196 = injectiveMoment H raw3196step0 := by
      have heq : raw3196step0 = (fun i j => raw3196 (permutation34 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3196 permutation34 permutation11
    _ = injectiveMoment H node1635 := by rfl

def raw3197 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

theorem canonical3197 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3197 = injectiveMoment H node1980 := by
  rfl

def raw3198 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

theorem canonical3198 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3198 = injectiveMoment H node1981 := by
  rfl

def raw3199 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw3199step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

theorem canonical3199 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3199 = injectiveMoment H node1634 := by
  calc
    injectiveMoment H raw3199 = injectiveMoment H raw3199step0 := by
      have heq : raw3199step0 = (fun i j => raw3199 (permutation33 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3199 permutation33 permutation11
    _ = injectiveMoment H node1634 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

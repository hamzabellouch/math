import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw928 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 4, -1], ![3, -4, 1]]

def raw928step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![4, -4], ![-1, 1]]

def raw928step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]

theorem canonical928 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw928 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw928 = injectiveMoment H raw928step0 := by
      have heq : raw928step0 = raw928.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw928).symm
    injectiveMoment H raw928step0 = injectiveMoment H raw928step1 := by
      have heq : raw928step1 = (fun i j => raw928step0 (permutation6 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw928step0 permutation6 permutation2
    _ = injectiveMoment H node8 := by rfl

def raw929 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 5, -2], ![3, -5, 2]]

def raw929step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![5, -5], ![-2, 2]]

def raw929step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![3, -3]]

theorem canonical929 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw929 = injectiveMoment H node7 := by
  calc
    injectiveMoment H raw929 = injectiveMoment H raw929step0 := by
      have heq : raw929step0 = raw929.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw929).symm
    injectiveMoment H raw929step0 = injectiveMoment H raw929step1 := by
      have heq : raw929step1 = (fun i j => raw929step0 (permutation6 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw929step0 permutation6 permutation2
    _ = injectiveMoment H node7 := by rfl

def raw930 : Matrix (Fin 2) (Fin 4) ℤ := ![![-2, -3, 3, 2], ![2, 3, -3, -2]]

def raw930step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-3, 3], ![3, -3], ![2, -2]]

def raw930step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]

theorem canonical930 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw930 = injectiveMoment H node23 := by
  calc
    injectiveMoment H raw930 = injectiveMoment H raw930step0 := by
      have heq : raw930step0 = raw930.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw930).symm
    injectiveMoment H raw930step0 = injectiveMoment H raw930step1 := by
      have heq : raw930step1 = (fun i j => raw930step0 (permutation16 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw930step0 permutation16 permutation1
    _ = injectiveMoment H node23 := by rfl

def raw931 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical931 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw931 = injectiveMoment H node384 := by
  rfl

def raw932 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical932 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw932 = injectiveMoment H node385 := by
  rfl

def raw933 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical933 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw933 = injectiveMoment H node386 := by
  rfl

def raw934 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical934 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw934 = injectiveMoment H node387 := by
  rfl

def raw935 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1]]

def raw935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical935 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw935 = injectiveMoment H node387 := by
  calc
    injectiveMoment H raw935 = injectiveMoment H raw935step0 := by
      have heq : raw935step0 = (fun i j => raw935 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw935 permutation34 permutation3
    _ = injectiveMoment H node387 := by rfl

def raw936 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

theorem canonical936 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw936 = injectiveMoment H node119 := by
  rfl

def raw937 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![0, 1, -1], ![2, -1, -1]]

def raw937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical937 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw937 = injectiveMoment H node385 := by
  calc
    injectiveMoment H raw937 = injectiveMoment H raw937step0 := by
      have heq : raw937step0 = (fun i j => raw937 (permutation35 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw937 permutation35 permutation3
    _ = injectiveMoment H node385 := by rfl

def raw938 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical938 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw938 = injectiveMoment H node388 := by
  rfl

def raw939 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical939 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw939 = injectiveMoment H node389 := by
  rfl

def raw940 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical940 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw940 = injectiveMoment H node120 := by
  rfl

def raw941 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical941 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw941 = injectiveMoment H node390 := by
  rfl

def raw942 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 3, -3], ![2, -1, -1]]

theorem canonical942 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw942 = injectiveMoment H node121 := by
  rfl

def raw943 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical943 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw943 = injectiveMoment H node122 := by
  rfl

def raw944 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

theorem canonical944 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw944 = injectiveMoment H node123 := by
  rfl

def raw945 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical945 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw945 = injectiveMoment H node124 := by
  rfl

def raw946 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![2, 2, -4]]

def raw946step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 1, 2], ![5, -1, -4]]

def raw946step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 2, -2], ![1, 2, -3]]

theorem canonical946 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw946 = injectiveMoment H node48 := by
  calc
    injectiveMoment H raw946 = injectiveMoment H raw946step0 := by
      have heq : raw946step0 = raw946.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw946).symm
    injectiveMoment H raw946step0 = injectiveMoment H raw946step1 := by
      have heq : raw946step1 = (fun i j => raw946step0 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw946step0 permutation7 permutation6
    _ = injectiveMoment H node48 := by rfl

def raw947 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def raw947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical947 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw947 = injectiveMoment H node385 := by
  calc
    injectiveMoment H raw947 = injectiveMoment H raw947step0 := by
      have heq : raw947step0 = (fun i j => raw947 (permutation41 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw947 permutation41 permutation3
    _ = injectiveMoment H node385 := by rfl

def raw948 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def raw948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical948 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw948 = injectiveMoment H node388 := by
  calc
    injectiveMoment H raw948 = injectiveMoment H raw948step0 := by
      have heq : raw948step0 = (fun i j => raw948 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw948 permutation39 permutation3
    _ = injectiveMoment H node388 := by rfl

def raw949 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical949 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw949 = injectiveMoment H node389 := by
  calc
    injectiveMoment H raw949 = injectiveMoment H raw949step0 := by
      have heq : raw949step0 = (fun i j => raw949 (permutation39 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw949 permutation39 permutation3
    _ = injectiveMoment H node389 := by rfl

def raw950 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 1, -1], ![2, 0, -2]]

def raw950step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical950 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw950 = injectiveMoment H node120 := by
  calc
    injectiveMoment H raw950 = injectiveMoment H raw950step0 := by
      have heq : raw950step0 = (fun i j => raw950 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw950 permutation11 permutation3
    _ = injectiveMoment H node120 := by rfl

def raw951 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 2, -2], ![2, -1, -1]]

theorem canonical951 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw951 = injectiveMoment H node125 := by
  rfl

def raw952 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, -1, 0], ![1, 2, -3]]

theorem canonical952 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw952 = injectiveMoment H node126 := by
  rfl

def raw953 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical953 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw953 = injectiveMoment H node127 := by
  rfl

def raw954 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1]]

def raw954step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical954 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw954 = injectiveMoment H node127 := by
  calc
    injectiveMoment H raw954 = injectiveMoment H raw954step0 := by
      have heq : raw954step0 = (fun i j => raw954 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw954 permutation10 permutation3
    _ = injectiveMoment H node127 := by rfl

def raw955 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![2, 1, -3]]

theorem canonical955 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw955 = injectiveMoment H node27 := by
  rfl

def raw956 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![1, -1, 0], ![1, 1, -2]]

theorem canonical956 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw956 = injectiveMoment H node128 := by
  rfl

def raw957 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

theorem canonical957 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw957 = injectiveMoment H node129 := by
  rfl

def raw958 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![2, 0, -2]]

theorem canonical958 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw958 = injectiveMoment H node28 := by
  rfl

def raw959 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

theorem canonical959 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw959 = injectiveMoment H node130 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI

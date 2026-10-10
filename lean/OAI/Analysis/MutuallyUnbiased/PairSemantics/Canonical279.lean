import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8928 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![1, -1, 1, -1], ![-1, 2, -3, 2]]

def raw8928step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, -1, 2], ![2, 1, -3], ![-1, -1, 2]]

def raw8928step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![1, 1, -2], ![-2, -1, 3], ![1, 1, -2]]

def raw8928step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical8928 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8928 = injectiveMoment H node175 := by
  calc
    injectiveMoment H raw8928 = injectiveMoment H raw8928step0 := by
      have heq : raw8928step0 = raw8928.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8928).symm
    injectiveMoment H raw8928step0 = injectiveMoment H raw8928step1 := by
      have heq : raw8928step1 = -raw8928step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8928step0).symm
    injectiveMoment H raw8928step1 = injectiveMoment H raw8928step2 := by
      have heq : raw8928step2 = (fun i j => raw8928step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8928step1 permutation21 permutation3
    _ = injectiveMoment H node175 := by rfl

def raw8929 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![1, 2, 0, -3], ![-1, -1, -2, 4]]

def raw8929step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![-1, 2, -1], ![2, 0, -2], ![-1, -3, 4]]

def raw8929step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![1, -2, 1], ![-2, 0, 2], ![1, 3, -4]]

def raw8929step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

theorem canonical8929 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8929 = injectiveMoment H node206 := by
  calc
    injectiveMoment H raw8929 = injectiveMoment H raw8929step0 := by
      have heq : raw8929step0 = raw8929.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8929).symm
    injectiveMoment H raw8929step0 = injectiveMoment H raw8929step1 := by
      have heq : raw8929step1 = -raw8929step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8929step0).symm
    injectiveMoment H raw8929step1 = injectiveMoment H raw8929step2 := by
      have heq : raw8929step2 = (fun i j => raw8929step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8929step1 permutation21 permutation3
    _ = injectiveMoment H node206 := by rfl

def raw8930 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![2, -3, 0, 1], ![-2, 4, -2, 0]]

def raw8930step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![-1, -3, 4], ![2, 0, -2], ![-1, 1, 0]]

def raw8930step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, 3, -4], ![-2, 0, 2], ![1, -1, 0]]

def raw8930step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

theorem canonical8930 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8930 = injectiveMoment H node201 := by
  calc
    injectiveMoment H raw8930 = injectiveMoment H raw8930step0 := by
      have heq : raw8930step0 = raw8930.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8930).symm
    injectiveMoment H raw8930step0 = injectiveMoment H raw8930step1 := by
      have heq : raw8930step1 = -raw8930step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8930step0).symm
    injectiveMoment H raw8930step1 = injectiveMoment H raw8930step2 := by
      have heq : raw8930step2 = (fun i j => raw8930step1 (permutation22 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8930step1 permutation22 permutation3
    _ = injectiveMoment H node201 := by rfl

def raw8931 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![2, -2, 0, 0], ![-2, 3, -2, 1]]

def raw8931step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![-1, -2, 3], ![2, 0, -2], ![-1, 0, 1]]

def raw8931step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

theorem canonical8931 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8931 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw8931 = injectiveMoment H raw8931step0 := by
      have heq : raw8931step0 = raw8931.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8931).symm
    injectiveMoment H raw8931step0 = injectiveMoment H raw8931step1 := by
      have heq : raw8931step1 = (fun i j => raw8931step0 (permutation20 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8931step0 permutation20 permutation5
    _ = injectiveMoment H node169 := by rfl

def raw8932 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![2, -2, 1, -1], ![-2, 3, -3, 2]]

def raw8932step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![-1, -2, 3], ![2, 1, -3], ![-1, -1, 2]]

def raw8932step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, 2, -3], ![-2, -1, 3], ![1, 1, -2]]

def raw8932step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical8932 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8932 = injectiveMoment H node167 := by
  calc
    injectiveMoment H raw8932 = injectiveMoment H raw8932step0 := by
      have heq : raw8932step0 = raw8932.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8932).symm
    injectiveMoment H raw8932step0 = injectiveMoment H raw8932step1 := by
      have heq : raw8932step1 = -raw8932step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8932step0).symm
    injectiveMoment H raw8932step1 = injectiveMoment H raw8932step2 := by
      have heq : raw8932step2 = (fun i j => raw8932step1 (permutation22 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8932step1 permutation22 permutation3
    _ = injectiveMoment H node167 := by rfl

def raw8933 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![2, -1, 0, -1], ![-2, 2, -2, 2]]

def raw8933step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![-1, -1, 2], ![2, 0, -2], ![-1, -1, 2]]

def raw8933step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, 1, -2], ![-2, 0, 2], ![1, 1, -2]]

def raw8933step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]

theorem canonical8933 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8933 = injectiveMoment H node202 := by
  calc
    injectiveMoment H raw8933 = injectiveMoment H raw8933step0 := by
      have heq : raw8933step0 = raw8933.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8933).symm
    injectiveMoment H raw8933step0 = injectiveMoment H raw8933step1 := by
      have heq : raw8933step1 = -raw8933step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8933step0).symm
    injectiveMoment H raw8933step1 = injectiveMoment H raw8933step2 := by
      have heq : raw8933step2 = (fun i j => raw8933step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8933step1 permutation21 permutation3
    _ = injectiveMoment H node202 := by rfl

def raw8934 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![2, -1, 1, -2], ![-2, 2, -3, 3]]

def raw8934step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![-1, -1, 2], ![2, 1, -3], ![-1, -2, 3]]

def raw8934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, 1, -2], ![-2, -1, 3], ![1, 2, -3]]

def raw8934step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical8934 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8934 = injectiveMoment H node167 := by
  calc
    injectiveMoment H raw8934 = injectiveMoment H raw8934step0 := by
      have heq : raw8934step0 = raw8934.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8934).symm
    injectiveMoment H raw8934step0 = injectiveMoment H raw8934step1 := by
      have heq : raw8934step1 = -raw8934step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8934step0).symm
    injectiveMoment H raw8934step1 = injectiveMoment H raw8934step2 := by
      have heq : raw8934step2 = (fun i j => raw8934step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8934step1 permutation21 permutation3
    _ = injectiveMoment H node167 := by rfl

def raw8935 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![3, -2, 0, -1], ![-3, 3, -2, 2]]

def raw8935step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, -2, 3], ![2, 0, -2], ![-1, -1, 2]]

def raw8935step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, 2, -3], ![-2, 0, 2], ![1, 1, -2]]

def raw8935step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

theorem canonical8935 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8935 = injectiveMoment H node196 := by
  calc
    injectiveMoment H raw8935 = injectiveMoment H raw8935step0 := by
      have heq : raw8935step0 = raw8935.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8935).symm
    injectiveMoment H raw8935step0 = injectiveMoment H raw8935step1 := by
      have heq : raw8935step1 = -raw8935step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8935step0).symm
    injectiveMoment H raw8935step1 = injectiveMoment H raw8935step2 := by
      have heq : raw8935step2 = (fun i j => raw8935step1 (permutation22 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8935step1 permutation22 permutation3
    _ = injectiveMoment H node196 := by rfl

def raw8936 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 2, -1], ![3, -1, 0, -2], ![-3, 2, -2, 3]]

def raw8936step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, -1, 2], ![2, 0, -2], ![-1, -2, 3]]

def raw8936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, 1, -2], ![-2, 0, 2], ![1, 2, -3]]

def raw8936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

theorem canonical8936 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8936 = injectiveMoment H node196 := by
  calc
    injectiveMoment H raw8936 = injectiveMoment H raw8936step0 := by
      have heq : raw8936step0 = raw8936.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8936).symm
    injectiveMoment H raw8936step0 = injectiveMoment H raw8936step1 := by
      have heq : raw8936step1 = -raw8936step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8936step0).symm
    injectiveMoment H raw8936step1 = injectiveMoment H raw8936step2 := by
      have heq : raw8936step2 = (fun i j => raw8936step1 (permutation21 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8936step1 permutation21 permutation3
    _ = injectiveMoment H node196 := by rfl

def raw8937 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 3, -2], ![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw8937step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

theorem canonical8937 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8937 = injectiveMoment H node2728 := by
  calc
    injectiveMoment H raw8937 = injectiveMoment H raw8937step0 := by
      have heq : raw8937step0 = (fun i j => raw8937 (permutation57 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8937 permutation57 permutation9
    _ = injectiveMoment H node2728 := by rfl

def raw8938 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 3, -2], ![-1, 0, -1, 2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def raw8938step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem canonical8938 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8938 = injectiveMoment H node1249 := by
  calc
    injectiveMoment H raw8938 = injectiveMoment H raw8938step0 := by
      have heq : raw8938step0 = (fun i j => raw8938 (permutation15 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8938 permutation15 permutation9
    _ = injectiveMoment H node1249 := by rfl

def raw8939 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 3, -2], ![-1, 2, -1, 0], ![1, -1, -2, 2]]

def raw8939step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 2, -1], ![3, -1, -2], ![-2, 0, 2]]

def raw8939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 1, -1], ![1, -2, 1], ![-3, 1, 2], ![2, 0, -2]]

def raw8939step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

theorem canonical8939 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8939 = injectiveMoment H node226 := by
  calc
    injectiveMoment H raw8939 = injectiveMoment H raw8939step0 := by
      have heq : raw8939step0 = raw8939.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8939).symm
    injectiveMoment H raw8939step0 = injectiveMoment H raw8939step1 := by
      have heq : raw8939step1 = -raw8939step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8939step0).symm
    injectiveMoment H raw8939step1 = injectiveMoment H raw8939step2 := by
      have heq : raw8939step2 = (fun i j => raw8939step1 (permutation19 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8939step1 permutation19 permutation6
    _ = injectiveMoment H node226 := by rfl

def raw8940 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 3, -2], ![0, 0, -1, 1], ![-1, 0, -1, 2], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw8940step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

theorem canonical8940 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8940 = injectiveMoment H node2728 := by
  calc
    injectiveMoment H raw8940 = injectiveMoment H raw8940step0 := by
      have heq : raw8940step0 = (fun i j => raw8940 (permutation80 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8940 permutation80 permutation9
    _ = injectiveMoment H node2728 := by rfl

def raw8941 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 3, -2], ![0, 0, -1, 1], ![-1, 2, -1, 0], ![1, -1, -1, 1]]

def raw8941step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-1, 0, 2, -1], ![3, -1, -1, -1], ![-2, 1, 0, 1]]

def raw8941step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical8941 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8941 = injectiveMoment H node939 := by
  calc
    injectiveMoment H raw8941 = injectiveMoment H raw8941step0 := by
      have heq : raw8941step0 = raw8941.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8941).symm
    injectiveMoment H raw8941step0 = injectiveMoment H raw8941step1 := by
      have heq : raw8941step1 = (fun i j => raw8941step0 (permutation21 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8941step0 permutation21 permutation18
    _ = injectiveMoment H node939 := by rfl

def raw8942 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-1, 2, -1, 0], ![1, -1, 0, 0]]

def raw8942step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -3, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, 1, 0], ![-1, 1, 0, 0]]

def raw8942step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical8942 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8942 = injectiveMoment H node2812 := by
  calc
    injectiveMoment H raw8942 = injectiveMoment H raw8942step0 := by
      have heq : raw8942step0 = -raw8942 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8942).symm
    injectiveMoment H raw8942step0 = injectiveMoment H raw8942step1 := by
      have heq : raw8942step1 = (fun i j => raw8942step0 (permutation135 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8942step0 permutation135 permutation13
    _ = injectiveMoment H node2812 := by rfl

def raw8943 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![0, -1, 0, 1]]

def raw8943step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, -3, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -2, 1, 1], ![0, 1, 0, -1]]

def raw8943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![1, 0, -1]]

def raw8943step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical8943 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8943 = injectiveMoment H node708 := by
  calc
    injectiveMoment H raw8943 = injectiveMoment H raw8943step0 := by
      have heq : raw8943step0 = -raw8943 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8943).symm
    injectiveMoment H raw8943step0 = injectiveMoment H raw8943step1 := by
      have hz : ∀ i, raw8943step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8943step1 = (fun i j => raw8943step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8943step0 permutation9 hz
    injectiveMoment H raw8943step1 = injectiveMoment H raw8943step2 := by
      have heq : raw8943step2 = (fun i j => raw8943step1 (permutation113 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8943step1 permutation113 permutation4
    _ = injectiveMoment H node708 := by rfl

def raw8944 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![0, -1, -1, 2]]

def raw8944step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, -3, 2], ![0, 0, 1, -1], ![0, -2, 1, 1], ![0, 1, 1, -2]]

def raw8944step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![0, 1, -1], ![-2, 1, 1], ![1, 1, -2]]

def raw8944step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical8944 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8944 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw8944 = injectiveMoment H raw8944step0 := by
      have heq : raw8944step0 = -raw8944 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8944).symm
    injectiveMoment H raw8944step0 = injectiveMoment H raw8944step1 := by
      have hz : ∀ i, raw8944step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8944step1 = (fun i j => raw8944step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8944step0 permutation9 hz
    injectiveMoment H raw8944step1 = injectiveMoment H raw8944step2 := by
      have heq : raw8944step2 = (fun i j => raw8944step1 (permutation24 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8944step1 permutation24 permutation4
    _ = injectiveMoment H node229 := by rfl

def raw8945 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -1, 3, -2], ![0, 2, -1, -1], ![0, -1, -2, 3]]

def raw8945step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, 1, -3, 2], ![0, -2, 1, 1], ![0, 1, 2, -3]]

def raw8945step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 1, 1], ![1, 2, -3]]

def raw8945step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![1, 2, -3]]

theorem canonical8945 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8945 = injectiveMoment H node43 := by
  calc
    injectiveMoment H raw8945 = injectiveMoment H raw8945step0 := by
      have heq : raw8945step0 = -raw8945 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8945).symm
    injectiveMoment H raw8945step0 = injectiveMoment H raw8945step1 := by
      have hz : ∀ i, raw8945step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8945step1 = (fun i j => raw8945step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8945step0 permutation9 hz
    injectiveMoment H raw8945step1 = injectiveMoment H raw8945step2 := by
      have heq : raw8945step2 = (fun i j => raw8945step1 (permutation5 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8945step1 permutation5 permutation3
    _ = injectiveMoment H node43 := by rfl

def raw8946 : Matrix (Fin 1) (Fin 2) ℤ := ![![0, 0]]

def raw8946step0 : Matrix (Fin 0) (Fin 2) ℤ := ![]

def raw8946step1 : Matrix (Fin 0) (Fin 1) ℤ := ![]

def raw8946step2 : Matrix (Fin 0) (Fin 0) ℤ := ![]

theorem canonical8946 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8946 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw8946 = injectiveMoment H raw8946step0 := by
      have hz : ∀ j, raw8946 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw8946step0 = (fun i j => raw8946 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8946 permutation0 hz
    injectiveMoment H raw8946step0 = injectiveMoment H raw8946step1 := by
      have hz : ∀ i, raw8946step0 i (permutation2 0) = 0 := by decide +kernel
      have heq : raw8946step1 = (fun i j => raw8946step0 i (permutation2 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8946step0 permutation2 hz
    injectiveMoment H raw8946step1 = injectiveMoment H raw8946step2 := by
      have hz : ∀ i, raw8946step1 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw8946step2 = (fun i j => raw8946step1 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8946step1 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

def raw8947 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![0, 0], ![0, 0], ![3, -3]]

def raw8947step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![0, 0], ![3, -3]]

def raw8947step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![3, -3]]

def raw8947step2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]

theorem canonical8947 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8947 = injectiveMoment H node3 := by
  calc
    injectiveMoment H raw8947 = injectiveMoment H raw8947step0 := by
      have hz : ∀ j, raw8947 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw8947step0 = (fun i j => raw8947 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8947 permutation104 hz
    injectiveMoment H raw8947step0 = injectiveMoment H raw8947step1 := by
      have hz : ∀ j, raw8947step0 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw8947step1 = (fun i j => raw8947step0 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8947step0 permutation21 hz
    injectiveMoment H raw8947step1 = injectiveMoment H raw8947step2 := by
      have hz : ∀ j, raw8947step1 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw8947step2 = (fun i j => raw8947step1 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8947step1 permutation3 hz
    _ = injectiveMoment H node3 := by rfl

def raw8948 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![0, 0], ![2, -2], ![1, -1]]

def raw8948step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![2, -2], ![1, -1]]

def raw8948step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]

def raw8948step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical8948 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8948 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw8948 = injectiveMoment H raw8948step0 := by
      have hz : ∀ j, raw8948 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw8948step0 = (fun i j => raw8948 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8948 permutation80 hz
    injectiveMoment H raw8948step0 = injectiveMoment H raw8948step1 := by
      have hz : ∀ j, raw8948step0 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8948step1 = (fun i j => raw8948step0 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8948step0 permutation9 hz
    injectiveMoment H raw8948step1 = injectiveMoment H raw8948step2 := by
      have heq : raw8948step2 = (fun i j => raw8948step1 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8948step1 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

def raw8949 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![0, 0], ![0, 0], ![2, -2]]

def raw8949step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![0, 0], ![2, -2]]

def raw8949step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![2, -2]]

def raw8949step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical8949 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8949 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw8949 = injectiveMoment H raw8949step0 := by
      have hz : ∀ j, raw8949 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw8949step0 = (fun i j => raw8949 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8949 permutation258 hz
    injectiveMoment H raw8949step0 = injectiveMoment H raw8949step1 := by
      have hz : ∀ j, raw8949step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw8949step1 = (fun i j => raw8949step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8949step0 permutation104 hz
    injectiveMoment H raw8949step1 = injectiveMoment H raw8949step2 := by
      have hz : ∀ j, raw8949step1 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8949step2 = (fun i j => raw8949step1 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8949step1 permutation9 hz
    _ = injectiveMoment H node10 := by rfl

def raw8950 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![0, 0], ![2, -2]]

def raw8950step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![2, -2]]

def raw8950step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical8950 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8950 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw8950 = injectiveMoment H raw8950step0 := by
      have hz : ∀ j, raw8950 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw8950step0 = (fun i j => raw8950 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8950 permutation104 hz
    injectiveMoment H raw8950step0 = injectiveMoment H raw8950step1 := by
      have hz : ∀ j, raw8950step0 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8950step1 = (fun i j => raw8950step0 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8950step0 permutation9 hz
    _ = injectiveMoment H node10 := by rfl

def raw8951 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw8951step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical8951 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8951 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw8951 = injectiveMoment H raw8951step0 := by
      have hz : ∀ j, raw8951 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw8951step0 = (fun i j => raw8951 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8951 permutation33 hz
    _ = injectiveMoment H node26 := by rfl

def raw8952 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![1, -1], ![1, -1], ![0, 0]]

def raw8952step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def raw8952step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical8952 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8952 = injectiveMoment H node26 := by
  calc
    injectiveMoment H raw8952 = injectiveMoment H raw8952step0 := by
      have hz : ∀ j, raw8952 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw8952step0 = (fun i j => raw8952 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8952 permutation308 hz
    injectiveMoment H raw8952step0 = injectiveMoment H raw8952step1 := by
      have hz : ∀ j, raw8952step0 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw8952step1 = (fun i j => raw8952step0 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8952step0 permutation33 hz
    _ = injectiveMoment H node26 := by rfl

def raw8953 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![2, -2]]

def raw8953step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical8953 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8953 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw8953 = injectiveMoment H raw8953step0 := by
      have hz : ∀ j, raw8953 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8953step0 = (fun i j => raw8953 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8953 permutation9 hz
    _ = injectiveMoment H node10 := by rfl

def raw8954 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![2, -2], ![0, 0]]

def raw8954step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![2, -2]]

def raw8954step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical8954 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8954 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw8954 = injectiveMoment H raw8954step0 := by
      have hz : ∀ j, raw8954 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw8954step0 = (fun i j => raw8954 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8954 permutation128 hz
    injectiveMoment H raw8954step0 = injectiveMoment H raw8954step1 := by
      have hz : ∀ j, raw8954step0 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8954step1 = (fun i j => raw8954step0 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8954step0 permutation9 hz
    _ = injectiveMoment H node10 := by rfl

def raw8955 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![2, -2], ![1, -1]]

def raw8955step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]

def raw8955step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical8955 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8955 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw8955 = injectiveMoment H raw8955step0 := by
      have hz : ∀ j, raw8955 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8955step0 = (fun i j => raw8955 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8955 permutation9 hz
    injectiveMoment H raw8955step0 = injectiveMoment H raw8955step1 := by
      have heq : raw8955step1 = (fun i j => raw8955step0 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8955step0 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

def raw8956 : Matrix (Fin 3) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![3, -3]]

def raw8956step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]

theorem canonical8956 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8956 = injectiveMoment H node3 := by
  calc
    injectiveMoment H raw8956 = injectiveMoment H raw8956step0 := by
      have hz : ∀ j, raw8956 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw8956step0 = (fun i j => raw8956 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8956 permutation3 hz
    _ = injectiveMoment H node3 := by rfl

def raw8957 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![0, 0], ![0, 0], ![3, -3]]

def raw8957step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![0, 0], ![3, -3]]

def raw8957step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![3, -3]]

def raw8957step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]

def raw8957step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical8957 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8957 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw8957 = injectiveMoment H raw8957step0 := by
      have hz : ∀ j, raw8957 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw8957step0 = (fun i j => raw8957 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8957 permutation258 hz
    injectiveMoment H raw8957step0 = injectiveMoment H raw8957step1 := by
      have hz : ∀ j, raw8957step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw8957step1 = (fun i j => raw8957step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8957step0 permutation104 hz
    injectiveMoment H raw8957step1 = injectiveMoment H raw8957step2 := by
      have hz : ∀ j, raw8957step1 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8957step2 = (fun i j => raw8957step1 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8957step1 permutation9 hz
    injectiveMoment H raw8957step2 = injectiveMoment H raw8957step3 := by
      have heq : raw8957step3 = (fun i j => raw8957step2 (permutation8 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8957step2 permutation8 permutation2
    _ = injectiveMoment H node10 := by rfl

def raw8958 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![0, 0], ![2, -2], ![1, -1]]

def raw8958step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw8958step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]

def raw8958step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]

theorem canonical8958 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8958 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw8958 = injectiveMoment H raw8958step0 := by
      have hz : ∀ j, raw8958 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw8958step0 = (fun i j => raw8958 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8958 permutation241 hz
    injectiveMoment H raw8958step0 = injectiveMoment H raw8958step1 := by
      have hz : ∀ j, raw8958step0 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw8958step1 = (fun i j => raw8958step0 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8958step0 permutation33 hz
    injectiveMoment H raw8958step1 = injectiveMoment H raw8958step2 := by
      have heq : raw8958step2 = (fun i j => raw8958step1 (permutation10 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8958step1 permutation10 permutation1
    _ = injectiveMoment H node46 := by rfl

def raw8959 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![0, 0], ![3, -3]]

def raw8959step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![3, -3]]

def raw8959step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]

def raw8959step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

theorem canonical8959 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8959 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw8959 = injectiveMoment H raw8959step0 := by
      have hz : ∀ j, raw8959 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw8959step0 = (fun i j => raw8959 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8959 permutation104 hz
    injectiveMoment H raw8959step0 = injectiveMoment H raw8959step1 := by
      have hz : ∀ j, raw8959step0 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8959step1 = (fun i j => raw8959step0 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8959step0 permutation9 hz
    injectiveMoment H raw8959step1 = injectiveMoment H raw8959step2 := by
      have heq : raw8959step2 = (fun i j => raw8959step1 (permutation8 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8959step1 permutation8 permutation2
    _ = injectiveMoment H node10 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

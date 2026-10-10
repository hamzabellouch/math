import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3040 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, 0, -2], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw3040step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-2, 0, 2, 0], ![4, -2, -1, -1]]

def raw3040step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem canonical3040 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3040 = injectiveMoment H node773 := by
  calc
    injectiveMoment H raw3040 = injectiveMoment H raw3040step0 := by
      have heq : raw3040step0 = raw3040.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3040).symm
    injectiveMoment H raw3040step0 = injectiveMoment H raw3040step1 := by
      have heq : raw3040step1 = (fun i j => raw3040step0 (permutation32 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3040step0 permutation32 permutation30
    _ = injectiveMoment H node773 := by rfl

def raw3041 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, 0, -2], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def raw3041step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-2, 0, 3, -1], ![4, -2, -2, 0]]

def raw3041step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 4, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical3041 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3041 = injectiveMoment H node1194 := by
  calc
    injectiveMoment H raw3041 = injectiveMoment H raw3041step0 := by
      have heq : raw3041step0 = raw3041.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3041).symm
    injectiveMoment H raw3041step0 = injectiveMoment H raw3041step1 := by
      have heq : raw3041step1 = (fun i j => raw3041step0 (permutation26 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3041step0 permutation26 permutation29
    _ = injectiveMoment H node1194 := by rfl

def raw3042 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def raw3042step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![-2, 0, 0, 2], ![4, -2, 0, -2]]

def raw3042step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 1, 1], ![2, 0, 0, -2], ![-4, 2, 0, 2]]

def raw3042step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, 1, 0]]

theorem canonical3042 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3042 = injectiveMoment H node1257 := by
  calc
    injectiveMoment H raw3042 = injectiveMoment H raw3042step0 := by
      have heq : raw3042step0 = raw3042.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3042).symm
    injectiveMoment H raw3042step0 = injectiveMoment H raw3042step1 := by
      have heq : raw3042step1 = -raw3042step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3042step0).symm
    injectiveMoment H raw3042step1 = injectiveMoment H raw3042step2 := by
      have heq : raw3042step2 = (fun i j => raw3042step1 (permutation12 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3042step1 permutation12 permutation24
    _ = injectiveMoment H node1257 := by rfl

def raw3043 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def raw3043step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, -1, -1]]

theorem canonical3043 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3043 = injectiveMoment H node398 := by
  calc
    injectiveMoment H raw3043 = injectiveMoment H raw3043step0 := by
      have heq : raw3043step0 = (fun i j => raw3043 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3043 permutation9 permutation11
    _ = injectiveMoment H node398 := by rfl

def raw3044 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, -1, 0, 0]]

def raw3044step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![-2, 0, 2, 0], ![4, -2, -2, 0]]

def raw3044step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 1, 1], ![2, 0, -2, 0], ![-4, 2, 2, 0]]

def raw3044step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, 1, 0]]

theorem canonical3044 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3044 = injectiveMoment H node1257 := by
  calc
    injectiveMoment H raw3044 = injectiveMoment H raw3044step0 := by
      have heq : raw3044step0 = raw3044.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3044).symm
    injectiveMoment H raw3044step0 = injectiveMoment H raw3044step1 := by
      have heq : raw3044step1 = -raw3044step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3044step0).symm
    injectiveMoment H raw3044step1 = injectiveMoment H raw3044step2 := by
      have heq : raw3044step2 = (fun i j => raw3044step1 (permutation12 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3044step1 permutation12 permutation30
    _ = injectiveMoment H node1257 := by rfl

def raw3045 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, 1, -3], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def raw3045step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-2, 1, 2, -1], ![4, -3, -1, 0]]

def raw3045step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 2, 0], ![2, -1, -2, 1], ![-4, 3, 1, 0]]

def raw3045step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 3, -4], ![0, 2, -2, 0], ![1, -2, -1, 2]]

theorem canonical3045 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3045 = injectiveMoment H node1087 := by
  calc
    injectiveMoment H raw3045 = injectiveMoment H raw3045step0 := by
      have heq : raw3045step0 = raw3045.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3045).symm
    injectiveMoment H raw3045step0 = injectiveMoment H raw3045step1 := by
      have heq : raw3045step1 = -raw3045step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3045step0).symm
    injectiveMoment H raw3045step1 = injectiveMoment H raw3045step2 := by
      have heq : raw3045step2 = (fun i j => raw3045step1 (permutation13 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3045step1 permutation13 permutation32
    _ = injectiveMoment H node1087 := by rfl

def raw3046 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3046step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![-2, 1, 0, 1], ![4, -3, 0, -1]]

def raw3046step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 1, 1], ![2, -1, 0, -1], ![-4, 3, 0, 1]]

def raw3046step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

theorem canonical3046 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3046 = injectiveMoment H node996 := by
  calc
    injectiveMoment H raw3046 = injectiveMoment H raw3046step0 := by
      have heq : raw3046step0 = raw3046.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3046).symm
    injectiveMoment H raw3046step0 = injectiveMoment H raw3046step1 := by
      have heq : raw3046step1 = -raw3046step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3046step0).symm
    injectiveMoment H raw3046step1 = injectiveMoment H raw3046step2 := by
      have heq : raw3046step2 = (fun i j => raw3046step1 (permutation12 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3046step1 permutation12 permutation26
    _ = injectiveMoment H node996 := by rfl

def raw3047 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3047step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![-2, 2, 0, 0], ![4, -4, 0, 0]]

def raw3047step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 4, -4], ![1, 1, -2, 0]]

theorem canonical3047 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3047 = injectiveMoment H node1029 := by
  calc
    injectiveMoment H raw3047 = injectiveMoment H raw3047step0 := by
      have heq : raw3047step0 = raw3047.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3047).symm
    injectiveMoment H raw3047step0 = injectiveMoment H raw3047step1 := by
      have heq : raw3047step1 = (fun i j => raw3047step0 (permutation18 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3047step0 permutation18 permutation25
    _ = injectiveMoment H node1029 := by rfl

def raw3048 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![1, -2, 1, 0], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def raw3048step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem canonical3048 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3048 = injectiveMoment H node397 := by
  calc
    injectiveMoment H raw3048 = injectiveMoment H raw3048step0 := by
      have heq : raw3048step0 = (fun i j => raw3048 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3048 permutation11 permutation11
    _ = injectiveMoment H node397 := by rfl

def raw3049 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![1, -2, 2, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def raw3049step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 1, 1], ![-2, 2, 1, -1], ![4, -1, -2, -1]]

def raw3049step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, 2, -2], ![1, 1, -2, 0]]

theorem canonical3049 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3049 = injectiveMoment H node465 := by
  calc
    injectiveMoment H raw3049 = injectiveMoment H raw3049step0 := by
      have heq : raw3049step0 = raw3049.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3049).symm
    injectiveMoment H raw3049step0 = injectiveMoment H raw3049step1 := by
      have heq : raw3049step1 = (fun i j => raw3049step0 (permutation28 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3049step0 permutation28 permutation26
    _ = injectiveMoment H node465 := by rfl

def raw3050 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![1, -2, 2, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def raw3050step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![-2, 2, -1, 1], ![4, -1, -1, -2]]

def raw3050step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 2, -2], ![1, 0, 1, -2]]

theorem canonical3050 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3050 = injectiveMoment H node469 := by
  calc
    injectiveMoment H raw3050 = injectiveMoment H raw3050step0 := by
      have heq : raw3050step0 = raw3050.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3050).symm
    injectiveMoment H raw3050step0 = injectiveMoment H raw3050step1 := by
      have heq : raw3050step1 = (fun i j => raw3050step0 (permutation30 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3050step0 permutation30 permutation32
    _ = injectiveMoment H node469 := by rfl

def raw3051 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![1, -2, 3, -2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw3051step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -2, 2, 0], ![-2, 3, -1, 0], ![4, -2, -1, -1]]

def raw3051step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem canonical3051 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3051 = injectiveMoment H node901 := by
  calc
    injectiveMoment H raw3051 = injectiveMoment H raw3051step0 := by
      have heq : raw3051step0 = raw3051.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3051).symm
    injectiveMoment H raw3051step0 = injectiveMoment H raw3051step1 := by
      have heq : raw3051step1 = (fun i j => raw3051step0 (permutation32 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3051step0 permutation32 permutation32
    _ = injectiveMoment H node901 := by rfl

def raw3052 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![1, -1, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def raw3052step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, -1, -1]]

theorem canonical3052 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3052 = injectiveMoment H node398 := by
  calc
    injectiveMoment H raw3052 = injectiveMoment H raw3052step0 := by
      have heq : raw3052step0 = (fun i j => raw3052 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3052 permutation11 permutation11
    _ = injectiveMoment H node398 := by rfl

def raw3053 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![1, -1, 2, -2], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def raw3053step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem canonical3053 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3053 = injectiveMoment H node585 := by
  calc
    injectiveMoment H raw3053 = injectiveMoment H raw3053step0 := by
      have heq : raw3053step0 = (fun i j => raw3053 (permutation12 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3053 permutation12 permutation9
    _ = injectiveMoment H node585 := by rfl

def raw3054 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![1, -1, 3, -3], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw3054step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![-2, 3, -1, 0], ![4, -3, -1, 0]]

def raw3054step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, -2, 1], ![2, -3, 1, 0], ![-4, 3, 1, 0]]

def raw3054step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -2, 1, 0]]

theorem canonical3054 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3054 = injectiveMoment H node1275 := by
  calc
    injectiveMoment H raw3054 = injectiveMoment H raw3054step0 := by
      have heq : raw3054step0 = raw3054.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3054).symm
    injectiveMoment H raw3054step0 = injectiveMoment H raw3054step1 := by
      have heq : raw3054step1 = -raw3054step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3054step0).symm
    injectiveMoment H raw3054step1 = injectiveMoment H raw3054step2 := by
      have heq : raw3054step2 = (fun i j => raw3054step1 (permutation12 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3054step1 permutation12 permutation32
    _ = injectiveMoment H node1275 := by rfl

def raw3055 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

theorem canonical3055 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3055 = injectiveMoment H node1940 := by
  rfl

def raw3056 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![1, 0, -1, 0], ![1, 2, 1, -4]]

def raw3056step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![-1, 1, -1, 1], ![3, 1, 0, -4]]

def raw3056step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![-3, -1, 0, 4]]

def raw3056step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, -1, 1, -1]]

theorem canonical3056 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3056 = injectiveMoment H node1306 := by
  calc
    injectiveMoment H raw3056 = injectiveMoment H raw3056step0 := by
      have heq : raw3056step0 = raw3056.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3056).symm
    injectiveMoment H raw3056step0 = injectiveMoment H raw3056step1 := by
      have heq : raw3056step1 = -raw3056step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3056step0).symm
    injectiveMoment H raw3056step1 = injectiveMoment H raw3056step2 := by
      have heq : raw3056step2 = (fun i j => raw3056step1 (permutation13 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3056step1 permutation13 permutation23
    _ = injectiveMoment H node1306 := by rfl

def raw3057 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![1, 1, -2, 0], ![1, 1, 2, -4]]

theorem canonical3057 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3057 = injectiveMoment H node586 := by
  rfl

def raw3058 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def raw3058step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

theorem canonical3058 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3058 = injectiveMoment H node487 := by
  calc
    injectiveMoment H raw3058 = injectiveMoment H raw3058step0 := by
      have heq : raw3058step0 = (fun i j => raw3058 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3058 permutation9 permutation11
    _ = injectiveMoment H node487 := by rfl

def raw3059 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 2, 0], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw3059step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

theorem canonical3059 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3059 = injectiveMoment H node472 := by
  calc
    injectiveMoment H raw3059 = injectiveMoment H raw3059step0 := by
      have heq : raw3059step0 = (fun i j => raw3059 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3059 permutation11 permutation11
    _ = injectiveMoment H node472 := by rfl

def raw3060 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 2, 0], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw3060step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![-1, 2, 0, -1], ![3, 0, -2, -1]]

def raw3060step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

theorem canonical3060 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3060 = injectiveMoment H node474 := by
  calc
    injectiveMoment H raw3060 = injectiveMoment H raw3060step0 := by
      have heq : raw3060step0 = raw3060.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3060).symm
    injectiveMoment H raw3060step0 = injectiveMoment H raw3060step1 := by
      have heq : raw3060step1 = (fun i j => raw3060step0 (permutation31 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3060step0 permutation31 permutation26
    _ = injectiveMoment H node474 := by rfl

def raw3061 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw3061step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![-1, 2, -1, 0], ![3, 0, -1, -2]]

def raw3061step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem canonical3061 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3061 = injectiveMoment H node476 := by
  calc
    injectiveMoment H raw3061 = injectiveMoment H raw3061step0 := by
      have heq : raw3061step0 = raw3061.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3061).symm
    injectiveMoment H raw3061step0 = injectiveMoment H raw3061step1 := by
      have heq : raw3061step1 = (fun i j => raw3061step0 (permutation32 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3061step0 permutation32 permutation32
    _ = injectiveMoment H node476 := by rfl

def raw3062 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, -1, 2], ![0, 0, 2, -2], ![2, 1, 0, -3]]

def raw3062step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, 1, -2], ![0, 0, -2, 2], ![-2, -1, 0, 3]]

def raw3062step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 1, -2]]

theorem canonical3062 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3062 = injectiveMoment H node794 := by
  calc
    injectiveMoment H raw3062 = injectiveMoment H raw3062step0 := by
      have heq : raw3062step0 = -raw3062 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3062).symm
    injectiveMoment H raw3062step0 = injectiveMoment H raw3062step1 := by
      have heq : raw3062step1 = (fun i j => raw3062step0 (permutation31 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3062step0 permutation31 permutation15
    _ = injectiveMoment H node794 := by rfl

def raw3063 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, -1, 2], ![0, 1, 2, -3], ![2, 0, 0, -2]]

def raw3063step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, 1, -2], ![0, -1, -2, 3], ![-2, 0, 0, 2]]

def raw3063step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, 1, 0, -2]]

theorem canonical3063 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3063 = injectiveMoment H node791 := by
  calc
    injectiveMoment H raw3063 = injectiveMoment H raw3063step0 := by
      have heq : raw3063step0 = -raw3063 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3063).symm
    injectiveMoment H raw3063step0 = injectiveMoment H raw3063step1 := by
      have heq : raw3063step1 = (fun i j => raw3063step0 (permutation25 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3063step0 permutation25 permutation17
    _ = injectiveMoment H node791 := by rfl

def raw3064 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 0, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3064step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![-1, 0, -1, 2], ![3, 1, 0, -4]]

def raw3064step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![-3, -1, 0, 4]]

def raw3064step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical3064 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3064 = injectiveMoment H node1171 := by
  calc
    injectiveMoment H raw3064 = injectiveMoment H raw3064step0 := by
      have heq : raw3064step0 = raw3064.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3064).symm
    injectiveMoment H raw3064step0 = injectiveMoment H raw3064step1 := by
      have heq : raw3064step1 = -raw3064step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3064step0).symm
    injectiveMoment H raw3064step1 = injectiveMoment H raw3064step2 := by
      have heq : raw3064step2 = (fun i j => raw3064step1 (permutation28 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3064step1 permutation28 permutation17
    _ = injectiveMoment H node1171 := by rfl

def raw3065 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw3065step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -1, 0], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![-1, -1, -2, 4]]

def raw3065step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical3065 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3065 = injectiveMoment H node2492 := by
  calc
    injectiveMoment H raw3065 = injectiveMoment H raw3065step0 := by
      have heq : raw3065step0 = -raw3065 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3065).symm
    injectiveMoment H raw3065step0 = injectiveMoment H raw3065step1 := by
      have heq : raw3065step1 = (fun i j => raw3065step0 (permutation149 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3065step0 permutation149 permutation15
    _ = injectiveMoment H node2492 := by rfl

def raw3066 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

theorem canonical3066 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3066 = injectiveMoment H node1941 := by
  rfl

def raw3067 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw3067step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 3, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical3067 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3067 = injectiveMoment H node2746 := by
  calc
    injectiveMoment H raw3067 = injectiveMoment H raw3067step0 := by
      have heq : raw3067step0 = (fun i j => raw3067 (permutation62 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3067 permutation62 permutation16
    _ = injectiveMoment H node2746 := by rfl

def raw3068 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def raw3068step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem canonical3068 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3068 = injectiveMoment H node1643 := by
  calc
    injectiveMoment H raw3068 = injectiveMoment H raw3068step0 := by
      have heq : raw3068step0 = (fun i j => raw3068 (permutation39 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3068 permutation39 permutation11
    _ = injectiveMoment H node1643 := by rfl

def raw3069 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

theorem canonical3069 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3069 = injectiveMoment H node1942 := by
  rfl

def raw3070 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw3070step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 3, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical3070 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3070 = injectiveMoment H node2719 := by
  calc
    injectiveMoment H raw3070 = injectiveMoment H raw3070step0 := by
      have heq : raw3070step0 = (fun i j => raw3070 (permutation62 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3070 permutation62 permutation16
    _ = injectiveMoment H node2719 := by rfl

def raw3071 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw3071step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 1, -3], ![0, 1, -2, 1], ![0, -1, 1, 0], ![-1, 0, 0, 1], ![-1, 0, 0, 1]]

def raw3071step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical3071 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3071 = injectiveMoment H node2812 := by
  calc
    injectiveMoment H raw3071 = injectiveMoment H raw3071step0 := by
      have heq : raw3071step0 = -raw3071 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3071).symm
    injectiveMoment H raw3071step0 = injectiveMoment H raw3071step1 := by
      have heq : raw3071step1 = (fun i j => raw3071step0 (permutation96 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3071step0 permutation96 permutation15
    _ = injectiveMoment H node2812 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

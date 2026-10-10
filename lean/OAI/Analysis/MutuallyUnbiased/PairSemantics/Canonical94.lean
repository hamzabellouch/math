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
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3008 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw3008step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-2, 0, 0, 2], ![4, -1, -1, -2]]

def raw3008step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 0, 2, -2], ![1, 1, -2, 0]]

theorem canonical3008 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3008 = injectiveMoment H node912 := by
  calc
    injectiveMoment H raw3008 = injectiveMoment H raw3008step0 := by
      have heq : raw3008step0 = raw3008.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3008).symm
    injectiveMoment H raw3008step0 = injectiveMoment H raw3008step1 := by
      have heq : raw3008step1 = (fun i j => raw3008step0 (permutation28 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3008step0 permutation28 permutation18
    _ = injectiveMoment H node912 := by rfl

def raw3009 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def raw3009step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-2, 0, 1, 1], ![4, -1, -2, -1]]

def raw3009step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical3009 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3009 = injectiveMoment H node772 := by
  calc
    injectiveMoment H raw3009 = injectiveMoment H raw3009step0 := by
      have heq : raw3009step0 = raw3009.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3009).symm
    injectiveMoment H raw3009step0 = injectiveMoment H raw3009step1 := by
      have heq : raw3009step1 = (fun i j => raw3009step0 (permutation28 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3009step0 permutation28 permutation18
    _ = injectiveMoment H node772 := by rfl

def raw3010 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3010step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 1, -3]]

theorem canonical3010 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3010 = injectiveMoment H node1467 := by
  calc
    injectiveMoment H raw3010 = injectiveMoment H raw3010step0 := by
      have heq : raw3010step0 = (fun i j => raw3010 (permutation36 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3010 permutation36 permutation21
    _ = injectiveMoment H node1467 := by rfl

def raw3011 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![0, 1, 2, -3], ![2, -2, 0, 0]]

def raw3011step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-2, 0, 2, 0], ![4, -1, -3, 0]]

def raw3011step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -2, 1, 0]]

theorem canonical3011 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3011 = injectiveMoment H node1180 := by
  calc
    injectiveMoment H raw3011 = injectiveMoment H raw3011step0 := by
      have heq : raw3011step0 = raw3011.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3011).symm
    injectiveMoment H raw3011step0 = injectiveMoment H raw3011step1 := by
      have heq : raw3011step1 = (fun i j => raw3011step0 (permutation31 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3011step0 permutation31 permutation20
    _ = injectiveMoment H node1180 := by rfl

def raw3012 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 1, 0, -2]]

def raw3012step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![-2, 0, 2, 0], ![4, -1, -1, -2]]

def raw3012step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical3012 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3012 = injectiveMoment H node772 := by
  calc
    injectiveMoment H raw3012 = injectiveMoment H raw3012step0 := by
      have heq : raw3012step0 = raw3012.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3012).symm
    injectiveMoment H raw3012step0 = injectiveMoment H raw3012step1 := by
      have heq : raw3012step1 = (fun i j => raw3012step0 (permutation31 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3012step0 permutation31 permutation20
    _ = injectiveMoment H node772 := by rfl

def raw3013 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 1, -1, -1]]

def raw3013step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![-2, 0, 3, -1], ![4, -1, -2, -1]]

def raw3013step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical3013 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3013 = injectiveMoment H node900 := by
  calc
    injectiveMoment H raw3013 = injectiveMoment H raw3013step0 := by
      have heq : raw3013step0 = raw3013.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3013).symm
    injectiveMoment H raw3013step0 = injectiveMoment H raw3013step1 := by
      have heq : raw3013step1 = (fun i j => raw3013step0 (permutation31 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3013step0 permutation31 permutation20
    _ = injectiveMoment H node900 := by rfl

def raw3014 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw3014step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-2, 0, 0, 2], ![4, -1, 0, -3]]

def raw3014step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem canonical3014 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3014 = injectiveMoment H node1178 := by
  calc
    injectiveMoment H raw3014 = injectiveMoment H raw3014step0 := by
      have heq : raw3014step0 = raw3014.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3014).symm
    injectiveMoment H raw3014step0 = injectiveMoment H raw3014step1 := by
      have heq : raw3014step1 = (fun i j => raw3014step0 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3014step0 permutation31 permutation18
    _ = injectiveMoment H node1178 := by rfl

def raw3015 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def raw3015step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![4, -1, -1, -2]]

def raw3015step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical3015 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3015 = injectiveMoment H node787 := by
  calc
    injectiveMoment H raw3015 = injectiveMoment H raw3015step0 := by
      have heq : raw3015step0 = raw3015.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3015).symm
    injectiveMoment H raw3015step0 = injectiveMoment H raw3015step1 := by
      have heq : raw3015step1 = (fun i j => raw3015step0 (permutation28 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3015step0 permutation28 permutation20
    _ = injectiveMoment H node787 := by rfl

def raw3016 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def raw3016step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-2, 0, 2, 0], ![4, -1, -2, -1]]

def raw3016step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical3016 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3016 = injectiveMoment H node914 := by
  calc
    injectiveMoment H raw3016 = injectiveMoment H raw3016step0 := by
      have heq : raw3016step0 = raw3016.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3016).symm
    injectiveMoment H raw3016step0 = injectiveMoment H raw3016step1 := by
      have heq : raw3016step1 = (fun i j => raw3016step0 (permutation32 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3016step0 permutation32 permutation30
    _ = injectiveMoment H node914 := by rfl

def raw3017 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -1, 3, -3]]

def raw3017step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![4, -1, 0, -3]]

def raw3017step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 3, -2], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical3017 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3017 = injectiveMoment H node1174 := by
  calc
    injectiveMoment H raw3017 = injectiveMoment H raw3017step0 := by
      have heq : raw3017step0 = raw3017.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3017).symm
    injectiveMoment H raw3017step0 = injectiveMoment H raw3017step1 := by
      have heq : raw3017step1 = (fun i j => raw3017step0 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3017step0 permutation31 permutation18
    _ = injectiveMoment H node1174 := by rfl

def raw3018 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, -1, 2, -2]]

def raw3018step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![4, -1, -1, -2]]

def raw3018step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical3018 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3018 = injectiveMoment H node914 := by
  calc
    injectiveMoment H raw3018 = injectiveMoment H raw3018step0 := by
      have heq : raw3018step0 = raw3018.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3018).symm
    injectiveMoment H raw3018step0 = injectiveMoment H raw3018step1 := by
      have heq : raw3018step1 = (fun i j => raw3018step0 (permutation32 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3018step0 permutation32 permutation24
    _ = injectiveMoment H node914 := by rfl

def raw3019 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 1, -2], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def raw3019step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-2, 1, 0, 1], ![4, -2, -1, -1]]

def raw3019step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical3019 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3019 = injectiveMoment H node772 := by
  calc
    injectiveMoment H raw3019 = injectiveMoment H raw3019step0 := by
      have heq : raw3019step0 = raw3019.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3019).symm
    injectiveMoment H raw3019step0 = injectiveMoment H raw3019step1 := by
      have heq : raw3019step1 = (fun i j => raw3019step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3019step0 permutation28 permutation24
    _ = injectiveMoment H node772 := by rfl

def raw3020 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3020step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 0, 1, -2]]

theorem canonical3020 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3020 = injectiveMoment H node1485 := by
  calc
    injectiveMoment H raw3020 = injectiveMoment H raw3020step0 := by
      have heq : raw3020step0 = (fun i j => raw3020 (permutation49 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3020 permutation49 permutation21
    _ = injectiveMoment H node1485 := by rfl

def raw3021 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def raw3021step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![-2, 1, 1, 0], ![4, -2, -2, 0]]

def raw3021step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem canonical3021 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3021 = injectiveMoment H node397 := by
  calc
    injectiveMoment H raw3021 = injectiveMoment H raw3021step0 := by
      have heq : raw3021step0 = raw3021.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3021).symm
    injectiveMoment H raw3021step0 = injectiveMoment H raw3021step1 := by
      have heq : raw3021step1 = (fun i j => raw3021step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3021step0 permutation27 permutation18
    _ = injectiveMoment H node397 := by rfl

def raw3022 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 1, 0, -2]]

def raw3022step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 1, -2], ![1, 0, 1, -2], ![1, 1, -2, 0]]

theorem canonical3022 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3022 = injectiveMoment H node404 := by
  calc
    injectiveMoment H raw3022 = injectiveMoment H raw3022step0 := by
      have heq : raw3022step0 = (fun i j => raw3022 (permutation10 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3022 permutation10 permutation11
    _ = injectiveMoment H node404 := by rfl

def raw3023 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def raw3023step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![-2, 1, 2, -1], ![4, -2, -1, -1]]

def raw3023step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, 2, -2], ![1, 1, -2, 0]]

theorem canonical3023 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3023 = injectiveMoment H node465 := by
  calc
    injectiveMoment H raw3023 = injectiveMoment H raw3023step0 := by
      have heq : raw3023step0 = raw3023.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3023).symm
    injectiveMoment H raw3023step0 = injectiveMoment H raw3023step1 := by
      have heq : raw3023step1 = (fun i j => raw3023step0 (permutation28 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3023step0 permutation28 permutation20
    _ = injectiveMoment H node465 := by rfl

def raw3024 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw3024step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, -1, -1, 2], ![-1, 1, 0, 0], ![-1, 0, -1, 2]]

def raw3024step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical3024 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3024 = injectiveMoment H node998 := by
  calc
    injectiveMoment H raw3024 = injectiveMoment H raw3024step0 := by
      have heq : raw3024step0 = -raw3024 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3024).symm
    injectiveMoment H raw3024step0 = injectiveMoment H raw3024step1 := by
      have heq : raw3024step1 = (fun i j => raw3024step0 (permutation19 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3024step0 permutation19 permutation17
    _ = injectiveMoment H node998 := by rfl

def raw3025 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 1, -2], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw3025step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, -1, -1, 2], ![-1, 1, -2, 2], ![-1, 0, 1, 0]]

def raw3025step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 2, 2, -4], ![1, -1, -2, 2]]

theorem canonical3025 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3025 = injectiveMoment H node1243 := by
  calc
    injectiveMoment H raw3025 = injectiveMoment H raw3025step0 := by
      have heq : raw3025step0 = -raw3025 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3025).symm
    injectiveMoment H raw3025step0 = injectiveMoment H raw3025step1 := by
      have heq : raw3025step1 = (fun i j => raw3025step0 (permutation19 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3025step0 permutation19 permutation15
    _ = injectiveMoment H node1243 := by rfl

def raw3026 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, -1, 2, -2]]

def raw3026step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 2, -4], ![0, -1, -1, 2], ![-1, 0, 1, 0], ![-1, 1, -2, 2]]

def raw3026step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 2, 2, -4], ![1, -1, -2, 2]]

theorem canonical3026 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3026 = injectiveMoment H node1243 := by
  calc
    injectiveMoment H raw3026 = injectiveMoment H raw3026step0 := by
      have heq : raw3026step0 = -raw3026 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3026).symm
    injectiveMoment H raw3026step0 = injectiveMoment H raw3026step1 := by
      have heq : raw3026step1 = (fun i j => raw3026step0 (permutation17 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3026step0 permutation17 permutation15
    _ = injectiveMoment H node1243 := by rfl

def raw3027 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 1, -1, -1]]

theorem canonical3027 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3027 = injectiveMoment H node583 := by
  rfl

def raw3028 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw3028step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-2, 2, 0, 0], ![4, -3, 0, -1]]

def raw3028step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![2, -2, 0, 0], ![-4, 3, 0, 1]]

def raw3028step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 3, -4]]

theorem canonical3028 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3028 = injectiveMoment H node1031 := by
  calc
    injectiveMoment H raw3028 = injectiveMoment H raw3028step0 := by
      have heq : raw3028step0 = raw3028.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3028).symm
    injectiveMoment H raw3028step0 = injectiveMoment H raw3028step1 := by
      have heq : raw3028step1 = -raw3028step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3028step0).symm
    injectiveMoment H raw3028step1 = injectiveMoment H raw3028step2 := by
      have heq : raw3028step2 = (fun i j => raw3028step1 (permutation11 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3028step1 permutation11 permutation32
    _ = injectiveMoment H node1031 := by rfl

def raw3029 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw3029step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-2, 2, 1, -1], ![4, -3, -1, 0]]

def raw3029step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![2, -2, -1, 1], ![-4, 3, 1, 0]]

def raw3029step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -2, 2]]

theorem canonical3029 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3029 = injectiveMoment H node1082 := by
  calc
    injectiveMoment H raw3029 = injectiveMoment H raw3029step0 := by
      have heq : raw3029step0 = raw3029.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3029).symm
    injectiveMoment H raw3029step0 = injectiveMoment H raw3029step1 := by
      have heq : raw3029step1 = -raw3029step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3029step0).symm
    injectiveMoment H raw3029step1 = injectiveMoment H raw3029step2 := by
      have heq : raw3029step2 = (fun i j => raw3029step1 (permutation10 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3029step1 permutation10 permutation32
    _ = injectiveMoment H node1082 := by rfl

def raw3030 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, -1, 1, -1]]

def raw3030step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![-2, 2, -1, 1], ![4, -3, 0, -1]]

def raw3030step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 0, 1], ![2, -2, 1, -1], ![-4, 3, 0, 1]]

def raw3030step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -2, 2]]

theorem canonical3030 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3030 = injectiveMoment H node1082 := by
  calc
    injectiveMoment H raw3030 = injectiveMoment H raw3030step0 := by
      have heq : raw3030step0 = raw3030.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3030).symm
    injectiveMoment H raw3030step0 = injectiveMoment H raw3030step1 := by
      have heq : raw3030step1 = -raw3030step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3030step0).symm
    injectiveMoment H raw3030step1 = injectiveMoment H raw3030step2 := by
      have heq : raw3030step2 = (fun i j => raw3030step1 (permutation10 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3030step1 permutation10 permutation26
    _ = injectiveMoment H node1082 := by rfl

def raw3031 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3031step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![-2, 3, 0, -1], ![4, -4, 0, 0]]

def raw3031step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 1, 0], ![2, -3, 0, 1], ![-4, 4, 0, 0]]

def raw3031step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 4, -4], ![0, 1, -3, 2], ![1, 0, -1, 0]]

theorem canonical3031 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3031 = injectiveMoment H node1069 := by
  calc
    injectiveMoment H raw3031 = injectiveMoment H raw3031step0 := by
      have heq : raw3031step0 = raw3031.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3031).symm
    injectiveMoment H raw3031step0 = injectiveMoment H raw3031step1 := by
      have heq : raw3031step1 = -raw3031step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3031step0).symm
    injectiveMoment H raw3031step1 = injectiveMoment H raw3031step2 := by
      have heq : raw3031step2 = (fun i j => raw3031step1 (permutation14 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3031step1 permutation14 permutation26
    _ = injectiveMoment H node1069 := by rfl

def raw3032 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw3032step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![-2, 3, -1, 0], ![4, -4, 0, 0]]

def raw3032step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 0, 1], ![2, -3, 1, 0], ![-4, 4, 0, 0]]

def raw3032step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 4, -4], ![0, 1, -3, 2], ![1, 0, -1, 0]]

theorem canonical3032 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3032 = injectiveMoment H node1069 := by
  calc
    injectiveMoment H raw3032 = injectiveMoment H raw3032step0 := by
      have heq : raw3032step0 = raw3032.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3032).symm
    injectiveMoment H raw3032step0 = injectiveMoment H raw3032step1 := by
      have heq : raw3032step1 = -raw3032step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3032step0).symm
    injectiveMoment H raw3032step1 = injectiveMoment H raw3032step2 := by
      have heq : raw3032step2 = (fun i j => raw3032step1 (permutation14 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3032step1 permutation14 permutation32
    _ = injectiveMoment H node1069 := by rfl

def raw3033 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 0, 2, -3]]

theorem canonical3033 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3033 = injectiveMoment H node584 := by
  rfl

def raw3034 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw3034step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-2, -1, 2, 1], ![4, -1, -1, -2]]

def raw3034step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 2, -2], ![1, 0, 1, -2]]

theorem canonical3034 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3034 = injectiveMoment H node469 := by
  calc
    injectiveMoment H raw3034 = injectiveMoment H raw3034step0 := by
      have heq : raw3034step0 = raw3034.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3034).symm
    injectiveMoment H raw3034step0 = injectiveMoment H raw3034step1 := by
      have heq : raw3034step1 = (fun i j => raw3034step0 (permutation30 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3034step0 permutation30 permutation30
    _ = injectiveMoment H node469 := by rfl

def raw3035 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw3035step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![-2, -1, 3, 0], ![4, -1, -2, -1]]

def raw3035step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem canonical3035 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3035 = injectiveMoment H node901 := by
  calc
    injectiveMoment H raw3035 = injectiveMoment H raw3035step0 := by
      have heq : raw3035step0 = raw3035.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3035).symm
    injectiveMoment H raw3035step0 = injectiveMoment H raw3035step1 := by
      have heq : raw3035step1 = (fun i j => raw3035step0 (permutation32 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3035step0 permutation32 permutation30
    _ = injectiveMoment H node901 := by rfl

def raw3036 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw3036step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![-2, -1, 0, 3], ![4, -1, 0, -3]]

def raw3036step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 1, 1], ![2, 1, 0, -3], ![-4, 1, 0, 3]]

def raw3036step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -2, 1, 0]]

theorem canonical3036 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3036 = injectiveMoment H node1275 := by
  calc
    injectiveMoment H raw3036 = injectiveMoment H raw3036step0 := by
      have heq : raw3036step0 = raw3036.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3036).symm
    injectiveMoment H raw3036step0 = injectiveMoment H raw3036step1 := by
      have heq : raw3036step1 = -raw3036step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3036step0).symm
    injectiveMoment H raw3036step1 = injectiveMoment H raw3036step2 := by
      have heq : raw3036step2 = (fun i j => raw3036step1 (permutation12 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3036step1 permutation12 permutation24
    _ = injectiveMoment H node1275 := by rfl

def raw3037 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem canonical3037 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3037 = injectiveMoment H node585 := by
  rfl

def raw3038 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 2, -2], ![1, -1, 1, -1]]

def raw3038step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem canonical3038 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3038 = injectiveMoment H node585 := by
  calc
    injectiveMoment H raw3038 = injectiveMoment H raw3038step0 := by
      have heq : raw3038step0 = (fun i j => raw3038 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3038 permutation10 permutation9
    _ = injectiveMoment H node585 := by rfl

def raw3039 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, 0, -2], ![1, -2, 1, 0], ![1, 0, 1, -2]]

def raw3039step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem canonical3039 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3039 = injectiveMoment H node397 := by
  calc
    injectiveMoment H raw3039 = injectiveMoment H raw3039step0 := by
      have heq : raw3039step0 = (fun i j => raw3039 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3039 permutation9 permutation11
    _ = injectiveMoment H node397 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

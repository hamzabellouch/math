import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3840 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, -3, 2]]

def raw3840step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, -1, 2], ![-1, 1, -1, 1], ![-1, 0, 3, -2]]

def raw3840step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem canonical3840 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3840 = injectiveMoment H node1249 := by
  calc
    injectiveMoment H raw3840 = injectiveMoment H raw3840step0 := by
      have heq : raw3840step0 = -raw3840 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3840).symm
    injectiveMoment H raw3840step0 = injectiveMoment H raw3840step1 := by
      have heq : raw3840step1 = (fun i j => raw3840step0 (permutation19 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3840step0 permutation19 permutation15
    _ = injectiveMoment H node1249 := by rfl

def raw3841 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 2, -3], ![1, -2, 0, 1], ![1, 1, -3, 1]]

def raw3841step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -2, 1, 0], ![1, 1, 1, -3]]

theorem canonical3841 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3841 = injectiveMoment H node616 := by
  calc
    injectiveMoment H raw3841 = injectiveMoment H raw3841step0 := by
      have heq : raw3841step0 = (fun i j => raw3841 (permutation9 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3841 permutation9 permutation10
    _ = injectiveMoment H node616 := by rfl

def raw3842 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -3, 2]]

def raw3842step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, -2, 3], ![-1, 1, 0, 0], ![-1, 0, 3, -2]]

def raw3842step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, 0, 0]]

theorem canonical3842 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3842 = injectiveMoment H node1214 := by
  calc
    injectiveMoment H raw3842 = injectiveMoment H raw3842step0 := by
      have heq : raw3842step0 = -raw3842 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3842).symm
    injectiveMoment H raw3842step0 = injectiveMoment H raw3842step1 := by
      have heq : raw3842step1 = (fun i j => raw3842step0 (permutation19 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3842step0 permutation19 permutation15
    _ = injectiveMoment H node1214 := by rfl

def raw3843 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -4, 2], ![2, -2, 3, -3]]

def raw3843step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -4, 3], ![1, 2, -3]]

theorem canonical3843 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3843 = injectiveMoment H node211 := by
  calc
    injectiveMoment H raw3843 = injectiveMoment H raw3843step0 := by
      have heq : raw3843step0 = raw3843.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3843).symm
    _ = injectiveMoment H node211 := by rfl

def raw3844 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -3, 1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw3844step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![1, -3, 2, 0], ![1, 1, -1, -1]]

def raw3844step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem canonical3844 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3844 = injectiveMoment H node1347 := by
  calc
    injectiveMoment H raw3844 = injectiveMoment H raw3844step0 := by
      have heq : raw3844step0 = raw3844.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3844).symm
    injectiveMoment H raw3844step0 = injectiveMoment H raw3844step1 := by
      have heq : raw3844step1 = (fun i j => raw3844step0 (permutation30 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3844step0 permutation30 permutation28
    _ = injectiveMoment H node1347 := by rfl

def raw3845 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -3, 1], ![2, -2, 2, -2]]

def raw3845step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

theorem canonical3845 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3845 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw3845 = injectiveMoment H raw3845step0 := by
      have heq : raw3845step0 = raw3845.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3845).symm
    _ = injectiveMoment H node212 := by rfl

def raw3846 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3846step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![1, -2, 0, 1], ![1, 0, 0, -1]]

def raw3846step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical3846 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3846 = injectiveMoment H node1000 := by
  calc
    injectiveMoment H raw3846 = injectiveMoment H raw3846step0 := by
      have heq : raw3846step0 = raw3846.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3846).symm
    injectiveMoment H raw3846step0 = injectiveMoment H raw3846step1 := by
      have heq : raw3846step1 = (fun i j => raw3846step0 (permutation20 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3846step0 permutation20 permutation25
    _ = injectiveMoment H node1000 := by rfl

def raw3847 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![2, -2, 1, -1]]

def raw3847step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def raw3847step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]

def raw3847step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical3847 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3847 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw3847 = injectiveMoment H raw3847step0 := by
      have heq : raw3847step0 = raw3847.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3847).symm
    injectiveMoment H raw3847step0 = injectiveMoment H raw3847step1 := by
      have heq : raw3847step1 = -raw3847step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3847step0).symm
    injectiveMoment H raw3847step1 = injectiveMoment H raw3847step2 := by
      have heq : raw3847step2 = (fun i j => raw3847step1 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3847step1 permutation19 permutation5
    _ = injectiveMoment H node203 := by rfl

def raw3848 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def raw3848step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical3848 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3848 = injectiveMoment H node1000 := by
  calc
    injectiveMoment H raw3848 = injectiveMoment H raw3848step0 := by
      have heq : raw3848step0 = (fun i j => raw3848 (permutation20 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3848 permutation20 permutation31
    _ = injectiveMoment H node1000 := by rfl

def raw3849 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

theorem canonical3849 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3849 = injectiveMoment H node621 := by
  rfl

def raw3850 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3850step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, -2, 0]]

theorem canonical3850 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3850 = injectiveMoment H node1045 := by
  calc
    injectiveMoment H raw3850 = injectiveMoment H raw3850step0 := by
      have heq : raw3850step0 = (fun i j => raw3850 (permutation18 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3850 permutation18 permutation25
    _ = injectiveMoment H node1045 := by rfl

def raw3851 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, -1, 1]]

def raw3851step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

theorem canonical3851 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3851 = injectiveMoment H node621 := by
  calc
    injectiveMoment H raw3851 = injectiveMoment H raw3851step0 := by
      have heq : raw3851step0 = (fun i j => raw3851 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3851 permutation10 permutation9
    _ = injectiveMoment H node621 := by rfl

def raw3852 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 3, -4, 1], ![2, -3, 3, -2]]

def raw3852step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -4, 3], ![1, 1, -2]]

theorem canonical3852 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3852 = injectiveMoment H node213 := by
  calc
    injectiveMoment H raw3852 = injectiveMoment H raw3852step0 := by
      have heq : raw3852step0 = raw3852.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3852).symm
    _ = injectiveMoment H node213 := by rfl

def raw3853 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 3, -2, -1], ![2, -3, 1, 0]]

def raw3853step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

theorem canonical3853 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3853 = injectiveMoment H node215 := by
  calc
    injectiveMoment H raw3853 = injectiveMoment H raw3853step0 := by
      have heq : raw3853step0 = raw3853.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3853).symm
    _ = injectiveMoment H node215 := by rfl

def raw3854 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 4, -2, -2], ![2, -4, 1, 1]]

def raw3854step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -2, 1], ![1, -2, 1]]

theorem canonical3854 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3854 = injectiveMoment H node218 := by
  calc
    injectiveMoment H raw3854 = injectiveMoment H raw3854step0 := by
      have heq : raw3854step0 = raw3854.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3854).symm
    _ = injectiveMoment H node218 := by rfl

def raw3855 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -3, 1, 1], ![1, 3, -2, -2]]

def raw3855step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

theorem canonical3855 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3855 = injectiveMoment H node223 := by
  calc
    injectiveMoment H raw3855 = injectiveMoment H raw3855step0 := by
      have heq : raw3855step0 = raw3855.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3855).symm
    _ = injectiveMoment H node223 := by rfl

def raw3856 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, -2, 3], ![1, 2, 1, -4]]

def raw3856step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

theorem canonical3856 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3856 = injectiveMoment H node225 := by
  calc
    injectiveMoment H raw3856 = injectiveMoment H raw3856step0 := by
      have heq : raw3856step0 = raw3856.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3856).symm
    _ = injectiveMoment H node225 := by rfl

def raw3857 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, -1, 2], ![0, 1, -2, 1], ![1, 1, 2, -4]]

def raw3857step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, -1, 2], ![1, 1, 2, -4]]

theorem canonical3857 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3857 = injectiveMoment H node618 := by
  calc
    injectiveMoment H raw3857 = injectiveMoment H raw3857step0 := by
      have heq : raw3857step0 = (fun i j => raw3857 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3857 permutation11 permutation9
    _ = injectiveMoment H node618 := by rfl

def raw3858 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, 1, 0], ![1, 2, -2, -1]]

def raw3858step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]

def raw3858step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical3858 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3858 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw3858 = injectiveMoment H raw3858step0 := by
      have heq : raw3858step0 = raw3858.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3858).symm
    injectiveMoment H raw3858step0 = injectiveMoment H raw3858step1 := by
      have heq : raw3858step1 = (fun i j => raw3858step0 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3858step0 permutation19 permutation5
    _ = injectiveMoment H node210 := by rfl

def raw3859 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, 2, -1], ![1, 2, -3, 0]]

def raw3859step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]

def raw3859step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

theorem canonical3859 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3859 = injectiveMoment H node226 := by
  calc
    injectiveMoment H raw3859 = injectiveMoment H raw3859step0 := by
      have heq : raw3859step0 = raw3859.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3859).symm
    injectiveMoment H raw3859step0 = injectiveMoment H raw3859step1 := by
      have heq : raw3859step1 = (fun i j => raw3859step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3859step0 permutation10 permutation3
    _ = injectiveMoment H node226 := by rfl

def raw3860 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, 3, -2], ![1, 2, -4, 1]]

def raw3860step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 3, -4], ![1, -2, 1]]

def raw3860step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

theorem canonical3860 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3860 = injectiveMoment H node225 := by
  calc
    injectiveMoment H raw3860 = injectiveMoment H raw3860step0 := by
      have heq : raw3860step0 = raw3860.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3860).symm
    injectiveMoment H raw3860step0 = injectiveMoment H raw3860step1 := by
      have heq : raw3860step1 = (fun i j => raw3860step0 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3860step0 permutation10 permutation3
    _ = injectiveMoment H node225 := by rfl

def raw3861 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def raw3861step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![0, -1, -1, 2], ![-1, 1, 0, 0]]

def raw3861step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical3861 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3861 = injectiveMoment H node1009 := by
  calc
    injectiveMoment H raw3861 = injectiveMoment H raw3861step0 := by
      have heq : raw3861step0 = -raw3861 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3861).symm
    injectiveMoment H raw3861step0 = injectiveMoment H raw3861step1 := by
      have heq : raw3861step1 = (fun i j => raw3861step0 (permutation21 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3861step0 permutation21 permutation17
    _ = injectiveMoment H node1009 := by rfl

def raw3862 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 2, -3, 0], ![1, -2, 2, -1]]

def raw3862step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

def raw3862step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

theorem canonical3862 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3862 = injectiveMoment H node226 := by
  calc
    injectiveMoment H raw3862 = injectiveMoment H raw3862step0 := by
      have heq : raw3862step0 = raw3862.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3862).symm
    injectiveMoment H raw3862step0 = injectiveMoment H raw3862step1 := by
      have heq : raw3862step1 = (fun i j => raw3862step0 (permutation10 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3862step0 permutation10 permutation4
    _ = injectiveMoment H node226 := by rfl

def raw3863 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 2, -2, -1], ![1, -2, 1, 0]]

def raw3863step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]

def raw3863step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical3863 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3863 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw3863 = injectiveMoment H raw3863step0 := by
      have heq : raw3863step0 = raw3863.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3863).symm
    injectiveMoment H raw3863step0 = injectiveMoment H raw3863step1 := by
      have heq : raw3863step1 = (fun i j => raw3863step0 (permutation19 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3863step0 permutation19 permutation7
    _ = injectiveMoment H node210 := by rfl

def raw3864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]

def raw3864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical3864 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3864 = injectiveMoment H node2653 := by
  calc
    injectiveMoment H raw3864 = injectiveMoment H raw3864step0 := by
      have heq : raw3864step0 = (fun i j => raw3864 (permutation293 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3864 permutation293 permutation6
    _ = injectiveMoment H node2653 := by rfl

def raw3865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]

def raw3865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical3865 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3865 = injectiveMoment H node2115 := by
  calc
    injectiveMoment H raw3865 = injectiveMoment H raw3865step0 := by
      have heq : raw3865step0 = (fun i j => raw3865 (permutation304 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3865 permutation304 permutation6
    _ = injectiveMoment H node2115 := by rfl

def raw3866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]

def raw3866step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

theorem canonical3866 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3866 = injectiveMoment H node2648 := by
  calc
    injectiveMoment H raw3866 = injectiveMoment H raw3866step0 := by
      have heq : raw3866step0 = (fun i j => raw3866 (permutation304 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3866 permutation304 permutation6
    _ = injectiveMoment H node2648 := by rfl

def raw3867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]

def raw3867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 1, 1]]

def raw3867step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

theorem canonical3867 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3867 = injectiveMoment H node2089 := by
  calc
    injectiveMoment H raw3867 = injectiveMoment H raw3867step0 := by
      have heq : raw3867step0 = -raw3867 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3867).symm
    injectiveMoment H raw3867step0 = injectiveMoment H raw3867step1 := by
      have heq : raw3867step1 = (fun i j => raw3867step0 (permutation154 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3867step0 permutation154 permutation8
    _ = injectiveMoment H node2089 := by rfl

def raw3868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]

def raw3868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]

def raw3868step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

theorem canonical3868 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3868 = injectiveMoment H node2090 := by
  calc
    injectiveMoment H raw3868 = injectiveMoment H raw3868step0 := by
      have heq : raw3868step0 = -raw3868 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3868).symm
    injectiveMoment H raw3868step0 = injectiveMoment H raw3868step1 := by
      have heq : raw3868step1 = (fun i j => raw3868step0 (permutation158 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3868step0 permutation158 permutation8
    _ = injectiveMoment H node2090 := by rfl

def raw3869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]

def raw3869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

theorem canonical3869 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3869 = injectiveMoment H node2092 := by
  calc
    injectiveMoment H raw3869 = injectiveMoment H raw3869step0 := by
      have heq : raw3869step0 = (fun i j => raw3869 (permutation297 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3869 permutation297 permutation6
    _ = injectiveMoment H node2092 := by rfl

def raw3870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw3870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]

def raw3870step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical3870 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3870 = injectiveMoment H node2663 := by
  calc
    injectiveMoment H raw3870 = injectiveMoment H raw3870step0 := by
      have heq : raw3870step0 = -raw3870 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3870).symm
    injectiveMoment H raw3870step0 = injectiveMoment H raw3870step1 := by
      have heq : raw3870step1 = (fun i j => raw3870step0 (permutation207 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3870step0 permutation207 permutation6
    _ = injectiveMoment H node2663 := by rfl

def raw3871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw3871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical3871 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3871 = injectiveMoment H node2656 := by
  calc
    injectiveMoment H raw3871 = injectiveMoment H raw3871step0 := by
      have heq : raw3871step0 = (fun i j => raw3871 (permutation390 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3871 permutation390 permutation6
    _ = injectiveMoment H node2656 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes52

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7168 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw7168step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 1, 1, -2], ![0, -1, -2, 3], ![-1, 0, 0, 1]]

def raw7168step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical7168 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7168 = injectiveMoment H node1198 := by
  calc
    injectiveMoment H raw7168 = injectiveMoment H raw7168step0 := by
      have heq : raw7168step0 = -raw7168 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7168).symm
    injectiveMoment H raw7168step0 = injectiveMoment H raw7168step1 := by
      have heq : raw7168step1 = (fun i j => raw7168step0 (permutation25 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7168step0 permutation25 permutation15
    _ = injectiveMoment H node1198 := by rfl

def raw7169 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw7169step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 1, 1, -2], ![0, -1, -3, 4], ![-1, 0, 1, 0]]

def raw7169step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical7169 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7169 = injectiveMoment H node1168 := by
  calc
    injectiveMoment H raw7169 = injectiveMoment H raw7169step0 := by
      have heq : raw7169step0 = -raw7169 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7169).symm
    injectiveMoment H raw7169step0 = injectiveMoment H raw7169step1 := by
      have heq : raw7169step1 = (fun i j => raw7169step0 (permutation25 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7169step0 permutation25 permutation15
    _ = injectiveMoment H node1168 := by rfl

def raw7170 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def raw7170step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical7170 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7170 = injectiveMoment H node998 := by
  calc
    injectiveMoment H raw7170 = injectiveMoment H raw7170step0 := by
      have heq : raw7170step0 = (fun i j => raw7170 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7170 permutation9 permutation11
    _ = injectiveMoment H node998 := by rfl

def raw7171 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw7171step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 1, 0, -1], ![0, -1, -2, 3], ![-1, 0, 1, 0]]

def raw7171step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical7171 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7171 = injectiveMoment H node1203 := by
  calc
    injectiveMoment H raw7171 = injectiveMoment H raw7171step0 := by
      have heq : raw7171step0 = -raw7171 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7171).symm
    injectiveMoment H raw7171step0 = injectiveMoment H raw7171step1 := by
      have heq : raw7171step1 = (fun i j => raw7171step0 (permutation25 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7171step0 permutation25 permutation15
    _ = injectiveMoment H node1203 := by rfl

def raw7172 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def raw7172step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![-1, 0, 2, -1], ![2, 1, -4, 1]]

def raw7172step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 1, -2, 1], ![1, 0, -2, 1], ![-2, -1, 4, -1]]

def raw7172step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical7172 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7172 = injectiveMoment H node786 := by
  calc
    injectiveMoment H raw7172 = injectiveMoment H raw7172step0 := by
      have heq : raw7172step0 = raw7172.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7172).symm
    injectiveMoment H raw7172step0 = injectiveMoment H raw7172step1 := by
      have heq : raw7172step1 = -raw7172step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7172step0).symm
    injectiveMoment H raw7172step1 = injectiveMoment H raw7172step2 := by
      have heq : raw7172step2 = (fun i j => raw7172step1 (permutation28 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7172step1 permutation28 permutation16
    _ = injectiveMoment H node786 := by rfl

def raw7173 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def raw7173step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 1, -1, 0], ![0, 0, 1, -1], ![0, -1, -2, 3], ![-1, 0, 1, 0]]

def raw7173step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical7173 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7173 = injectiveMoment H node2705 := by
  calc
    injectiveMoment H raw7173 = injectiveMoment H raw7173step0 := by
      have heq : raw7173step0 = -raw7173 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7173).symm
    injectiveMoment H raw7173step0 = injectiveMoment H raw7173step1 := by
      have heq : raw7173step1 = (fun i j => raw7173step0 (permutation126 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7173step0 permutation126 permutation15
    _ = injectiveMoment H node2705 := by rfl

def raw7174 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 0, 2, -2], ![1, 0, -1, 0]]

def raw7174step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 1, -1, 0], ![0, -1, 1, 0], ![0, 0, -2, 2], ![-1, 0, 1, 0]]

def raw7174step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem canonical7174 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7174 = injectiveMoment H node2758 := by
  calc
    injectiveMoment H raw7174 = injectiveMoment H raw7174step0 := by
      have heq : raw7174step0 = -raw7174 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7174).symm
    injectiveMoment H raw7174step0 = injectiveMoment H raw7174step1 := by
      have heq : raw7174step1 = (fun i j => raw7174step0 (permutation102 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7174step0 permutation102 permutation16
    _ = injectiveMoment H node2758 := by rfl

def raw7175 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

theorem canonical7175 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7175 = injectiveMoment H node2727 := by
  rfl

def raw7176 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 0, -2, 2], ![1, 1, 1, -3]]

def raw7176step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 1, -2, 1], ![0, 0, 2, -2], ![-1, -1, -1, 3]]

def raw7176step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem canonical7176 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7176 = injectiveMoment H node973 := by
  calc
    injectiveMoment H raw7176 = injectiveMoment H raw7176step0 := by
      have heq : raw7176step0 = -raw7176 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7176).symm
    injectiveMoment H raw7176step0 = injectiveMoment H raw7176step1 := by
      have heq : raw7176step1 = (fun i j => raw7176step0 (permutation32 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7176step0 permutation32 permutation9
    _ = injectiveMoment H node973 := by rfl

def raw7177 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical7177 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7177 = injectiveMoment H node1245 := by
  rfl

def raw7178 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical7178 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7178 = injectiveMoment H node1246 := by
  rfl

def raw7179 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, -1, 1, -1]]

def raw7179step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

theorem canonical7179 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7179 = injectiveMoment H node1309 := by
  calc
    injectiveMoment H raw7179 = injectiveMoment H raw7179step0 := by
      have heq : raw7179step0 = (fun i j => raw7179 (permutation9 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7179 permutation9 permutation10
    _ = injectiveMoment H node1309 := by rfl

def raw7180 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def raw7180step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical7180 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7180 = injectiveMoment H node1009 := by
  calc
    injectiveMoment H raw7180 = injectiveMoment H raw7180step0 := by
      have heq : raw7180step0 = (fun i j => raw7180 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7180 permutation11 permutation11
    _ = injectiveMoment H node1009 := by rfl

def raw7181 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![1, 1, -1, -1]]

def raw7181step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 2, -1], ![2, -1, -1]]

def raw7181step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![-2, 1, 1]]

def raw7181step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical7181 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7181 = injectiveMoment H node230 := by
  calc
    injectiveMoment H raw7181 = injectiveMoment H raw7181step0 := by
      have heq : raw7181step0 = raw7181.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7181).symm
    injectiveMoment H raw7181step0 = injectiveMoment H raw7181step1 := by
      have heq : raw7181step1 = -raw7181step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7181step0).symm
    injectiveMoment H raw7181step1 = injectiveMoment H raw7181step2 := by
      have heq : raw7181step2 = (fun i j => raw7181step1 (permutation29 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7181step1 permutation29 permutation4
    _ = injectiveMoment H node230 := by rfl

def raw7182 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def raw7182step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical7182 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7182 = injectiveMoment H node1206 := by
  calc
    injectiveMoment H raw7182 = injectiveMoment H raw7182step0 := by
      have heq : raw7182step0 = (fun i j => raw7182 (permutation16 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7182 permutation16 permutation16
    _ = injectiveMoment H node1206 := by rfl

def raw7183 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def raw7183step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical7183 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7183 = injectiveMoment H node1207 := by
  calc
    injectiveMoment H raw7183 = injectiveMoment H raw7183step0 := by
      have heq : raw7183step0 = (fun i j => raw7183 (permutation16 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7183 permutation16 permutation16
    _ = injectiveMoment H node1207 := by rfl

def raw7184 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def raw7184step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 1, -3, 2], ![0, -2, 2, 0], ![-1, 1, 0, 0]]

def raw7184step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, 0, 1]]

theorem canonical7184 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7184 = injectiveMoment H node1301 := by
  calc
    injectiveMoment H raw7184 = injectiveMoment H raw7184step0 := by
      have heq : raw7184step0 = -raw7184 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7184).symm
    injectiveMoment H raw7184step0 = injectiveMoment H raw7184step1 := by
      have heq : raw7184step1 = (fun i j => raw7184step0 (permutation32 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7184step0 permutation32 permutation13
    _ = injectiveMoment H node1301 := by rfl

def raw7185 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem canonical7185 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7185 = injectiveMoment H node1249 := by
  rfl

def raw7186 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![1, 1, -2, 0]]

def raw7186step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 3, -2], ![2, -2, 0]]

def raw7186step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical7186 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7186 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw7186 = injectiveMoment H raw7186step0 := by
      have heq : raw7186step0 = raw7186.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7186).symm
    injectiveMoment H raw7186step0 = injectiveMoment H raw7186step1 := by
      have heq : raw7186step1 = (fun i j => raw7186step0 (permutation25 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7186step0 permutation25 permutation7
    _ = injectiveMoment H node185 := by rfl

def raw7187 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, 0, 0, -1]]

def raw7187step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

theorem canonical7187 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7187 = injectiveMoment H node280 := by
  calc
    injectiveMoment H raw7187 = injectiveMoment H raw7187step0 := by
      have hz : ∀ i, raw7187 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7187step0 = (fun i j => raw7187 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7187 permutation15 hz
    _ = injectiveMoment H node280 := by rfl

def raw7188 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 3, -3]]

theorem canonical7188 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7188 = injectiveMoment H node1252 := by
  rfl

def raw7189 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw7189step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 0, 2, -2], ![0, -1, -3, 4], ![-1, 1, 0, 0]]

def raw7189step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem canonical7189 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7189 = injectiveMoment H node1178 := by
  calc
    injectiveMoment H raw7189 = injectiveMoment H raw7189step0 := by
      have heq : raw7189step0 = -raw7189 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7189).symm
    injectiveMoment H raw7189step0 = injectiveMoment H raw7189step1 := by
      have heq : raw7189step1 = (fun i j => raw7189step0 (permutation23 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7189step0 permutation23 permutation15
    _ = injectiveMoment H node1178 := by rfl

def raw7190 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 3, -2]]

theorem canonical7190 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7190 = injectiveMoment H node1255 := by
  rfl

def raw7191 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![1, 0, 3, -4]]

def raw7191step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 0, 2, -2], ![-1, 0, -3, 4]]

def raw7191step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, -3, 4]]

def raw7191step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

theorem canonical7191 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7191 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw7191 = injectiveMoment H raw7191step0 := by
      have heq : raw7191step0 = -raw7191 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7191).symm
    injectiveMoment H raw7191step0 = injectiveMoment H raw7191step1 := by
      have hz : ∀ i, raw7191step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw7191step1 = (fun i j => raw7191step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7191step0 permutation15 hz
    injectiveMoment H raw7191step1 = injectiveMoment H raw7191step2 := by
      have heq : raw7191step2 = (fun i j => raw7191step1 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7191step1 permutation8 permutation3
    _ = injectiveMoment H node52 := by rfl

def raw7192 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def raw7192step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, -3, 4], ![-1, 1, 0, 0]]

def raw7192step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem canonical7192 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7192 = injectiveMoment H node2690 := by
  calc
    injectiveMoment H raw7192 = injectiveMoment H raw7192step0 := by
      have heq : raw7192step0 = -raw7192 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7192).symm
    injectiveMoment H raw7192step0 = injectiveMoment H raw7192step1 := by
      have heq : raw7192step1 = (fun i j => raw7192step0 (permutation112 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7192step0 permutation112 permutation15
    _ = injectiveMoment H node2690 := by rfl

def raw7193 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-1, -1, 2, 0], ![1, 2, 1, -4]]

def raw7193step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 1, 0, 0], ![1, 1, -2, 0], ![-1, -2, -1, 4]]

def raw7193step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical7193 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7193 = injectiveMoment H node2930 := by
  calc
    injectiveMoment H raw7193 = injectiveMoment H raw7193step0 := by
      have heq : raw7193step0 = -raw7193 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7193).symm
    injectiveMoment H raw7193step0 = injectiveMoment H raw7193step1 := by
      have heq : raw7193step1 = (fun i j => raw7193step0 (permutation337 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7193step0 permutation337 permutation15
    _ = injectiveMoment H node2930 := by rfl

def raw7194 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 0, 3, -3], ![1, -1, 0, 0]]

def raw7194step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0]]

theorem canonical7194 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7194 = injectiveMoment H node2730 := by
  calc
    injectiveMoment H raw7194 = injectiveMoment H raw7194step0 := by
      have heq : raw7194step0 = (fun i j => raw7194 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7194 permutation35 permutation9
    _ = injectiveMoment H node2730 := by rfl

def raw7195 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem canonical7195 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7195 = injectiveMoment H node2732 := by
  rfl

def raw7196 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem canonical7196 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7196 = injectiveMoment H node2733 := by
  rfl

def raw7197 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-1, -1, 1, 1], ![1, 1, 2, -4]]

def raw7197step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![1, 0, 1, -2], ![0, 0, 1, -1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![1, 1, -1, -1], ![-1, -1, -2, 4]]

def raw7197step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical7197 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7197 = injectiveMoment H node3342 := by
  calc
    injectiveMoment H raw7197 = injectiveMoment H raw7197step0 := by
      have heq : raw7197step0 = -raw7197 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7197).symm
    injectiveMoment H raw7197step0 = injectiveMoment H raw7197step1 := by
      have heq : raw7197step1 = (fun i j => raw7197step0 (permutation357 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7197step0 permutation357 permutation15
    _ = injectiveMoment H node3342 := by rfl

def raw7198 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 2, -2]]

theorem canonical7198 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7198 = injectiveMoment H node1259 := by
  rfl

def raw7199 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def raw7199step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![-1, -1, 2, 0], ![2, 1, -3, 0]]

def raw7199step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 0, -1], ![0, 0, -1, 1], ![1, 1, -2, 0], ![-2, -1, 3, 0]]

def raw7199step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical7199 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7199 = injectiveMoment H node1202 := by
  calc
    injectiveMoment H raw7199 = injectiveMoment H raw7199step0 := by
      have heq : raw7199step0 = raw7199.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7199).symm
    injectiveMoment H raw7199step0 = injectiveMoment H raw7199step1 := by
      have heq : raw7199step1 = -raw7199step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7199step0).symm
    injectiveMoment H raw7199step1 = injectiveMoment H raw7199step2 := by
      have heq : raw7199step2 = (fun i j => raw7199step1 (permutation27 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7199step1 permutation27 permutation19
    _ = injectiveMoment H node1202 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

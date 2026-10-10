import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4960 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 3, -3], ![1, -2, 1], ![1, -2, 1]]

def raw4960step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

theorem canonical4960 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4960 = injectiveMoment H node223 := by
  calc
    injectiveMoment H raw4960 = injectiveMoment H raw4960step0 := by
      have heq : raw4960step0 = (fun i j => raw4960 (permutation9 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4960 permutation9 permutation4
    _ = injectiveMoment H node223 := by rfl

def raw4961 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -4, 3], ![0, 2, -2], ![1, 1, -2]]

def raw4961step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

theorem canonical4961 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4961 = injectiveMoment H node225 := by
  calc
    injectiveMoment H raw4961 = injectiveMoment H raw4961step0 := by
      have heq : raw4961step0 = (fun i j => raw4961 (permutation12 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4961 permutation12 permutation4
    _ = injectiveMoment H node225 := by rfl

def raw4962 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -4, 3], ![0, 3, -3], ![1, 0, -1]]

def raw4962step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, -1, 0], ![1, 3, -4]]

theorem canonical4962 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4962 = injectiveMoment H node221 := by
  calc
    injectiveMoment H raw4962 = injectiveMoment H raw4962step0 := by
      have heq : raw4962step0 = (fun i j => raw4962 (permutation12 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4962 permutation12 permutation4
    _ = injectiveMoment H node221 := by rfl

def raw4963 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -4, 3], ![1, 3, -4]]

theorem canonical4963 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4963 = injectiveMoment H node42 := by
  rfl

def raw4964 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![0, 2, -2], ![1, 0, -1]]

def raw4964step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

theorem canonical4964 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4964 = injectiveMoment H node226 := by
  calc
    injectiveMoment H raw4964 = injectiveMoment H raw4964step0 := by
      have heq : raw4964step0 = (fun i j => raw4964 (permutation12 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4964 permutation12 permutation4
    _ = injectiveMoment H node226 := by rfl

def raw4965 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![1, 2, -3]]

theorem canonical4965 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4965 = injectiveMoment H node43 := by
  rfl

def raw4966 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical4966 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4966 = injectiveMoment H node44 := by
  rfl

def raw4967 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 0, -1]]

def raw4967step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1]]

def raw4967step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, 0, -1]]

theorem canonical4967 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4967 = injectiveMoment H node61 := by
  calc
    injectiveMoment H raw4967 = injectiveMoment H raw4967step0 := by
      have heq : raw4967step0 = -raw4967 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4967).symm
    injectiveMoment H raw4967step0 = injectiveMoment H raw4967step1 := by
      have heq : raw4967step1 = (fun i j => raw4967step0 (permutation4 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4967step0 permutation4 permutation6
    _ = injectiveMoment H node61 := by rfl

def raw4968 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![-2, -2, 1, 3], ![4, 1, -2, -3]]

def raw4968step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![1, -2, 1], ![1, 1, -2], ![0, 3, -3]]

def raw4968step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -2, 1], ![1, 1, -2]]

theorem canonical4968 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4968 = injectiveMoment H node154 := by
  calc
    injectiveMoment H raw4968 = injectiveMoment H raw4968step0 := by
      have heq : raw4968step0 = raw4968.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4968).symm
    injectiveMoment H raw4968step0 = injectiveMoment H raw4968step1 := by
      have heq : raw4968step1 = (fun i j => raw4968step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4968step0 permutation13 permutation3
    _ = injectiveMoment H node154 := by rfl

def raw4969 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![-2, -2, 2, 2], ![4, 1, -3, -2]]

def raw4969step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![1, -2, 1], ![1, 2, -3], ![0, 2, -2]]

def raw4969step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -2, 1], ![1, 2, -3]]

theorem canonical4969 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4969 = injectiveMoment H node152 := by
  calc
    injectiveMoment H raw4969 = injectiveMoment H raw4969step0 := by
      have heq : raw4969step0 = raw4969.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4969).symm
    injectiveMoment H raw4969step0 = injectiveMoment H raw4969step1 := by
      have heq : raw4969step1 = (fun i j => raw4969step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4969step0 permutation13 permutation3
    _ = injectiveMoment H node152 := by rfl

def raw4970 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![-2, 1, 2, -1], ![4, -2, -3, 1]]

def raw4970step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 1, -2], ![1, 2, -3], ![0, -1, 1]]

def raw4970step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 1, -2], ![1, 2, -3]]

theorem canonical4970 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4970 = injectiveMoment H node144 := by
  calc
    injectiveMoment H raw4970 = injectiveMoment H raw4970step0 := by
      have heq : raw4970step0 = raw4970.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4970).symm
    injectiveMoment H raw4970step0 = injectiveMoment H raw4970step1 := by
      have heq : raw4970step1 = (fun i j => raw4970step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4970step0 permutation13 permutation3
    _ = injectiveMoment H node144 := by rfl

def raw4971 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![-1, -2, 1, 2], ![3, 1, -2, -2]]

def raw4971step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 1, -2], ![0, 2, -2]]

def raw4971step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

theorem canonical4971 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4971 = injectiveMoment H node184 := by
  calc
    injectiveMoment H raw4971 = injectiveMoment H raw4971step0 := by
      have heq : raw4971step0 = raw4971.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4971).symm
    injectiveMoment H raw4971step0 = injectiveMoment H raw4971step1 := by
      have heq : raw4971step1 = (fun i j => raw4971step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4971step0 permutation13 permutation3
    _ = injectiveMoment H node184 := by rfl

def raw4972 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![-1, -2, 2, 1], ![3, 1, -3, -1]]

def raw4972step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 2, -3], ![0, 1, -1]]

def raw4972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical4972 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4972 = injectiveMoment H node180 := by
  calc
    injectiveMoment H raw4972 = injectiveMoment H raw4972step0 := by
      have heq : raw4972step0 = raw4972.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4972).symm
    injectiveMoment H raw4972step0 = injectiveMoment H raw4972step1 := by
      have heq : raw4972step1 = (fun i j => raw4972step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4972step0 permutation13 permutation3
    _ = injectiveMoment H node180 := by rfl

def raw4973 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![-1, 1, 1, -1], ![3, -2, -2, 1]]

def raw4973step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 1, -2], ![1, 1, -2], ![0, -1, 1]]

def raw4973step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

theorem canonical4973 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4973 = injectiveMoment H node175 := by
  calc
    injectiveMoment H raw4973 = injectiveMoment H raw4973step0 := by
      have heq : raw4973step0 = raw4973.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4973).symm
    injectiveMoment H raw4973step0 = injectiveMoment H raw4973step1 := by
      have heq : raw4973step1 = (fun i j => raw4973step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4973step0 permutation13 permutation3
    _ = injectiveMoment H node175 := by rfl

def raw4974 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![-1, 1, 2, -2], ![3, -2, -3, 2]]

def raw4974step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 1, -2], ![1, 2, -3], ![0, -2, 2]]

def raw4974step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

theorem canonical4974 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4974 = injectiveMoment H node167 := by
  calc
    injectiveMoment H raw4974 = injectiveMoment H raw4974step0 := by
      have heq : raw4974step0 = raw4974.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4974).symm
    injectiveMoment H raw4974step0 = injectiveMoment H raw4974step1 := by
      have heq : raw4974step1 = (fun i j => raw4974step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4974step0 permutation13 permutation3
    _ = injectiveMoment H node167 := by rfl

def raw4975 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -3, 1, 2], ![2, 2, -2, -2]]

def raw4975step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -3, 2], ![1, 1, -2], ![0, 2, -2]]

def raw4975step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

theorem canonical4975 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4975 = injectiveMoment H node212 := by
  calc
    injectiveMoment H raw4975 = injectiveMoment H raw4975step0 := by
      have heq : raw4975step0 = raw4975.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4975).symm
    injectiveMoment H raw4975step0 = injectiveMoment H raw4975step1 := by
      have heq : raw4975step1 = (fun i j => raw4975step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4975step0 permutation13 permutation3
    _ = injectiveMoment H node212 := by rfl

def raw4976 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -3, 2, 1], ![2, 2, -3, -1]]

def raw4976step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -3, 2], ![1, 2, -3], ![0, 1, -1]]

def raw4976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

theorem canonical4976 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4976 = injectiveMoment H node209 := by
  calc
    injectiveMoment H raw4976 = injectiveMoment H raw4976step0 := by
      have heq : raw4976step0 = raw4976.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4976).symm
    injectiveMoment H raw4976step0 = injectiveMoment H raw4976step1 := by
      have heq : raw4976step1 = (fun i j => raw4976step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4976step0 permutation13 permutation3
    _ = injectiveMoment H node209 := by rfl

def raw4977 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -2, -2, 4], ![2, 1, 1, -4]]

def raw4977step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -2, 1], ![1, -2, 1], ![0, 4, -4]]

def raw4977step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -2, 1], ![1, -2, 1]]

theorem canonical4977 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4977 = injectiveMoment H node218 := by
  calc
    injectiveMoment H raw4977 = injectiveMoment H raw4977step0 := by
      have heq : raw4977step0 = raw4977.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4977).symm
    injectiveMoment H raw4977step0 = injectiveMoment H raw4977step1 := by
      have heq : raw4977step1 = (fun i j => raw4977step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4977step0 permutation13 permutation3
    _ = injectiveMoment H node218 := by rfl

def raw4978 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -2, -1, 3], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw4978step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, 2, -4]]

theorem canonical4978 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4978 = injectiveMoment H node1953 := by
  calc
    injectiveMoment H raw4978 = injectiveMoment H raw4978step0 := by
      have heq : raw4978step0 = (fun i j => raw4978 (permutation64 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4978 permutation64 permutation15
    _ = injectiveMoment H node1953 := by rfl

def raw4979 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -2, -1, 3], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw4979step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -2, 0, 1], ![1, -1, -1, 1], ![0, 3, 0, -3]]

def raw4979step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -2, 0, 1]]

theorem canonical4979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4979 = injectiveMoment H node1352 := by
  calc
    injectiveMoment H raw4979 = injectiveMoment H raw4979step0 := by
      have heq : raw4979step0 = raw4979.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4979).symm
    injectiveMoment H raw4979step0 = injectiveMoment H raw4979step1 := by
      have heq : raw4979step1 = (fun i j => raw4979step0 (permutation26 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4979step0 permutation26 permutation21
    _ = injectiveMoment H node1352 := by rfl

def raw4980 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -2, 0, 2], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw4980step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, -1, 1, 0], ![1, 1, -2, 0], ![1, 1, 1, -3]]

theorem canonical4980 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4980 = injectiveMoment H node2007 := by
  calc
    injectiveMoment H raw4980 = injectiveMoment H raw4980step0 := by
      have heq : raw4980step0 = (fun i j => raw4980 (permutation64 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4980 permutation64 permutation17
    _ = injectiveMoment H node2007 := by rfl

def raw4981 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -2, 1, 1], ![2, 1, -2, -1]]

def raw4981step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -2, 1], ![1, 1, -2], ![0, 1, -1]]

def raw4981step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical4981 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4981 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw4981 = injectiveMoment H raw4981step0 := by
      have heq : raw4981step0 = raw4981.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4981).symm
    injectiveMoment H raw4981step0 = injectiveMoment H raw4981step1 := by
      have heq : raw4981step1 = (fun i j => raw4981step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4981step0 permutation13 permutation3
    _ = injectiveMoment H node210 := by rfl

def raw4982 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -2, 3, -1], ![2, 1, -4, 1]]

def raw4982step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -2, 1], ![1, 3, -4], ![0, -1, 1]]

def raw4982step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

theorem canonical4982 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4982 = injectiveMoment H node206 := by
  calc
    injectiveMoment H raw4982 = injectiveMoment H raw4982step0 := by
      have heq : raw4982step0 = raw4982.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4982).symm
    injectiveMoment H raw4982step0 = injectiveMoment H raw4982step1 := by
      have heq : raw4982step1 = (fun i j => raw4982step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4982step0 permutation13 permutation3
    _ = injectiveMoment H node206 := by rfl

def raw4983 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem canonical4983 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4983 = injectiveMoment H node2307 := by
  rfl

def raw4984 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

theorem canonical4984 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4984 = injectiveMoment H node2308 := by
  rfl

def raw4985 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw4985step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, 1, 0]]

theorem canonical4985 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4985 = injectiveMoment H node2693 := by
  calc
    injectiveMoment H raw4985 = injectiveMoment H raw4985step0 := by
      have heq : raw4985step0 = (fun i j => raw4985 (permutation65 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4985 permutation65 permutation15
    _ = injectiveMoment H node2693 := by rfl

def raw4986 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

theorem canonical4986 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4986 = injectiveMoment H node2309 := by
  rfl

def raw4987 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![2, 0, 0, -2]]

def raw4987step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -2, 1, 0]]

theorem canonical4987 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4987 = injectiveMoment H node1180 := by
  calc
    injectiveMoment H raw4987 = injectiveMoment H raw4987step0 := by
      have heq : raw4987step0 = (fun i j => raw4987 (permutation18 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4987 permutation18 permutation15
    _ = injectiveMoment H node1180 := by rfl

def raw4988 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem canonical4988 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4988 = injectiveMoment H node2310 := by
  rfl

def raw4989 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical4989 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4989 = injectiveMoment H node2311 := by
  rfl

def raw4990 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![2, -1, 1, -2]]

def raw4990step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![1, -3, 1, 1], ![0, 4, -2, -2]]

def raw4990step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, 1, -3]]

theorem canonical4990 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4990 = injectiveMoment H node578 := by
  calc
    injectiveMoment H raw4990 = injectiveMoment H raw4990step0 := by
      have heq : raw4990step0 = raw4990.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4990).symm
    injectiveMoment H raw4990step0 = injectiveMoment H raw4990step1 := by
      have heq : raw4990step1 = (fun i j => raw4990step0 (permutation27 i) (permutation22 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4990step0 permutation27 permutation22
    _ = injectiveMoment H node578 := by rfl

def raw4991 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical4991 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4991 = injectiveMoment H node2312 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI

import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw160 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]

def raw160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]

def raw160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical160 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw160 = injectiveMoment H node443 := by
  calc
    injectiveMoment H raw160 = injectiveMoment H raw160step0 := by
      have heq : raw160step0 = -raw160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw160).symm
    injectiveMoment H raw160step0 = injectiveMoment H raw160step1 := by
      have heq : raw160step1 = (fun i j => raw160step0 (permutation49 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw160step0 permutation49 permutation6
    _ = injectiveMoment H node443 := by rfl

def raw161 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]

def raw161step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 1, 0], ![-3, 0, 3]]

def raw161step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical161 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw161 = injectiveMoment H node155 := by
  calc
    injectiveMoment H raw161 = injectiveMoment H raw161step0 := by
      have heq : raw161step0 = -raw161 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw161).symm
    injectiveMoment H raw161step0 = injectiveMoment H raw161step1 := by
      have heq : raw161step1 = (fun i j => raw161step0 (permutation13 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw161step0 permutation13 permutation6
    _ = injectiveMoment H node155 := by rfl

def raw162 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]

def raw162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]

def raw162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical162 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw162 = injectiveMoment H node440 := by
  calc
    injectiveMoment H raw162 = injectiveMoment H raw162step0 := by
      have heq : raw162step0 = -raw162 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw162).symm
    injectiveMoment H raw162step0 = injectiveMoment H raw162step1 := by
      have heq : raw162step1 = (fun i j => raw162step0 (permutation41 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw162step0 permutation41 permutation6
    _ = injectiveMoment H node440 := by rfl

def raw163 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]

def raw163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]

def raw163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

theorem canonical163 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw163 = injectiveMoment H node421 := by
  calc
    injectiveMoment H raw163 = injectiveMoment H raw163step0 := by
      have heq : raw163step0 = -raw163 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw163).symm
    injectiveMoment H raw163step0 = injectiveMoment H raw163step1 := by
      have heq : raw163step1 = (fun i j => raw163step0 (permutation37 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw163step0 permutation37 permutation8
    _ = injectiveMoment H node421 := by rfl

def raw164 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]

def raw164step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]

def raw164step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical164 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw164 = injectiveMoment H node149 := by
  calc
    injectiveMoment H raw164 = injectiveMoment H raw164step0 := by
      have heq : raw164step0 = -raw164 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw164).symm
    injectiveMoment H raw164step0 = injectiveMoment H raw164step1 := by
      have heq : raw164step1 = (fun i j => raw164step0 (permutation11 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw164step0 permutation11 permutation6
    _ = injectiveMoment H node149 := by rfl

def raw165 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]

def raw165step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]

def raw165step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]

theorem canonical165 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw165 = injectiveMoment H node132 := by
  calc
    injectiveMoment H raw165 = injectiveMoment H raw165step0 := by
      have heq : raw165step0 = -raw165 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw165).symm
    injectiveMoment H raw165step0 = injectiveMoment H raw165step1 := by
      have heq : raw165step1 = (fun i j => raw165step0 (permutation10 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw165step0 permutation10 permutation8
    _ = injectiveMoment H node132 := by rfl

def raw166 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]

def raw166step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]

theorem canonical166 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw166 = injectiveMoment H node102 := by
  calc
    injectiveMoment H raw166 = injectiveMoment H raw166step0 := by
      have heq : raw166step0 = (fun i j => raw166 (permutation32 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw166 permutation32 permutation8
    _ = injectiveMoment H node102 := by rfl

def raw167 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]

def raw167step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]

def raw167step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

theorem canonical167 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw167 = injectiveMoment H node153 := by
  calc
    injectiveMoment H raw167 = injectiveMoment H raw167step0 := by
      have heq : raw167step0 = -raw167 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw167).symm
    injectiveMoment H raw167step0 = injectiveMoment H raw167step1 := by
      have heq : raw167step1 = (fun i j => raw167step0 (permutation13 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw167step0 permutation13 permutation6
    _ = injectiveMoment H node153 := by rfl

def raw168 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]

def raw168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

theorem canonical168 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw168 = injectiveMoment H node422 := by
  calc
    injectiveMoment H raw168 = injectiveMoment H raw168step0 := by
      have heq : raw168step0 = -raw168 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw168).symm
    injectiveMoment H raw168step0 = injectiveMoment H raw168step1 := by
      have heq : raw168step1 = (fun i j => raw168step0 (permutation56 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw168step0 permutation56 permutation6
    _ = injectiveMoment H node422 := by rfl

def raw169 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]

def raw169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]

def raw169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical169 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw169 = injectiveMoment H node437 := by
  calc
    injectiveMoment H raw169 = injectiveMoment H raw169step0 := by
      have heq : raw169step0 = -raw169 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw169).symm
    injectiveMoment H raw169step0 = injectiveMoment H raw169step1 := by
      have heq : raw169step1 = (fun i j => raw169step0 (permutation42 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw169step0 permutation42 permutation6
    _ = injectiveMoment H node437 := by rfl

def raw170 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]

def raw170step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]

def raw170step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical170 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw170 = injectiveMoment H node146 := by
  calc
    injectiveMoment H raw170 = injectiveMoment H raw170step0 := by
      have heq : raw170step0 = -raw170 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw170).symm
    injectiveMoment H raw170step0 = injectiveMoment H raw170step1 := by
      have heq : raw170step1 = (fun i j => raw170step0 (permutation12 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw170step0 permutation12 permutation6
    _ = injectiveMoment H node146 := by rfl

def raw171 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]

def raw171step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]

def raw171step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]

theorem canonical171 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw171 = injectiveMoment H node134 := by
  calc
    injectiveMoment H raw171 = injectiveMoment H raw171step0 := by
      have heq : raw171step0 = -raw171 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw171).symm
    injectiveMoment H raw171step0 = injectiveMoment H raw171step1 := by
      have heq : raw171step1 = (fun i j => raw171step0 (permutation12 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw171step0 permutation12 permutation6
    _ = injectiveMoment H node134 := by rfl

def raw172 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]

def raw172step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 2, -1], ![-3, 0, 3]]

def raw172step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

theorem canonical172 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw172 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw172 = injectiveMoment H raw172step0 := by
      have heq : raw172step0 = -raw172 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw172).symm
    injectiveMoment H raw172step0 = injectiveMoment H raw172step1 := by
      have heq : raw172step1 = (fun i j => raw172step0 (permutation4 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw172step0 permutation4 permutation6
    _ = injectiveMoment H node32 := by rfl

def raw173 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def raw173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]

def raw173step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical173 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw173 = injectiveMoment H node441 := by
  calc
    injectiveMoment H raw173 = injectiveMoment H raw173step0 := by
      have heq : raw173step0 = -raw173 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw173).symm
    injectiveMoment H raw173step0 = injectiveMoment H raw173step1 := by
      have heq : raw173step1 = (fun i j => raw173step0 (permutation49 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw173step0 permutation49 permutation6
    _ = injectiveMoment H node441 := by rfl

def raw174 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]

def raw174step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]

def raw174step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

theorem canonical174 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw174 = injectiveMoment H node145 := by
  calc
    injectiveMoment H raw174 = injectiveMoment H raw174step0 := by
      have heq : raw174step0 = -raw174 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw174).symm
    injectiveMoment H raw174step0 = injectiveMoment H raw174step1 := by
      have heq : raw174step1 = (fun i j => raw174step0 (permutation9 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw174step0 permutation9 permutation8
    _ = injectiveMoment H node145 := by rfl

def raw175 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw175step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]

def raw175step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical175 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw175 = injectiveMoment H node150 := by
  calc
    injectiveMoment H raw175 = injectiveMoment H raw175step0 := by
      have heq : raw175step0 = -raw175 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw175).symm
    injectiveMoment H raw175step0 = injectiveMoment H raw175step1 := by
      have heq : raw175step1 = (fun i j => raw175step0 (permutation11 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw175step0 permutation11 permutation6
    _ = injectiveMoment H node150 := by rfl

def raw176 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]

def raw176step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]

def raw176step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-2, 1, 1], ![-2, 0, 2]]

def raw176step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

theorem canonical176 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw176 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw176 = injectiveMoment H raw176step0 := by
      have heq : raw176step0 = raw176.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw176).symm
    injectiveMoment H raw176step0 = injectiveMoment H raw176step1 := by
      have heq : raw176step1 = -raw176step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw176step0).symm
    injectiveMoment H raw176step1 = injectiveMoment H raw176step2 := by
      have heq : raw176step2 = (fun i j => raw176step1 (permutation4 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw176step1 permutation4 permutation6
    _ = injectiveMoment H node52 := by rfl

def raw177 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]

def raw177step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]

theorem canonical177 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw177 = injectiveMoment H node20 := by
  calc
    injectiveMoment H raw177 = injectiveMoment H raw177step0 := by
      have heq : raw177step0 = (fun i j => raw177 (permutation6 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw177 permutation6 permutation6
    _ = injectiveMoment H node20 := by rfl

def raw178 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]

def raw178step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-2, 2, 0], ![-2, 0, 2]]

def raw178step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]

theorem canonical178 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw178 = injectiveMoment H node31 := by
  calc
    injectiveMoment H raw178 = injectiveMoment H raw178step0 := by
      have heq : raw178step0 = -raw178 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw178).symm
    injectiveMoment H raw178step0 = injectiveMoment H raw178step1 := by
      have heq : raw178step1 = (fun i j => raw178step0 (permutation4 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw178step0 permutation4 permutation6
    _ = injectiveMoment H node31 := by rfl

def raw179 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]

def raw179step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-2, 1, 1], ![-2, 1, 1]]

def raw179step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 1, -2], ![1, 1, -2]]

theorem canonical179 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw179 = injectiveMoment H node35 := by
  calc
    injectiveMoment H raw179 = injectiveMoment H raw179step0 := by
      have heq : raw179step0 = -raw179 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw179).symm
    injectiveMoment H raw179step0 = injectiveMoment H raw179step1 := by
      have heq : raw179step1 = (fun i j => raw179step0 (permutation3 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw179step0 permutation3 permutation6
    _ = injectiveMoment H node35 := by rfl

def raw180 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]

def raw180step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]

theorem canonical180 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw180 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw180 = injectiveMoment H raw180step0 := by
      have heq : raw180step0 = raw180.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw180).symm
    _ = injectiveMoment H node9 := by rfl

def raw181 : Matrix (Fin 2) (Fin 4) ℤ := ![![-4, 2, 3, -1], ![4, -2, -3, 1]]

def raw181step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![3, -3], ![-1, 1]]

def raw181step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]

theorem canonical181 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw181 = injectiveMoment H node15 := by
  calc
    injectiveMoment H raw181 = injectiveMoment H raw181step0 := by
      have heq : raw181step0 = raw181.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw181).symm
    injectiveMoment H raw181step0 = injectiveMoment H raw181step1 := by
      have heq : raw181step1 = (fun i j => raw181step0 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw181step0 permutation13 permutation1
    _ = injectiveMoment H node15 := by rfl

def raw182 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 3, 1], ![4, -3, -1]]

def raw182step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![3, -3], ![1, -1]]

def raw182step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]

theorem canonical182 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw182 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw182 = injectiveMoment H raw182step0 := by
      have heq : raw182step0 = raw182.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw182).symm
    injectiveMoment H raw182step0 = injectiveMoment H raw182step1 := by
      have heq : raw182step1 = (fun i j => raw182step0 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw182step0 permutation4 permutation1
    _ = injectiveMoment H node8 := by rfl

def raw183 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![0, 0], ![1, -1], ![1, -1], ![3, -3]]

def raw183step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]

theorem canonical183 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw183 = injectiveMoment H node67 := by
  calc
    injectiveMoment H raw183 = injectiveMoment H raw183step0 := by
      have hz : ∀ j, raw183 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw183step0 = (fun i j => raw183 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw183 permutation221 hz
    _ = injectiveMoment H node67 := by rfl

def raw184 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![0, 0], ![1, -1], ![2, -2], ![2, -2]]

def raw184step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]

theorem canonical184 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw184 = injectiveMoment H node68 := by
  calc
    injectiveMoment H raw184 = injectiveMoment H raw184step0 := by
      have hz : ∀ j, raw184 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw184step0 = (fun i j => raw184 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw184 permutation221 hz
    _ = injectiveMoment H node68 := by rfl

def raw185 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![0, 0], ![1, -1], ![4, -4]]

def raw185step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]

theorem canonical185 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw185 = injectiveMoment H node14 := by
  calc
    injectiveMoment H raw185 = injectiveMoment H raw185step0 := by
      have hz : ∀ j, raw185 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw185step0 = (fun i j => raw185 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw185 permutation80 hz
    _ = injectiveMoment H node14 := by rfl

def raw186 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![0, 0], ![2, -2], ![3, -3]]

def raw186step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]

theorem canonical186 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw186 = injectiveMoment H node15 := by
  calc
    injectiveMoment H raw186 = injectiveMoment H raw186step0 := by
      have hz : ∀ j, raw186 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw186step0 = (fun i j => raw186 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw186 permutation80 hz
    _ = injectiveMoment H node15 := by rfl

def raw187 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical187 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw187 = injectiveMoment H node296 := by
  rfl

def raw188 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]

theorem canonical188 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw188 = injectiveMoment H node67 := by
  rfl

def raw189 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]

theorem canonical189 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw189 = injectiveMoment H node68 := by
  rfl

def raw190 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]

theorem canonical190 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw190 = injectiveMoment H node14 := by
  rfl

def raw191 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]

theorem canonical191 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw191 = injectiveMoment H node15 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI

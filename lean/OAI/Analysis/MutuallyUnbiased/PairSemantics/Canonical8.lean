import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw256 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 2, -3], ![1, 0, -1], ![1, 0, -1]]

def raw256step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

theorem canonical256 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw256 = injectiveMoment H node119 := by
  calc
    injectiveMoment H raw256 = injectiveMoment H raw256step0 := by
      have heq : raw256step0 = (fun i j => raw256 (permutation12 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw256 permutation12 permutation5
    _ = injectiveMoment H node119 := by rfl

def raw257 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 2, -3], ![2, 0, -2]]

def raw257step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![2, 1, -3]]

theorem canonical257 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw257 = injectiveMoment H node27 := by
  calc
    injectiveMoment H raw257 = injectiveMoment H raw257step0 := by
      have heq : raw257step0 = (fun i j => raw257 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw257 permutation4 permutation5
    _ = injectiveMoment H node27 := by rfl

def raw258 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 3, -4], ![2, -1, -1]]

def raw258step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![5, -4, -1]]

def raw258step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![2, -3, 1], ![-5, 4, 1]]

def raw258step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -3, 2], ![1, 4, -5]]

theorem canonical258 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw258 = injectiveMoment H node39 := by
  calc
    injectiveMoment H raw258 = injectiveMoment H raw258step0 := by
      have heq : raw258step0 = raw258.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw258).symm
    injectiveMoment H raw258step0 = injectiveMoment H raw258step1 := by
      have heq : raw258step1 = -raw258step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw258step0).symm
    injectiveMoment H raw258step1 = injectiveMoment H raw258step2 := by
      have heq : raw258step2 = (fun i j => raw258step1 (permutation3 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw258step1 permutation3 permutation8
    _ = injectiveMoment H node39 := by rfl

def raw259 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![2, -1, -1], ![1, 3, -4]]

def raw259step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, -1, 3], ![5, -1, -4]]

def raw259step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -2, -1], ![2, 1, -3], ![-5, 1, 4]]

def raw259step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -3, 2], ![1, 4, -5]]

theorem canonical259 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw259 = injectiveMoment H node39 := by
  calc
    injectiveMoment H raw259 = injectiveMoment H raw259step0 := by
      have heq : raw259step0 = raw259.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw259).symm
    injectiveMoment H raw259step0 = injectiveMoment H raw259step1 := by
      have heq : raw259step1 = -raw259step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw259step0).symm
    injectiveMoment H raw259step1 = injectiveMoment H raw259step2 := by
      have heq : raw259step2 = (fun i j => raw259step1 (permutation3 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw259step1 permutation3 permutation6
    _ = injectiveMoment H node39 := by rfl

def raw260 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![2, 0, -2], ![1, 2, -3]]

def raw260step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![2, 1, -3]]

theorem canonical260 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw260 = injectiveMoment H node27 := by
  calc
    injectiveMoment H raw260 = injectiveMoment H raw260step0 := by
      have heq : raw260step0 = (fun i j => raw260 (permutation3 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw260 permutation3 permutation5
    _ = injectiveMoment H node27 := by rfl

def raw261 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, -1, 1, 3], ![-1, 2, 1, -2], ![4, -1, -2, -1]]

def raw261step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 1, -2], ![3, -2, -1]]

def raw261step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![1, -2, 1], ![2, -1, -1]]

theorem canonical261 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw261 = injectiveMoment H node161 := by
  calc
    injectiveMoment H raw261 = injectiveMoment H raw261step0 := by
      have heq : raw261step0 = raw261.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw261).symm
    injectiveMoment H raw261step0 = injectiveMoment H raw261step1 := by
      have heq : raw261step1 = (fun i j => raw261step0 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw261step0 permutation28 permutation6
    _ = injectiveMoment H node161 := by rfl

def raw262 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, -1, 1, 3], ![1, 2, -2, -1], ![2, -1, 1, -2]]

def raw262step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]

def raw262step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]

theorem canonical262 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw262 = injectiveMoment H node159 := by
  calc
    injectiveMoment H raw262 = injectiveMoment H raw262step0 := by
      have heq : raw262step0 = raw262.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw262).symm
    injectiveMoment H raw262step0 = injectiveMoment H raw262step1 := by
      have heq : raw262step1 = (fun i j => raw262step0 (permutation30 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw262step0 permutation30 permutation8
    _ = injectiveMoment H node159 := by rfl

def raw263 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, -1, 2, 2], ![-1, 2, -2, 1], ![4, -1, 0, -3]]

def raw263step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -2, 0], ![2, 1, -3]]

def raw263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![2, -1, -1]]

theorem canonical263 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw263 = injectiveMoment H node191 := by
  calc
    injectiveMoment H raw263 = injectiveMoment H raw263step0 := by
      have heq : raw263step0 = raw263.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw263).symm
    injectiveMoment H raw263step0 = injectiveMoment H raw263step1 := by
      have heq : raw263step1 = (fun i j => raw263step0 (permutation22 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw263step0 permutation22 permutation6
    _ = injectiveMoment H node191 := by rfl

def raw264 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, -1, 2, 2], ![-1, 2, 1, -2], ![4, -1, -3, 0]]

def raw264step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, 1, -3], ![2, -2, 0]]

def raw264step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![2, -1, -1]]

theorem canonical264 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw264 = injectiveMoment H node191 := by
  calc
    injectiveMoment H raw264 = injectiveMoment H raw264step0 := by
      have heq : raw264step0 = raw264.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw264).symm
    injectiveMoment H raw264step0 = injectiveMoment H raw264step1 := by
      have heq : raw264step1 = (fun i j => raw264step0 (permutation28 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw264step0 permutation28 permutation6
    _ = injectiveMoment H node191 := by rfl

def raw265 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, -1, 2, 2], ![1, -1, 2, -2], ![2, 2, -4, 0]]

def raw265step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, 2, -4], ![2, -2, 0]]

def raw265step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-2, -2, 4], ![-2, 2, 0]]

def raw265step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, 1, -2], ![2, -2, 0]]

theorem canonical265 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw265 = injectiveMoment H node136 := by
  calc
    injectiveMoment H raw265 = injectiveMoment H raw265step0 := by
      have heq : raw265step0 = raw265.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw265).symm
    injectiveMoment H raw265step0 = injectiveMoment H raw265step1 := by
      have heq : raw265step1 = -raw265step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw265step0).symm
    injectiveMoment H raw265step1 = injectiveMoment H raw265step2 := by
      have heq : raw265step2 = (fun i j => raw265step1 (permutation21 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw265step1 permutation21 permutation5
    _ = injectiveMoment H node136 := by rfl

def raw266 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, -1, 2, 2], ![1, 2, -3, 0], ![2, -1, 1, -2]]

def raw266step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]

def raw266step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]

theorem canonical266 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw266 = injectiveMoment H node103 := by
  calc
    injectiveMoment H raw266 = injectiveMoment H raw266step0 := by
      have heq : raw266step0 = raw266.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw266).symm
    injectiveMoment H raw266step0 = injectiveMoment H raw266step1 := by
      have heq : raw266step1 = (fun i j => raw266step0 (permutation25 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw266step0 permutation25 permutation6
    _ = injectiveMoment H node103 := by rfl

def raw267 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, -1, 3, 1], ![-1, 2, -2, 1], ![4, -1, -1, -2]]

def raw267step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![3, -2, -1], ![1, 1, -2]]

def raw267step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![1, -2, 1], ![2, -1, -1]]

theorem canonical267 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw267 = injectiveMoment H node161 := by
  calc
    injectiveMoment H raw267 = injectiveMoment H raw267step0 := by
      have heq : raw267step0 = raw267.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw267).symm
    injectiveMoment H raw267step0 = injectiveMoment H raw267step1 := by
      have heq : raw267step1 = (fun i j => raw267step0 (permutation22 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw267step0 permutation22 permutation6
    _ = injectiveMoment H node161 := by rfl

def raw268 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, -1, 3, 1], ![1, 2, -1, -2], ![2, -1, -2, 1]]

def raw268step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![3, -1, -2], ![1, -2, 1]]

def raw268step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]

theorem canonical268 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw268 = injectiveMoment H node159 := by
  calc
    injectiveMoment H raw268 = injectiveMoment H raw268step0 := by
      have heq : raw268step0 = raw268.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw268).symm
    injectiveMoment H raw268step0 = injectiveMoment H raw268step1 := by
      have heq : raw268step1 = (fun i j => raw268step0 (permutation24 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw268step0 permutation24 permutation8
    _ = injectiveMoment H node159 := by rfl

def raw269 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]

theorem canonical269 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw269 = injectiveMoment H node305 := by
  rfl

def raw270 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]

theorem canonical270 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw270 = injectiveMoment H node306 := by
  rfl

def raw271 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

theorem canonical271 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw271 = injectiveMoment H node307 := by
  rfl

def raw272 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

theorem canonical272 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw272 = injectiveMoment H node308 := by
  rfl

def raw273 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]

theorem canonical273 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw273 = injectiveMoment H node310 := by
  rfl

def raw274 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]

theorem canonical274 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw274 = injectiveMoment H node79 := by
  rfl

def raw275 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw275step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw275step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3]]

theorem canonical275 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw275 = injectiveMoment H node243 := by
  calc
    injectiveMoment H raw275 = injectiveMoment H raw275step0 := by
      have hz : ∀ j, raw275 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw275step0 = (fun i j => raw275 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw275 permutation57 hz
    injectiveMoment H raw275step0 = injectiveMoment H raw275step1 := by
      have heq : raw275step1 = (fun i j => raw275step0 (permutation11 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw275step0 permutation11 permutation5
    _ = injectiveMoment H node243 := by rfl

def raw276 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 2, -2], ![3, -1, -2]]

def raw276step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 0, 3], ![-1, 0, 2, -1], ![4, 0, -2, -2]]

def raw276step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![4, -2, -2]]

def raw276step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

theorem canonical276 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw276 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw276 = injectiveMoment H raw276step0 := by
      have heq : raw276step0 = raw276.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw276).symm
    injectiveMoment H raw276step0 = injectiveMoment H raw276step1 := by
      have hz : ∀ i, raw276step0 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw276step1 = (fun i j => raw276step0 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw276step0 permutation15 hz
    injectiveMoment H raw276step1 = injectiveMoment H raw276step2 := by
      have heq : raw276step2 = (fun i j => raw276step1 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw276step1 permutation7 permutation6
    _ = injectiveMoment H node32 := by rfl

def raw277 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def raw277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]

def raw277step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]

def raw277step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

theorem canonical277 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw277 = injectiveMoment H node173 := by
  calc
    injectiveMoment H raw277 = injectiveMoment H raw277step0 := by
      have heq : raw277step0 = -raw277 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw277).symm
    injectiveMoment H raw277step0 = injectiveMoment H raw277step1 := by
      have hz : ∀ j, raw277step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw277step1 = (fun i j => raw277step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw277step0 permutation57 hz
    injectiveMoment H raw277step1 = injectiveMoment H raw277step2 := by
      have heq : raw277step2 = (fun i j => raw277step1 (permutation32 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw277step1 permutation32 permutation5
    _ = injectiveMoment H node173 := by rfl

def raw278 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]

def raw278step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![-3, 0, 1, 2], ![-1, 0, -1, 2], ![4, 0, 0, -4]]

def raw278step1 : Matrix (Fin 3) (Fin 4) ℤ := ![![3, 0, -1, -2], ![1, 0, 1, -2], ![-4, 0, 0, 4]]

def raw278step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-4, 0, 4]]

def raw278step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 4, -4], ![1, -2, 1]]

theorem canonical278 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw278 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw278 = injectiveMoment H raw278step0 := by
      have heq : raw278step0 = raw278.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw278).symm
    injectiveMoment H raw278step0 = injectiveMoment H raw278step1 := by
      have heq : raw278step1 = -raw278step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw278step0).symm
    injectiveMoment H raw278step1 = injectiveMoment H raw278step2 := by
      have hz : ∀ i, raw278step1 i (permutation15 0) = 0 := by decide +kernel
      have heq : raw278step2 = (fun i j => raw278step1 i (permutation15 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw278step1 permutation15 hz
    injectiveMoment H raw278step2 = injectiveMoment H raw278step3 := by
      have heq : raw278step3 = (fun i j => raw278step2 (permutation4 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw278step2 permutation4 permutation6
    _ = injectiveMoment H node59 := by rfl

def raw279 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 2, -3], ![2, -1, -1]]

def raw279step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, -2, 3], ![-2, 1, 1]]

def raw279step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -2, 3], ![-2, 1, 1]]

def raw279step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 3, -4]]

theorem canonical279 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw279 = injectiveMoment H node40 := by
  calc
    injectiveMoment H raw279 = injectiveMoment H raw279step0 := by
      have heq : raw279step0 = -raw279 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw279).symm
    injectiveMoment H raw279step0 = injectiveMoment H raw279step1 := by
      have hz : ∀ j, raw279step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw279step1 = (fun i j => raw279step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw279step0 permutation15 hz
    injectiveMoment H raw279step1 = injectiveMoment H raw279step2 := by
      have heq : raw279step2 = (fun i j => raw279step1 (permutation6 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw279step1 permutation6 permutation5
    _ = injectiveMoment H node40 := by rfl

def raw280 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]

def raw280step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def raw280step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3]]

theorem canonical280 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw280 = injectiveMoment H node243 := by
  calc
    injectiveMoment H raw280 = injectiveMoment H raw280step0 := by
      have hz : ∀ j, raw280 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw280step0 = (fun i j => raw280 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw280 permutation80 hz
    injectiveMoment H raw280step0 = injectiveMoment H raw280step1 := by
      have heq : raw280step1 = (fun i j => raw280step0 (permutation11 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw280step0 permutation11 permutation5
    _ = injectiveMoment H node243 := by rfl

def raw281 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

theorem canonical281 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw281 = injectiveMoment H node313 := by
  rfl

def raw282 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def raw282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical282 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw282 = injectiveMoment H node739 := by
  calc
    injectiveMoment H raw282 = injectiveMoment H raw282step0 := by
      have heq : raw282step0 = (fun i j => raw282 (permutation49 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw282 permutation49 permutation5
    _ = injectiveMoment H node739 := by rfl

def raw283 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def raw283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical283 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw283 = injectiveMoment H node742 := by
  calc
    injectiveMoment H raw283 = injectiveMoment H raw283step0 := by
      have heq : raw283step0 = (fun i j => raw283 (permutation55 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw283 permutation55 permutation5
    _ = injectiveMoment H node742 := by rfl

def raw284 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]

theorem canonical284 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw284 = injectiveMoment H node314 := by
  rfl

def raw285 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]

def raw285step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical285 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw285 = injectiveMoment H node248 := by
  calc
    injectiveMoment H raw285 = injectiveMoment H raw285step0 := by
      have heq : raw285step0 = (fun i j => raw285 (permutation13 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw285 permutation13 permutation5
    _ = injectiveMoment H node248 := by rfl

def raw286 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

theorem canonical286 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw286 = injectiveMoment H node315 := by
  rfl

def raw287 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]

theorem canonical287 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw287 = injectiveMoment H node316 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI

import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw192 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![0, 0], ![0, 0], ![1, -1], ![1, -1], ![2, -2]]

def raw192step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![0, 0], ![1, -1], ![1, -1], ![2, -2]]

def raw192step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical192 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw192 = injectiveMoment H node16 := by
  calc
    injectiveMoment H raw192 = injectiveMoment H raw192step0 := by
      have hz : ∀ j, raw192 (permutation221 0) j = 0 := by decide +kernel
      have heq : raw192step0 = (fun i j => raw192 (permutation221 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw192 permutation221 hz
    injectiveMoment H raw192step0 = injectiveMoment H raw192step1 := by
      have hz : ∀ j, raw192step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw192step1 = (fun i j => raw192step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw192step0 permutation57 hz
    _ = injectiveMoment H node16 := by rfl

def raw193 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![0, 0], ![0, 0], ![1, -1], ![3, -3]]

def raw193step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![0, 0], ![1, -1], ![3, -3]]

def raw193step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]

theorem canonical193 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw193 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw193 = injectiveMoment H raw193step0 := by
      have hz : ∀ j, raw193 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw193step0 = (fun i j => raw193 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw193 permutation80 hz
    injectiveMoment H raw193step0 = injectiveMoment H raw193step1 := by
      have hz : ∀ j, raw193step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw193step1 = (fun i j => raw193step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw193step0 permutation15 hz
    _ = injectiveMoment H node8 := by rfl

def raw194 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![0, 0], ![0, 0], ![2, -2], ![2, -2]]

def raw194step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![0, 0], ![2, -2], ![2, -2]]

def raw194step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]

theorem canonical194 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw194 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw194 = injectiveMoment H raw194step0 := by
      have hz : ∀ j, raw194 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw194step0 = (fun i j => raw194 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw194 permutation80 hz
    injectiveMoment H raw194step0 = injectiveMoment H raw194step1 := by
      have hz : ∀ j, raw194step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw194step1 = (fun i j => raw194step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw194step0 permutation15 hz
    _ = injectiveMoment H node9 := by rfl

def raw195 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![0, 0], ![0, 0], ![4, -4]]

def raw195step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![0, 0], ![4, -4]]

def raw195step1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-4, 4], ![4, -4]]

theorem canonical195 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw195 = injectiveMoment H node2 := by
  calc
    injectiveMoment H raw195 = injectiveMoment H raw195step0 := by
      have hz : ∀ j, raw195 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw195step0 = (fun i j => raw195 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw195 permutation21 hz
    injectiveMoment H raw195step0 = injectiveMoment H raw195step1 := by
      have hz : ∀ j, raw195step0 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw195step1 = (fun i j => raw195step0 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw195step0 permutation5 hz
    _ = injectiveMoment H node2 := by rfl

def raw196 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![0, 0], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

def raw196step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical196 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw196 = injectiveMoment H node69 := by
  calc
    injectiveMoment H raw196 = injectiveMoment H raw196step0 := by
      have hz : ∀ j, raw196 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw196step0 = (fun i j => raw196 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw196 permutation202 hz
    _ = injectiveMoment H node69 := by rfl

def raw197 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![0, 0], ![1, -1], ![1, -1], ![2, -2]]

def raw197step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical197 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw197 = injectiveMoment H node16 := by
  calc
    injectiveMoment H raw197 = injectiveMoment H raw197step0 := by
      have hz : ∀ j, raw197 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw197step0 = (fun i j => raw197 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw197 permutation57 hz
    _ = injectiveMoment H node16 := by rfl

def raw198 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![0, 0], ![1, -1], ![3, -3]]

def raw198step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]

theorem canonical198 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw198 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw198 = injectiveMoment H raw198step0 := by
      have hz : ∀ j, raw198 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw198step0 = (fun i j => raw198 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw198 permutation15 hz
    _ = injectiveMoment H node8 := by rfl

def raw199 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![0, 0], ![2, -2], ![2, -2]]

def raw199step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]

theorem canonical199 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw199 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw199 = injectiveMoment H raw199step0 := by
      have hz : ∀ j, raw199 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw199step0 = (fun i j => raw199 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw199 permutation15 hz
    _ = injectiveMoment H node9 := by rfl

def raw200 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![0, 0], ![4, -4]]

def raw200step0 : Matrix (Fin 2) (Fin 2) ℤ := ![![-4, 4], ![4, -4]]

theorem canonical200 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw200 = injectiveMoment H node2 := by
  calc
    injectiveMoment H raw200 = injectiveMoment H raw200step0 := by
      have hz : ∀ j, raw200 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw200step0 = (fun i j => raw200 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw200 permutation5 hz
    _ = injectiveMoment H node2 := by rfl

def raw201 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![0, 0], ![1, -1], ![2, -2]]

def raw201step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical201 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw201 = injectiveMoment H node16 := by
  calc
    injectiveMoment H raw201 = injectiveMoment H raw201step0 := by
      have hz : ∀ j, raw201 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw201step0 = (fun i j => raw201 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw201 permutation80 hz
    _ = injectiveMoment H node16 := by rfl

def raw202 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![0, 0], ![2, -2], ![1, -1]]

def raw202step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![2, -2], ![1, -1]]

def raw202step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical202 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw202 = injectiveMoment H node16 := by
  calc
    injectiveMoment H raw202 = injectiveMoment H raw202step0 := by
      have hz : ∀ j, raw202 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw202step0 = (fun i j => raw202 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw202 permutation80 hz
    injectiveMoment H raw202step0 = injectiveMoment H raw202step1 := by
      have heq : raw202step1 = (fun i j => raw202step0 (permutation10 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw202step0 permutation10 permutation1
    _ = injectiveMoment H node16 := by rfl

def raw203 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![0, 0], ![3, -3]]

def raw203step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]

theorem canonical203 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw203 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw203 = injectiveMoment H raw203step0 := by
      have hz : ∀ j, raw203 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw203step0 = (fun i j => raw203 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw203 permutation21 hz
    _ = injectiveMoment H node8 := by rfl

def raw204 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![0, 0], ![0, 0], ![2, -2]]

def raw204step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![0, 0], ![2, -2]]

def raw204step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical204 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw204 = injectiveMoment H node16 := by
  calc
    injectiveMoment H raw204 = injectiveMoment H raw204step0 := by
      have hz : ∀ j, raw204 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw204step0 = (fun i j => raw204 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw204 permutation258 hz
    injectiveMoment H raw204step0 = injectiveMoment H raw204step1 := by
      have hz : ∀ j, raw204step0 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw204step1 = (fun i j => raw204step0 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw204step0 permutation104 hz
    _ = injectiveMoment H node16 := by rfl

def raw205 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]

def raw205step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical205 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw205 = injectiveMoment H node69 := by
  calc
    injectiveMoment H raw205 = injectiveMoment H raw205step0 := by
      have hz : ∀ j, raw205 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw205step0 = (fun i j => raw205 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw205 permutation241 hz
    _ = injectiveMoment H node69 := by rfl

def raw206 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![0, 0], ![2, -2]]

def raw206step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical206 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw206 = injectiveMoment H node16 := by
  calc
    injectiveMoment H raw206 = injectiveMoment H raw206step0 := by
      have hz : ∀ j, raw206 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw206step0 = (fun i j => raw206 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw206 permutation104 hz
    _ = injectiveMoment H node16 := by rfl

def raw207 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

theorem canonical207 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw207 = injectiveMoment H node69 := by
  rfl

def raw208 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical208 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw208 = injectiveMoment H node16 := by
  rfl

def raw209 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2], ![0, 0]]

def raw209step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical209 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw209 = injectiveMoment H node16 := by
  calc
    injectiveMoment H raw209 = injectiveMoment H raw209step0 := by
      have hz : ∀ j, raw209 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw209step0 = (fun i j => raw209 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw209 permutation128 hz
    _ = injectiveMoment H node16 := by rfl

def raw210 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![2, -2], ![1, -1]]

def raw210step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw210 = injectiveMoment H node16 := by
  calc
    injectiveMoment H raw210 = injectiveMoment H raw210step0 := by
      have heq : raw210step0 = (fun i j => raw210 (permutation10 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw210 permutation10 permutation1
    _ = injectiveMoment H node16 := by rfl

def raw211 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]

theorem canonical211 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw211 = injectiveMoment H node8 := by
  rfl

def raw212 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![0, 0], ![2, -2]]

def raw212step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]

theorem canonical212 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw212 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw212 = injectiveMoment H raw212step0 := by
      have hz : ∀ j, raw212 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw212step0 = (fun i j => raw212 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw212 permutation21 hz
    _ = injectiveMoment H node9 := by rfl

def raw213 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![1, -1], ![1, -1]]

def raw213step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]

theorem canonical213 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw213 = injectiveMoment H node16 := by
  calc
    injectiveMoment H raw213 = injectiveMoment H raw213step0 := by
      have heq : raw213step0 = (fun i j => raw213 (permutation12 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw213 permutation12 permutation1
    _ = injectiveMoment H node16 := by rfl

def raw214 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]

theorem canonical214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw214 = injectiveMoment H node9 := by
  rfl

def raw215 : Matrix (Fin 2) (Fin 2) ℤ := ![![-4, 4], ![4, -4]]

theorem canonical215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw215 = injectiveMoment H node2 := by
  rfl

def raw216 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 5, -1], ![4, -5, 1]]

def raw216step0 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![5, -5], ![-1, 1]]

def raw216step1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![4, -4]]

theorem canonical216 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw216 = injectiveMoment H node6 := by
  calc
    injectiveMoment H raw216 = injectiveMoment H raw216step0 := by
      have heq : raw216step0 = raw216.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw216).symm
    injectiveMoment H raw216step0 = injectiveMoment H raw216step1 := by
      have heq : raw216step1 = (fun i j => raw216step0 (permutation6 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw216step0 permutation6 permutation2
    _ = injectiveMoment H node6 := by rfl

def raw217 : Matrix (Fin 2) (Fin 4) ℤ := ![![-3, -2, 2, 3], ![3, 2, -2, -3]]

def raw217step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]

theorem canonical217 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw217 = injectiveMoment H node23 := by
  calc
    injectiveMoment H raw217 = injectiveMoment H raw217step0 := by
      have heq : raw217step0 = raw217.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw217).symm
    _ = injectiveMoment H node23 := by rfl

def raw218 : Matrix (Fin 2) (Fin 4) ℤ := ![![-3, -2, 3, 2], ![3, 2, -3, -2]]

def raw218step0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![3, -3], ![2, -2]]

def raw218step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]

theorem canonical218 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw218 = injectiveMoment H node23 := by
  calc
    injectiveMoment H raw218 = injectiveMoment H raw218step0 := by
      have heq : raw218step0 = raw218.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw218).symm
    injectiveMoment H raw218step0 = injectiveMoment H raw218step1 := by
      have heq : raw218step1 = (fun i j => raw218step0 (permutation10 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw218step0 permutation10 permutation1
    _ = injectiveMoment H node23 := by rfl

def raw219 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

theorem canonical219 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw219 = injectiveMoment H node297 := by
  rfl

def raw220 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]

def raw220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

theorem canonical220 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw220 = injectiveMoment H node389 := by
  calc
    injectiveMoment H raw220 = injectiveMoment H raw220step0 := by
      have heq : raw220step0 = (fun i j => raw220 (permutation49 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw220 permutation49 permutation5
    _ = injectiveMoment H node389 := by rfl

def raw221 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

theorem canonical221 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw221 = injectiveMoment H node298 := by
  rfl

def raw222 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

theorem canonical222 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw222 = injectiveMoment H node299 := by
  rfl

def raw223 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

theorem canonical223 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw223 = injectiveMoment H node300 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI

import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5952 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0]]

def raw5952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical5952 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5952 = injectiveMoment H node876 := by
  calc
    injectiveMoment H raw5952 = injectiveMoment H raw5952step0 := by
      have heq : raw5952step0 = (fun i j => raw5952 (permutation80 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5952 permutation80 permutation4
    _ = injectiveMoment H node876 := by rfl

def raw5953 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3]]

def raw5953step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3]]

theorem canonical5953 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5953 = injectiveMoment H node267 := by
  calc
    injectiveMoment H raw5953 = injectiveMoment H raw5953step0 := by
      have heq : raw5953step0 = (fun i j => raw5953 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5953 permutation11 permutation3
    _ = injectiveMoment H node267 := by rfl

def raw5954 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]

def raw5954step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical5954 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5954 = injectiveMoment H node271 := by
  calc
    injectiveMoment H raw5954 = injectiveMoment H raw5954step0 := by
      have hz : ∀ j, raw5954 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5954step0 = (fun i j => raw5954 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5954 permutation80 hz
    _ = injectiveMoment H node271 := by rfl

def raw5955 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0]]

def raw5955step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical5955 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5955 = injectiveMoment H node272 := by
  calc
    injectiveMoment H raw5955 = injectiveMoment H raw5955step0 := by
      have hz : ∀ j, raw5955 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5955step0 = (fun i j => raw5955 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5955 permutation80 hz
    _ = injectiveMoment H node272 := by rfl

def raw5956 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2]]

def raw5956step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, 1, -2]]

theorem canonical5956 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5956 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw5956 = injectiveMoment H raw5956step0 := by
      have hz : ∀ j, raw5956 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5956step0 = (fun i j => raw5956 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5956 permutation21 hz
    _ = injectiveMoment H node56 := by rfl

def raw5957 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2]]

def raw5957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

theorem canonical5957 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5957 = injectiveMoment H node881 := by
  calc
    injectiveMoment H raw5957 = injectiveMoment H raw5957step0 := by
      have heq : raw5957step0 = (fun i j => raw5957 (permutation45 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5957 permutation45 permutation3
    _ = injectiveMoment H node881 := by rfl

def raw5958 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1]]

def raw5958step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical5958 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5958 = injectiveMoment H node271 := by
  calc
    injectiveMoment H raw5958 = injectiveMoment H raw5958step0 := by
      have hz : ∀ j, raw5958 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5958step0 = (fun i j => raw5958 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5958 permutation104 hz
    _ = injectiveMoment H node271 := by rfl

def raw5959 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical5959 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5959 = injectiveMoment H node884 := by
  rfl

def raw5960 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

theorem canonical5960 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5960 = injectiveMoment H node885 := by
  rfl

def raw5961 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]

def raw5961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical5961 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5961 = injectiveMoment H node884 := by
  calc
    injectiveMoment H raw5961 = injectiveMoment H raw5961step0 := by
      have heq : raw5961step0 = (fun i j => raw5961 (permutation34 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5961 permutation34 permutation3
    _ = injectiveMoment H node884 := by rfl

def raw5962 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical5962 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5962 = injectiveMoment H node271 := by
  rfl

def raw5963 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1]]

def raw5963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

theorem canonical5963 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5963 = injectiveMoment H node882 := by
  calc
    injectiveMoment H raw5963 = injectiveMoment H raw5963step0 := by
      have heq : raw5963step0 = (fun i j => raw5963 (permutation45 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5963 permutation45 permutation3
    _ = injectiveMoment H node882 := by rfl

def raw5964 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1]]

def raw5964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

theorem canonical5964 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5964 = injectiveMoment H node885 := by
  calc
    injectiveMoment H raw5964 = injectiveMoment H raw5964step0 := by
      have heq : raw5964step0 = (fun i j => raw5964 (permutation35 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5964 permutation35 permutation3
    _ = injectiveMoment H node885 := by rfl

def raw5965 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical5965 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5965 = injectiveMoment H node272 := by
  rfl

def raw5966 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0]]

def raw5966step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical5966 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5966 = injectiveMoment H node272 := by
  calc
    injectiveMoment H raw5966 = injectiveMoment H raw5966step0 := by
      have hz : ∀ j, raw5966 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw5966step0 = (fun i j => raw5966 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5966 permutation128 hz
    _ = injectiveMoment H node272 := by rfl

def raw5967 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0]]

def raw5967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical5967 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5967 = injectiveMoment H node883 := by
  calc
    injectiveMoment H raw5967 = injectiveMoment H raw5967step0 := by
      have heq : raw5967step0 = (fun i j => raw5967 (permutation45 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5967 permutation45 permutation3
    _ = injectiveMoment H node883 := by rfl

def raw5968 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1]]

theorem canonical5968 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5968 = injectiveMoment H node273 := by
  rfl

def raw5969 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![0, -1, 1]]

def raw5969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

theorem canonical5969 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5969 = injectiveMoment H node883 := by
  calc
    injectiveMoment H raw5969 = injectiveMoment H raw5969step0 := by
      have heq : raw5969step0 = (fun i j => raw5969 (permutation51 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5969 permutation51 permutation3
    _ = injectiveMoment H node883 := by rfl

def raw5970 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, -2, 1], ![0, 3, -3]]

def raw5970step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1]]

theorem canonical5970 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5970 = injectiveMoment H node273 := by
  calc
    injectiveMoment H raw5970 = injectiveMoment H raw5970step0 := by
      have heq : raw5970step0 = (fun i j => raw5970 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5970 permutation10 permutation3
    _ = injectiveMoment H node273 := by rfl

def raw5971 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 2, -2]]

def raw5971step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical5971 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5971 = injectiveMoment H node272 := by
  calc
    injectiveMoment H raw5971 = injectiveMoment H raw5971step0 := by
      have heq : raw5971step0 = (fun i j => raw5971 (permutation10 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5971 permutation10 permutation3
    _ = injectiveMoment H node272 := by rfl

def raw5972 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, 1, -2]]

theorem canonical5972 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5972 = injectiveMoment H node56 := by
  rfl

def raw5973 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2]]

def raw5973step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

theorem canonical5973 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5973 = injectiveMoment H node268 := by
  calc
    injectiveMoment H raw5973 = injectiveMoment H raw5973step0 := by
      have heq : raw5973step0 = (fun i j => raw5973 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5973 permutation11 permutation3
    _ = injectiveMoment H node268 := by rfl

def raw5974 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1]]

def raw5974step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

theorem canonical5974 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5974 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw5974 = injectiveMoment H raw5974step0 := by
      have hz : ∀ j, raw5974 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5974step0 = (fun i j => raw5974 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5974 permutation21 hz
    _ = injectiveMoment H node57 := by rfl

def raw5975 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1]]

def raw5975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

theorem canonical5975 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5975 = injectiveMoment H node885 := by
  calc
    injectiveMoment H raw5975 = injectiveMoment H raw5975step0 := by
      have heq : raw5975step0 = (fun i j => raw5975 (permutation41 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5975 permutation41 permutation3
    _ = injectiveMoment H node885 := by rfl

def raw5976 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0]]

def raw5976step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical5976 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5976 = injectiveMoment H node272 := by
  calc
    injectiveMoment H raw5976 = injectiveMoment H raw5976step0 := by
      have heq : raw5976step0 = (fun i j => raw5976 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5976 permutation11 permutation3
    _ = injectiveMoment H node272 := by rfl

def raw5977 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1]]

theorem canonical5977 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5977 = injectiveMoment H node274 := by
  rfl

def raw5978 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![0, 1, -1]]

def raw5978step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

theorem canonical5978 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5978 = injectiveMoment H node272 := by
  calc
    injectiveMoment H raw5978 = injectiveMoment H raw5978step0 := by
      have heq : raw5978step0 = (fun i j => raw5978 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5978 permutation13 permutation3
    _ = injectiveMoment H node272 := by rfl

def raw5979 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![1, 0, -1]]

theorem canonical5979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5979 = injectiveMoment H node57 := by
  rfl

def raw5980 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![0, -2, 2], ![1, 1, -2]]

def raw5980step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 3, -3], ![1, 1, -2]]

theorem canonical5980 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5980 = injectiveMoment H node265 := by
  calc
    injectiveMoment H raw5980 = injectiveMoment H raw5980step0 := by
      have heq : raw5980step0 = (fun i j => raw5980 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5980 permutation11 permutation3
    _ = injectiveMoment H node265 := by rfl

def raw5981 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1]]

def raw5981step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

theorem canonical5981 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5981 = injectiveMoment H node269 := by
  calc
    injectiveMoment H raw5981 = injectiveMoment H raw5981step0 := by
      have heq : raw5981step0 = (fun i j => raw5981 (permutation11 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5981 permutation11 permutation3
    _ = injectiveMoment H node269 := by rfl

def raw5982 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

theorem canonical5982 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5982 = injectiveMoment H node58 := by
  rfl

def raw5983 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0], ![0, 0, 0]]

def raw5983step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 3, -3], ![1, -1, 0]]

theorem canonical5983 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5983 = injectiveMoment H node58 := by
  calc
    injectiveMoment H raw5983 = injectiveMoment H raw5983step0 := by
      have hz : ∀ j, raw5983 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw5983step0 = (fun i j => raw5983 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5983 permutation27 hz
    _ = injectiveMoment H node58 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

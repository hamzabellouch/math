import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1952 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

theorem canonical1952 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1952 = injectiveMoment H node1695 := by
  rfl

def raw1953 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

theorem canonical1953 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1953 = injectiveMoment H node1696 := by
  rfl

def raw1954 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 0, -2]]

theorem canonical1954 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1954 = injectiveMoment H node1697 := by
  rfl

def raw1955 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical1955 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1955 = injectiveMoment H node1698 := by
  rfl

def raw1956 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1956step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical1956 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1956 = injectiveMoment H node2428 := by
  calc
    injectiveMoment H raw1956 = injectiveMoment H raw1956step0 := by
      have heq : raw1956step0 = (fun i j => raw1956 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1956 permutation36 permutation15
    _ = injectiveMoment H node2428 := by rfl

def raw1957 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw1957step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical1957 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1957 = injectiveMoment H node2428 := by
  calc
    injectiveMoment H raw1957 = injectiveMoment H raw1957step0 := by
      have heq : raw1957step0 = (fun i j => raw1957 (permutation38 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1957 permutation38 permutation15
    _ = injectiveMoment H node2428 := by rfl

def raw1958 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, 0, -1, -1]]

def raw1958step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical1958 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1958 = injectiveMoment H node807 := by
  calc
    injectiveMoment H raw1958 = injectiveMoment H raw1958step0 := by
      have heq : raw1958step0 = (fun i j => raw1958 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1958 permutation10 permutation15
    _ = injectiveMoment H node807 := by rfl

def raw1959 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1]]

theorem canonical1959 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1959 = injectiveMoment H node1699 := by
  rfl

def raw1960 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

theorem canonical1960 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1960 = injectiveMoment H node1700 := by
  rfl

def raw1961 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

theorem canonical1961 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1961 = injectiveMoment H node1701 := by
  rfl

def raw1962 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def raw1962step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical1962 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1962 = injectiveMoment H node2426 := by
  calc
    injectiveMoment H raw1962 = injectiveMoment H raw1962step0 := by
      have heq : raw1962step0 = (fun i j => raw1962 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1962 permutation36 permutation15
    _ = injectiveMoment H node2426 := by rfl

def raw1963 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1963step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical1963 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1963 = injectiveMoment H node2427 := by
  calc
    injectiveMoment H raw1963 = injectiveMoment H raw1963step0 := by
      have heq : raw1963step0 = (fun i j => raw1963 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1963 permutation36 permutation15
    _ = injectiveMoment H node2427 := by rfl

def raw1964 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw1964step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical1964 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1964 = injectiveMoment H node806 := by
  calc
    injectiveMoment H raw1964 = injectiveMoment H raw1964step0 := by
      have heq : raw1964step0 = (fun i j => raw1964 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1964 permutation10 permutation15
    _ = injectiveMoment H node806 := by rfl

def raw1965 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -3, 1], ![2, -1, 1, -2]]

theorem canonical1965 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1965 = injectiveMoment H node480 := by
  rfl

def raw1966 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical1966 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1966 = injectiveMoment H node1702 := by
  rfl

def raw1967 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, -1, 0, -1]]

def raw1967step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 0, 2, -1], ![0, 2, -2, 0], ![3, -2, 0, -1]]

def raw1967step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

theorem canonical1967 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1967 = injectiveMoment H node474 := by
  calc
    injectiveMoment H raw1967 = injectiveMoment H raw1967step0 := by
      have heq : raw1967step0 = raw1967.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1967).symm
    injectiveMoment H raw1967step0 = injectiveMoment H raw1967step1 := by
      have heq : raw1967step1 = (fun i j => raw1967step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1967step0 permutation29 permutation20
    _ = injectiveMoment H node474 := by rfl

def raw1968 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical1968 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1968 = injectiveMoment H node1703 := by
  rfl

def raw1969 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical1969 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1969 = injectiveMoment H node1704 := by
  rfl

def raw1970 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -1, -1, 0]]

theorem canonical1970 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1970 = injectiveMoment H node481 := by
  rfl

def raw1971 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem canonical1971 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1971 = injectiveMoment H node1705 := by
  rfl

def raw1972 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

theorem canonical1972 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1972 = injectiveMoment H node1706 := by
  rfl

def raw1973 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, -1, -1, 1]]

def raw1973step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem canonical1973 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1973 = injectiveMoment H node1705 := by
  calc
    injectiveMoment H raw1973 = injectiveMoment H raw1973step0 := by
      have heq : raw1973step0 = (fun i j => raw1973 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1973 permutation34 permutation9
    _ = injectiveMoment H node1705 := by rfl

def raw1974 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![2, -1, -2, 1]]

theorem canonical1974 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1974 = injectiveMoment H node482 := by
  rfl

def raw1975 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, -1, -2]]

theorem canonical1975 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1975 = injectiveMoment H node483 := by
  rfl

def raw1976 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 2, -2, -1]]

def raw1976step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, -1, 2], ![0, 2, 0, -2], ![3, -2, 0, -1]]

def raw1976step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, 0, 1, -2], ![0, -2, 0, 2], ![-3, 2, 0, 1]]

def raw1976step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical1976 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1976 = injectiveMoment H node1235 := by
  calc
    injectiveMoment H raw1976 = injectiveMoment H raw1976step0 := by
      have heq : raw1976step0 = raw1976.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1976).symm
    injectiveMoment H raw1976step0 = injectiveMoment H raw1976step1 := by
      have heq : raw1976step1 = -raw1976step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1976step0).symm
    injectiveMoment H raw1976step1 = injectiveMoment H raw1976step2 := by
      have heq : raw1976step2 = (fun i j => raw1976step1 (permutation12 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1976step1 permutation12 permutation24
    _ = injectiveMoment H node1235 := by rfl

def raw1977 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, 0, -2, 1], ![1, 1, 0, -2]]

def raw1977step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem canonical1977 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1977 = injectiveMoment H node804 := by
  calc
    injectiveMoment H raw1977 = injectiveMoment H raw1977step0 := by
      have heq : raw1977step0 = (fun i j => raw1977 (permutation9 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1977 permutation9 permutation15
    _ = injectiveMoment H node804 := by rfl

def raw1978 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw1978step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, -1, -1]]

theorem canonical1978 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1978 = injectiveMoment H node805 := by
  calc
    injectiveMoment H raw1978 = injectiveMoment H raw1978step0 := by
      have heq : raw1978step0 = (fun i j => raw1978 (permutation9 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1978 permutation9 permutation15
    _ = injectiveMoment H node805 := by rfl

def raw1979 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw1979step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 0, 1], ![0, 2, 0, -2], ![3, -2, -1, 0]]

def raw1979step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem canonical1979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1979 = injectiveMoment H node802 := by
  calc
    injectiveMoment H raw1979 = injectiveMoment H raw1979step0 := by
      have heq : raw1979step0 = raw1979.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1979).symm
    injectiveMoment H raw1979step0 = injectiveMoment H raw1979step1 := by
      have heq : raw1979step1 = (fun i j => raw1979step0 (permutation30 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1979step0 permutation30 permutation24
    _ = injectiveMoment H node802 := by rfl

def raw1980 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, 0, 0, -1]]

def raw1980step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 0, 1, 0], ![0, 2, -2, 0], ![3, -2, 0, -1]]

def raw1980step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem canonical1980 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1980 = injectiveMoment H node802 := by
  calc
    injectiveMoment H raw1980 = injectiveMoment H raw1980step0 := by
      have heq : raw1980step0 = raw1980.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1980).symm
    injectiveMoment H raw1980step0 = injectiveMoment H raw1980step1 := by
      have heq : raw1980step1 = (fun i j => raw1980step0 (permutation30 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1980step0 permutation30 permutation30
    _ = injectiveMoment H node802 := by rfl

def raw1981 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 0, -1, 0]]

def raw1981step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, -1, -1]]

theorem canonical1981 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1981 = injectiveMoment H node805 := by
  calc
    injectiveMoment H raw1981 = injectiveMoment H raw1981step0 := by
      have heq : raw1981step0 = (fun i j => raw1981 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1981 permutation10 permutation15
    _ = injectiveMoment H node805 := by rfl

def raw1982 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, 1, 0, -2], ![1, 0, -2, 1]]

def raw1982step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem canonical1982 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1982 = injectiveMoment H node804 := by
  calc
    injectiveMoment H raw1982 = injectiveMoment H raw1982step0 := by
      have heq : raw1982step0 = (fun i j => raw1982 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1982 permutation10 permutation15
    _ = injectiveMoment H node804 := by rfl

def raw1983 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, 2, -1, -2], ![1, -1, -1, 1]]

def raw1983step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, -1, -2]]

theorem canonical1983 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1983 = injectiveMoment H node483 := by
  calc
    injectiveMoment H raw1983 = injectiveMoment H raw1983step0 := by
      have heq : raw1983step0 = (fun i j => raw1983 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1983 permutation10 permutation9
    _ = injectiveMoment H node483 := by rfl

end MUB6.Certificate.PairSemantics

end OAI

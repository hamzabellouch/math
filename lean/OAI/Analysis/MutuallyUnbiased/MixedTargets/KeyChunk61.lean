import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound61
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1952 : keyMomentRows (1952 : Fin 2886) =
    keyMomentRow1952 := by decide +kernel

theorem keyMomentRowsAt1953 : keyMomentRows (1953 : Fin 2886) =
    keyMomentRow1953 := by decide +kernel

theorem keyMomentRowsAt1954 : keyMomentRows (1954 : Fin 2886) =
    keyMomentRow1954 := by decide +kernel

theorem keyMomentRowsAt1955 : keyMomentRows (1955 : Fin 2886) =
    keyMomentRow1955 := by decide +kernel

theorem keyMomentRowsAt1956 : keyMomentRows (1956 : Fin 2886) =
    keyMomentRow1956 := by decide +kernel

theorem keyMomentRowsAt1957 : keyMomentRows (1957 : Fin 2886) =
    keyMomentRow1957 := by decide +kernel

theorem keyMomentRowsAt1958 : keyMomentRows (1958 : Fin 2886) =
    keyMomentRow1958 := by decide +kernel

theorem keyMomentRowsAt1959 : keyMomentRows (1959 : Fin 2886) =
    keyMomentRow1959 := by decide +kernel

theorem keyMomentRowsAt1960 : keyMomentRows (1960 : Fin 2886) =
    keyMomentRow1960 := by decide +kernel

theorem keyMomentRowsAt1961 : keyMomentRows (1961 : Fin 2886) =
    keyMomentRow1961 := by decide +kernel

theorem keyMomentRowsAt1962 : keyMomentRows (1962 : Fin 2886) =
    keyMomentRow1962 := by decide +kernel

theorem keyMomentRowsAt1963 : keyMomentRows (1963 : Fin 2886) =
    keyMomentRow1963 := by decide +kernel

theorem keyMomentRowsAt1964 : keyMomentRows (1964 : Fin 2886) =
    keyMomentRow1964 := by decide +kernel

theorem keyMomentRowsAt1965 : keyMomentRows (1965 : Fin 2886) =
    keyMomentRow1965 := by decide +kernel

theorem keyMomentRowsAt1966 : keyMomentRows (1966 : Fin 2886) =
    keyMomentRow1966 := by decide +kernel

theorem keyMomentRowsAt1967 : keyMomentRows (1967 : Fin 2886) =
    keyMomentRow1967 := by decide +kernel

theorem keyMomentRowsAt1968 : keyMomentRows (1968 : Fin 2886) =
    keyMomentRow1968 := by decide +kernel

theorem keyMomentRowsAt1969 : keyMomentRows (1969 : Fin 2886) =
    keyMomentRow1969 := by decide +kernel

theorem keyMomentRowsAt1970 : keyMomentRows (1970 : Fin 2886) =
    keyMomentRow1970 := by decide +kernel

theorem keyMomentRowsAt1971 : keyMomentRows (1971 : Fin 2886) =
    keyMomentRow1971 := by decide +kernel

theorem keyMomentRowsAt1972 : keyMomentRows (1972 : Fin 2886) =
    keyMomentRow1972 := by decide +kernel

theorem keyMomentRowsAt1973 : keyMomentRows (1973 : Fin 2886) =
    keyMomentRow1973 := by decide +kernel

theorem keyMomentRowsAt1974 : keyMomentRows (1974 : Fin 2886) =
    keyMomentRow1974 := by decide +kernel

theorem keyMomentRowsAt1975 : keyMomentRows (1975 : Fin 2886) =
    keyMomentRow1975 := by decide +kernel

theorem keyMomentRowsAt1976 : keyMomentRows (1976 : Fin 2886) =
    keyMomentRow1976 := by decide +kernel

theorem keyMomentRowsAt1977 : keyMomentRows (1977 : Fin 2886) =
    keyMomentRow1977 := by decide +kernel

theorem keyMomentRowsAt1978 : keyMomentRows (1978 : Fin 2886) =
    keyMomentRow1978 := by decide +kernel

theorem keyMomentRowsAt1979 : keyMomentRows (1979 : Fin 2886) =
    keyMomentRow1979 := by decide +kernel

theorem keyMomentRowsAt1980 : keyMomentRows (1980 : Fin 2886) =
    keyMomentRow1980 := by decide +kernel

theorem keyMomentRowsAt1981 : keyMomentRows (1981 : Fin 2886) =
    keyMomentRow1981 := by decide +kernel

theorem keyMomentRowsAt1982 : keyMomentRows (1982 : Fin 2886) =
    keyMomentRow1982 := by decide +kernel

theorem keyMomentRowsAt1983 : keyMomentRows (1983 : Fin 2886) =
    keyMomentRow1983 := by decide +kernel

theorem keyMomentChunkSound61 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 61) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1952 ∨ k.val = 1953 ∨ k.val = 1954 ∨ k.val = 1955 ∨ k.val = 1956 ∨ k.val = 1957 ∨ k.val = 1958 ∨ k.val = 1959 ∨ k.val = 1960 ∨ k.val = 1961 ∨ k.val = 1962 ∨ k.val = 1963 ∨ k.val = 1964 ∨ k.val = 1965 ∨ k.val = 1966 ∨ k.val = 1967 ∨ k.val = 1968 ∨ k.val = 1969 ∨ k.val = 1970 ∨ k.val = 1971 ∨ k.val = 1972 ∨ k.val = 1973 ∨ k.val = 1974 ∨ k.val = 1975 ∨ k.val = 1976 ∨ k.val = 1977 ∨ k.val = 1978 ∨ k.val = 1979 ∨ k.val = 1980 ∨ k.val = 1981 ∨ k.val = 1982 ∨ k.val = 1983 := by omega
  rcases heq with h1952 | h1953 | h1954 | h1955 | h1956 | h1957 | h1958 | h1959 | h1960 | h1961 | h1962 | h1963 | h1964 | h1965 | h1966 | h1967 | h1968 | h1969 | h1970 | h1971 | h1972 | h1973 | h1974 | h1975 | h1976 | h1977 | h1978 | h1979 | h1980 | h1981 | h1982 | h1983
  · have he : k = (1952 : Fin 2886) := Fin.ext h1952
    subst k
    rw [keyMomentRowsAt1952]
    exact keyMoment1952 B hB
  · have he : k = (1953 : Fin 2886) := Fin.ext h1953
    subst k
    rw [keyMomentRowsAt1953]
    exact keyMoment1953 B hB
  · have he : k = (1954 : Fin 2886) := Fin.ext h1954
    subst k
    rw [keyMomentRowsAt1954]
    exact keyMoment1954 B hB
  · have he : k = (1955 : Fin 2886) := Fin.ext h1955
    subst k
    rw [keyMomentRowsAt1955]
    exact keyMoment1955 B hB
  · have he : k = (1956 : Fin 2886) := Fin.ext h1956
    subst k
    rw [keyMomentRowsAt1956]
    exact keyMoment1956 B hB
  · have he : k = (1957 : Fin 2886) := Fin.ext h1957
    subst k
    rw [keyMomentRowsAt1957]
    exact keyMoment1957 B hB
  · have he : k = (1958 : Fin 2886) := Fin.ext h1958
    subst k
    rw [keyMomentRowsAt1958]
    exact keyMoment1958 B hB
  · have he : k = (1959 : Fin 2886) := Fin.ext h1959
    subst k
    rw [keyMomentRowsAt1959]
    exact keyMoment1959 B hB
  · have he : k = (1960 : Fin 2886) := Fin.ext h1960
    subst k
    rw [keyMomentRowsAt1960]
    exact keyMoment1960 B hB
  · have he : k = (1961 : Fin 2886) := Fin.ext h1961
    subst k
    rw [keyMomentRowsAt1961]
    exact keyMoment1961 B hB
  · have he : k = (1962 : Fin 2886) := Fin.ext h1962
    subst k
    rw [keyMomentRowsAt1962]
    exact keyMoment1962 B hB
  · have he : k = (1963 : Fin 2886) := Fin.ext h1963
    subst k
    rw [keyMomentRowsAt1963]
    exact keyMoment1963 B hB
  · have he : k = (1964 : Fin 2886) := Fin.ext h1964
    subst k
    rw [keyMomentRowsAt1964]
    exact keyMoment1964 B hB
  · have he : k = (1965 : Fin 2886) := Fin.ext h1965
    subst k
    rw [keyMomentRowsAt1965]
    exact keyMoment1965 B hB
  · have he : k = (1966 : Fin 2886) := Fin.ext h1966
    subst k
    rw [keyMomentRowsAt1966]
    exact keyMoment1966 B hB
  · have he : k = (1967 : Fin 2886) := Fin.ext h1967
    subst k
    rw [keyMomentRowsAt1967]
    exact keyMoment1967 B hB
  · have he : k = (1968 : Fin 2886) := Fin.ext h1968
    subst k
    rw [keyMomentRowsAt1968]
    exact keyMoment1968 B hB
  · have he : k = (1969 : Fin 2886) := Fin.ext h1969
    subst k
    rw [keyMomentRowsAt1969]
    exact keyMoment1969 B hB
  · have he : k = (1970 : Fin 2886) := Fin.ext h1970
    subst k
    rw [keyMomentRowsAt1970]
    exact keyMoment1970 B hB
  · have he : k = (1971 : Fin 2886) := Fin.ext h1971
    subst k
    rw [keyMomentRowsAt1971]
    exact keyMoment1971 B hB
  · have he : k = (1972 : Fin 2886) := Fin.ext h1972
    subst k
    rw [keyMomentRowsAt1972]
    exact keyMoment1972 B hB
  · have he : k = (1973 : Fin 2886) := Fin.ext h1973
    subst k
    rw [keyMomentRowsAt1973]
    exact keyMoment1973 B hB
  · have he : k = (1974 : Fin 2886) := Fin.ext h1974
    subst k
    rw [keyMomentRowsAt1974]
    exact keyMoment1974 B hB
  · have he : k = (1975 : Fin 2886) := Fin.ext h1975
    subst k
    rw [keyMomentRowsAt1975]
    exact keyMoment1975 B hB
  · have he : k = (1976 : Fin 2886) := Fin.ext h1976
    subst k
    rw [keyMomentRowsAt1976]
    exact keyMoment1976 B hB
  · have he : k = (1977 : Fin 2886) := Fin.ext h1977
    subst k
    rw [keyMomentRowsAt1977]
    exact keyMoment1977 B hB
  · have he : k = (1978 : Fin 2886) := Fin.ext h1978
    subst k
    rw [keyMomentRowsAt1978]
    exact keyMoment1978 B hB
  · have he : k = (1979 : Fin 2886) := Fin.ext h1979
    subst k
    rw [keyMomentRowsAt1979]
    exact keyMoment1979 B hB
  · have he : k = (1980 : Fin 2886) := Fin.ext h1980
    subst k
    rw [keyMomentRowsAt1980]
    exact keyMoment1980 B hB
  · have he : k = (1981 : Fin 2886) := Fin.ext h1981
    subst k
    rw [keyMomentRowsAt1981]
    exact keyMoment1981 B hB
  · have he : k = (1982 : Fin 2886) := Fin.ext h1982
    subst k
    rw [keyMomentRowsAt1982]
    exact keyMoment1982 B hB
  · have he : k = (1983 : Fin 2886) := Fin.ext h1983
    subst k
    rw [keyMomentRowsAt1983]
    exact keyMoment1983 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI

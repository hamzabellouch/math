import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound63
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2016 : keyMomentRows (2016 : Fin 2886) =
    keyMomentRow2016 := by decide +kernel

theorem keyMomentRowsAt2017 : keyMomentRows (2017 : Fin 2886) =
    keyMomentRow2017 := by decide +kernel

theorem keyMomentRowsAt2018 : keyMomentRows (2018 : Fin 2886) =
    keyMomentRow2018 := by decide +kernel

theorem keyMomentRowsAt2019 : keyMomentRows (2019 : Fin 2886) =
    keyMomentRow2019 := by decide +kernel

theorem keyMomentRowsAt2020 : keyMomentRows (2020 : Fin 2886) =
    keyMomentRow2020 := by decide +kernel

theorem keyMomentRowsAt2021 : keyMomentRows (2021 : Fin 2886) =
    keyMomentRow2021 := by decide +kernel

theorem keyMomentRowsAt2022 : keyMomentRows (2022 : Fin 2886) =
    keyMomentRow2022 := by decide +kernel

theorem keyMomentRowsAt2023 : keyMomentRows (2023 : Fin 2886) =
    keyMomentRow2023 := by decide +kernel

theorem keyMomentRowsAt2024 : keyMomentRows (2024 : Fin 2886) =
    keyMomentRow2024 := by decide +kernel

theorem keyMomentRowsAt2025 : keyMomentRows (2025 : Fin 2886) =
    keyMomentRow2025 := by decide +kernel

theorem keyMomentRowsAt2026 : keyMomentRows (2026 : Fin 2886) =
    keyMomentRow2026 := by decide +kernel

theorem keyMomentRowsAt2027 : keyMomentRows (2027 : Fin 2886) =
    keyMomentRow2027 := by decide +kernel

theorem keyMomentRowsAt2028 : keyMomentRows (2028 : Fin 2886) =
    keyMomentRow2028 := by decide +kernel

theorem keyMomentRowsAt2029 : keyMomentRows (2029 : Fin 2886) =
    keyMomentRow2029 := by decide +kernel

theorem keyMomentRowsAt2030 : keyMomentRows (2030 : Fin 2886) =
    keyMomentRow2030 := by decide +kernel

theorem keyMomentRowsAt2031 : keyMomentRows (2031 : Fin 2886) =
    keyMomentRow2031 := by decide +kernel

theorem keyMomentRowsAt2032 : keyMomentRows (2032 : Fin 2886) =
    keyMomentRow2032 := by decide +kernel

theorem keyMomentRowsAt2033 : keyMomentRows (2033 : Fin 2886) =
    keyMomentRow2033 := by decide +kernel

theorem keyMomentRowsAt2034 : keyMomentRows (2034 : Fin 2886) =
    keyMomentRow2034 := by decide +kernel

theorem keyMomentRowsAt2035 : keyMomentRows (2035 : Fin 2886) =
    keyMomentRow2035 := by decide +kernel

theorem keyMomentRowsAt2036 : keyMomentRows (2036 : Fin 2886) =
    keyMomentRow2036 := by decide +kernel

theorem keyMomentRowsAt2037 : keyMomentRows (2037 : Fin 2886) =
    keyMomentRow2037 := by decide +kernel

theorem keyMomentRowsAt2038 : keyMomentRows (2038 : Fin 2886) =
    keyMomentRow2038 := by decide +kernel

theorem keyMomentRowsAt2039 : keyMomentRows (2039 : Fin 2886) =
    keyMomentRow2039 := by decide +kernel

theorem keyMomentRowsAt2040 : keyMomentRows (2040 : Fin 2886) =
    keyMomentRow2040 := by decide +kernel

theorem keyMomentRowsAt2041 : keyMomentRows (2041 : Fin 2886) =
    keyMomentRow2041 := by decide +kernel

theorem keyMomentRowsAt2042 : keyMomentRows (2042 : Fin 2886) =
    keyMomentRow2042 := by decide +kernel

theorem keyMomentRowsAt2043 : keyMomentRows (2043 : Fin 2886) =
    keyMomentRow2043 := by decide +kernel

theorem keyMomentRowsAt2044 : keyMomentRows (2044 : Fin 2886) =
    keyMomentRow2044 := by decide +kernel

theorem keyMomentRowsAt2045 : keyMomentRows (2045 : Fin 2886) =
    keyMomentRow2045 := by decide +kernel

theorem keyMomentRowsAt2046 : keyMomentRows (2046 : Fin 2886) =
    keyMomentRow2046 := by decide +kernel

theorem keyMomentRowsAt2047 : keyMomentRows (2047 : Fin 2886) =
    keyMomentRow2047 := by decide +kernel

theorem keyMomentChunkSound63 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 63) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2016 ∨ k.val = 2017 ∨ k.val = 2018 ∨ k.val = 2019 ∨ k.val = 2020 ∨ k.val = 2021 ∨ k.val = 2022 ∨ k.val = 2023 ∨ k.val = 2024 ∨ k.val = 2025 ∨ k.val = 2026 ∨ k.val = 2027 ∨ k.val = 2028 ∨ k.val = 2029 ∨ k.val = 2030 ∨ k.val = 2031 ∨ k.val = 2032 ∨ k.val = 2033 ∨ k.val = 2034 ∨ k.val = 2035 ∨ k.val = 2036 ∨ k.val = 2037 ∨ k.val = 2038 ∨ k.val = 2039 ∨ k.val = 2040 ∨ k.val = 2041 ∨ k.val = 2042 ∨ k.val = 2043 ∨ k.val = 2044 ∨ k.val = 2045 ∨ k.val = 2046 ∨ k.val = 2047 := by omega
  rcases heq with h2016 | h2017 | h2018 | h2019 | h2020 | h2021 | h2022 | h2023 | h2024 | h2025 | h2026 | h2027 | h2028 | h2029 | h2030 | h2031 | h2032 | h2033 | h2034 | h2035 | h2036 | h2037 | h2038 | h2039 | h2040 | h2041 | h2042 | h2043 | h2044 | h2045 | h2046 | h2047
  · have he : k = (2016 : Fin 2886) := Fin.ext h2016
    subst k
    rw [keyMomentRowsAt2016]
    exact keyMoment2016 B hB
  · have he : k = (2017 : Fin 2886) := Fin.ext h2017
    subst k
    rw [keyMomentRowsAt2017]
    exact keyMoment2017 B hB
  · have he : k = (2018 : Fin 2886) := Fin.ext h2018
    subst k
    rw [keyMomentRowsAt2018]
    exact keyMoment2018 B hB
  · have he : k = (2019 : Fin 2886) := Fin.ext h2019
    subst k
    rw [keyMomentRowsAt2019]
    exact keyMoment2019 B hB
  · have he : k = (2020 : Fin 2886) := Fin.ext h2020
    subst k
    rw [keyMomentRowsAt2020]
    exact keyMoment2020 B hB
  · have he : k = (2021 : Fin 2886) := Fin.ext h2021
    subst k
    rw [keyMomentRowsAt2021]
    exact keyMoment2021 B hB
  · have he : k = (2022 : Fin 2886) := Fin.ext h2022
    subst k
    rw [keyMomentRowsAt2022]
    exact keyMoment2022 B hB
  · have he : k = (2023 : Fin 2886) := Fin.ext h2023
    subst k
    rw [keyMomentRowsAt2023]
    exact keyMoment2023 B hB
  · have he : k = (2024 : Fin 2886) := Fin.ext h2024
    subst k
    rw [keyMomentRowsAt2024]
    exact keyMoment2024 B hB
  · have he : k = (2025 : Fin 2886) := Fin.ext h2025
    subst k
    rw [keyMomentRowsAt2025]
    exact keyMoment2025 B hB
  · have he : k = (2026 : Fin 2886) := Fin.ext h2026
    subst k
    rw [keyMomentRowsAt2026]
    exact keyMoment2026 B hB
  · have he : k = (2027 : Fin 2886) := Fin.ext h2027
    subst k
    rw [keyMomentRowsAt2027]
    exact keyMoment2027 B hB
  · have he : k = (2028 : Fin 2886) := Fin.ext h2028
    subst k
    rw [keyMomentRowsAt2028]
    exact keyMoment2028 B hB
  · have he : k = (2029 : Fin 2886) := Fin.ext h2029
    subst k
    rw [keyMomentRowsAt2029]
    exact keyMoment2029 B hB
  · have he : k = (2030 : Fin 2886) := Fin.ext h2030
    subst k
    rw [keyMomentRowsAt2030]
    exact keyMoment2030 B hB
  · have he : k = (2031 : Fin 2886) := Fin.ext h2031
    subst k
    rw [keyMomentRowsAt2031]
    exact keyMoment2031 B hB
  · have he : k = (2032 : Fin 2886) := Fin.ext h2032
    subst k
    rw [keyMomentRowsAt2032]
    exact keyMoment2032 B hB
  · have he : k = (2033 : Fin 2886) := Fin.ext h2033
    subst k
    rw [keyMomentRowsAt2033]
    exact keyMoment2033 B hB
  · have he : k = (2034 : Fin 2886) := Fin.ext h2034
    subst k
    rw [keyMomentRowsAt2034]
    exact keyMoment2034 B hB
  · have he : k = (2035 : Fin 2886) := Fin.ext h2035
    subst k
    rw [keyMomentRowsAt2035]
    exact keyMoment2035 B hB
  · have he : k = (2036 : Fin 2886) := Fin.ext h2036
    subst k
    rw [keyMomentRowsAt2036]
    exact keyMoment2036 B hB
  · have he : k = (2037 : Fin 2886) := Fin.ext h2037
    subst k
    rw [keyMomentRowsAt2037]
    exact keyMoment2037 B hB
  · have he : k = (2038 : Fin 2886) := Fin.ext h2038
    subst k
    rw [keyMomentRowsAt2038]
    exact keyMoment2038 B hB
  · have he : k = (2039 : Fin 2886) := Fin.ext h2039
    subst k
    rw [keyMomentRowsAt2039]
    exact keyMoment2039 B hB
  · have he : k = (2040 : Fin 2886) := Fin.ext h2040
    subst k
    rw [keyMomentRowsAt2040]
    exact keyMoment2040 B hB
  · have he : k = (2041 : Fin 2886) := Fin.ext h2041
    subst k
    rw [keyMomentRowsAt2041]
    exact keyMoment2041 B hB
  · have he : k = (2042 : Fin 2886) := Fin.ext h2042
    subst k
    rw [keyMomentRowsAt2042]
    exact keyMoment2042 B hB
  · have he : k = (2043 : Fin 2886) := Fin.ext h2043
    subst k
    rw [keyMomentRowsAt2043]
    exact keyMoment2043 B hB
  · have he : k = (2044 : Fin 2886) := Fin.ext h2044
    subst k
    rw [keyMomentRowsAt2044]
    exact keyMoment2044 B hB
  · have he : k = (2045 : Fin 2886) := Fin.ext h2045
    subst k
    rw [keyMomentRowsAt2045]
    exact keyMoment2045 B hB
  · have he : k = (2046 : Fin 2886) := Fin.ext h2046
    subst k
    rw [keyMomentRowsAt2046]
    exact keyMoment2046 B hB
  · have he : k = (2047 : Fin 2886) := Fin.ext h2047
    subst k
    rw [keyMomentRowsAt2047]
    exact keyMoment2047 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI

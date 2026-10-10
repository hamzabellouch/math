import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound67
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2144 : keyMomentRows (2144 : Fin 2886) =
    keyMomentRow2144 := by decide +kernel

theorem keyMomentRowsAt2145 : keyMomentRows (2145 : Fin 2886) =
    keyMomentRow2145 := by decide +kernel

theorem keyMomentRowsAt2146 : keyMomentRows (2146 : Fin 2886) =
    keyMomentRow2146 := by decide +kernel

theorem keyMomentRowsAt2147 : keyMomentRows (2147 : Fin 2886) =
    keyMomentRow2147 := by decide +kernel

theorem keyMomentRowsAt2148 : keyMomentRows (2148 : Fin 2886) =
    keyMomentRow2148 := by decide +kernel

theorem keyMomentRowsAt2149 : keyMomentRows (2149 : Fin 2886) =
    keyMomentRow2149 := by decide +kernel

theorem keyMomentRowsAt2150 : keyMomentRows (2150 : Fin 2886) =
    keyMomentRow2150 := by decide +kernel

theorem keyMomentRowsAt2151 : keyMomentRows (2151 : Fin 2886) =
    keyMomentRow2151 := by decide +kernel

theorem keyMomentRowsAt2152 : keyMomentRows (2152 : Fin 2886) =
    keyMomentRow2152 := by decide +kernel

theorem keyMomentRowsAt2153 : keyMomentRows (2153 : Fin 2886) =
    keyMomentRow2153 := by decide +kernel

theorem keyMomentRowsAt2154 : keyMomentRows (2154 : Fin 2886) =
    keyMomentRow2154 := by decide +kernel

theorem keyMomentRowsAt2155 : keyMomentRows (2155 : Fin 2886) =
    keyMomentRow2155 := by decide +kernel

theorem keyMomentRowsAt2156 : keyMomentRows (2156 : Fin 2886) =
    keyMomentRow2156 := by decide +kernel

theorem keyMomentRowsAt2157 : keyMomentRows (2157 : Fin 2886) =
    keyMomentRow2157 := by decide +kernel

theorem keyMomentRowsAt2158 : keyMomentRows (2158 : Fin 2886) =
    keyMomentRow2158 := by decide +kernel

theorem keyMomentRowsAt2159 : keyMomentRows (2159 : Fin 2886) =
    keyMomentRow2159 := by decide +kernel

theorem keyMomentRowsAt2160 : keyMomentRows (2160 : Fin 2886) =
    keyMomentRow2160 := by decide +kernel

theorem keyMomentRowsAt2161 : keyMomentRows (2161 : Fin 2886) =
    keyMomentRow2161 := by decide +kernel

theorem keyMomentRowsAt2162 : keyMomentRows (2162 : Fin 2886) =
    keyMomentRow2162 := by decide +kernel

theorem keyMomentRowsAt2163 : keyMomentRows (2163 : Fin 2886) =
    keyMomentRow2163 := by decide +kernel

theorem keyMomentRowsAt2164 : keyMomentRows (2164 : Fin 2886) =
    keyMomentRow2164 := by decide +kernel

theorem keyMomentRowsAt2165 : keyMomentRows (2165 : Fin 2886) =
    keyMomentRow2165 := by decide +kernel

theorem keyMomentRowsAt2166 : keyMomentRows (2166 : Fin 2886) =
    keyMomentRow2166 := by decide +kernel

theorem keyMomentRowsAt2167 : keyMomentRows (2167 : Fin 2886) =
    keyMomentRow2167 := by decide +kernel

theorem keyMomentRowsAt2168 : keyMomentRows (2168 : Fin 2886) =
    keyMomentRow2168 := by decide +kernel

theorem keyMomentRowsAt2169 : keyMomentRows (2169 : Fin 2886) =
    keyMomentRow2169 := by decide +kernel

theorem keyMomentRowsAt2170 : keyMomentRows (2170 : Fin 2886) =
    keyMomentRow2170 := by decide +kernel

theorem keyMomentRowsAt2171 : keyMomentRows (2171 : Fin 2886) =
    keyMomentRow2171 := by decide +kernel

theorem keyMomentRowsAt2172 : keyMomentRows (2172 : Fin 2886) =
    keyMomentRow2172 := by decide +kernel

theorem keyMomentRowsAt2173 : keyMomentRows (2173 : Fin 2886) =
    keyMomentRow2173 := by decide +kernel

theorem keyMomentRowsAt2174 : keyMomentRows (2174 : Fin 2886) =
    keyMomentRow2174 := by decide +kernel

theorem keyMomentRowsAt2175 : keyMomentRows (2175 : Fin 2886) =
    keyMomentRow2175 := by decide +kernel

theorem keyMomentChunkSound67 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 67) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2144 ∨ k.val = 2145 ∨ k.val = 2146 ∨ k.val = 2147 ∨ k.val = 2148 ∨ k.val = 2149 ∨ k.val = 2150 ∨ k.val = 2151 ∨ k.val = 2152 ∨ k.val = 2153 ∨ k.val = 2154 ∨ k.val = 2155 ∨ k.val = 2156 ∨ k.val = 2157 ∨ k.val = 2158 ∨ k.val = 2159 ∨ k.val = 2160 ∨ k.val = 2161 ∨ k.val = 2162 ∨ k.val = 2163 ∨ k.val = 2164 ∨ k.val = 2165 ∨ k.val = 2166 ∨ k.val = 2167 ∨ k.val = 2168 ∨ k.val = 2169 ∨ k.val = 2170 ∨ k.val = 2171 ∨ k.val = 2172 ∨ k.val = 2173 ∨ k.val = 2174 ∨ k.val = 2175 := by omega
  rcases heq with h2144 | h2145 | h2146 | h2147 | h2148 | h2149 | h2150 | h2151 | h2152 | h2153 | h2154 | h2155 | h2156 | h2157 | h2158 | h2159 | h2160 | h2161 | h2162 | h2163 | h2164 | h2165 | h2166 | h2167 | h2168 | h2169 | h2170 | h2171 | h2172 | h2173 | h2174 | h2175
  · have he : k = (2144 : Fin 2886) := Fin.ext h2144
    subst k
    rw [keyMomentRowsAt2144]
    exact keyMoment2144 B hB
  · have he : k = (2145 : Fin 2886) := Fin.ext h2145
    subst k
    rw [keyMomentRowsAt2145]
    exact keyMoment2145 B hB
  · have he : k = (2146 : Fin 2886) := Fin.ext h2146
    subst k
    rw [keyMomentRowsAt2146]
    exact keyMoment2146 B hB
  · have he : k = (2147 : Fin 2886) := Fin.ext h2147
    subst k
    rw [keyMomentRowsAt2147]
    exact keyMoment2147 B hB
  · have he : k = (2148 : Fin 2886) := Fin.ext h2148
    subst k
    rw [keyMomentRowsAt2148]
    exact keyMoment2148 B hB
  · have he : k = (2149 : Fin 2886) := Fin.ext h2149
    subst k
    rw [keyMomentRowsAt2149]
    exact keyMoment2149 B hB
  · have he : k = (2150 : Fin 2886) := Fin.ext h2150
    subst k
    rw [keyMomentRowsAt2150]
    exact keyMoment2150 B hB
  · have he : k = (2151 : Fin 2886) := Fin.ext h2151
    subst k
    rw [keyMomentRowsAt2151]
    exact keyMoment2151 B hB
  · have he : k = (2152 : Fin 2886) := Fin.ext h2152
    subst k
    rw [keyMomentRowsAt2152]
    exact keyMoment2152 B hB
  · have he : k = (2153 : Fin 2886) := Fin.ext h2153
    subst k
    rw [keyMomentRowsAt2153]
    exact keyMoment2153 B hB
  · have he : k = (2154 : Fin 2886) := Fin.ext h2154
    subst k
    rw [keyMomentRowsAt2154]
    exact keyMoment2154 B hB
  · have he : k = (2155 : Fin 2886) := Fin.ext h2155
    subst k
    rw [keyMomentRowsAt2155]
    exact keyMoment2155 B hB
  · have he : k = (2156 : Fin 2886) := Fin.ext h2156
    subst k
    rw [keyMomentRowsAt2156]
    exact keyMoment2156 B hB
  · have he : k = (2157 : Fin 2886) := Fin.ext h2157
    subst k
    rw [keyMomentRowsAt2157]
    exact keyMoment2157 B hB
  · have he : k = (2158 : Fin 2886) := Fin.ext h2158
    subst k
    rw [keyMomentRowsAt2158]
    exact keyMoment2158 B hB
  · have he : k = (2159 : Fin 2886) := Fin.ext h2159
    subst k
    rw [keyMomentRowsAt2159]
    exact keyMoment2159 B hB
  · have he : k = (2160 : Fin 2886) := Fin.ext h2160
    subst k
    rw [keyMomentRowsAt2160]
    exact keyMoment2160 B hB
  · have he : k = (2161 : Fin 2886) := Fin.ext h2161
    subst k
    rw [keyMomentRowsAt2161]
    exact keyMoment2161 B hB
  · have he : k = (2162 : Fin 2886) := Fin.ext h2162
    subst k
    rw [keyMomentRowsAt2162]
    exact keyMoment2162 B hB
  · have he : k = (2163 : Fin 2886) := Fin.ext h2163
    subst k
    rw [keyMomentRowsAt2163]
    exact keyMoment2163 B hB
  · have he : k = (2164 : Fin 2886) := Fin.ext h2164
    subst k
    rw [keyMomentRowsAt2164]
    exact keyMoment2164 B hB
  · have he : k = (2165 : Fin 2886) := Fin.ext h2165
    subst k
    rw [keyMomentRowsAt2165]
    exact keyMoment2165 B hB
  · have he : k = (2166 : Fin 2886) := Fin.ext h2166
    subst k
    rw [keyMomentRowsAt2166]
    exact keyMoment2166 B hB
  · have he : k = (2167 : Fin 2886) := Fin.ext h2167
    subst k
    rw [keyMomentRowsAt2167]
    exact keyMoment2167 B hB
  · have he : k = (2168 : Fin 2886) := Fin.ext h2168
    subst k
    rw [keyMomentRowsAt2168]
    exact keyMoment2168 B hB
  · have he : k = (2169 : Fin 2886) := Fin.ext h2169
    subst k
    rw [keyMomentRowsAt2169]
    exact keyMoment2169 B hB
  · have he : k = (2170 : Fin 2886) := Fin.ext h2170
    subst k
    rw [keyMomentRowsAt2170]
    exact keyMoment2170 B hB
  · have he : k = (2171 : Fin 2886) := Fin.ext h2171
    subst k
    rw [keyMomentRowsAt2171]
    exact keyMoment2171 B hB
  · have he : k = (2172 : Fin 2886) := Fin.ext h2172
    subst k
    rw [keyMomentRowsAt2172]
    exact keyMoment2172 B hB
  · have he : k = (2173 : Fin 2886) := Fin.ext h2173
    subst k
    rw [keyMomentRowsAt2173]
    exact keyMoment2173 B hB
  · have he : k = (2174 : Fin 2886) := Fin.ext h2174
    subst k
    rw [keyMomentRowsAt2174]
    exact keyMoment2174 B hB
  · have he : k = (2175 : Fin 2886) := Fin.ext h2175
    subst k
    rw [keyMomentRowsAt2175]
    exact keyMoment2175 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI

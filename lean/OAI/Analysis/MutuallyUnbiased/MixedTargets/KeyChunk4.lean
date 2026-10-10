import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound4
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt128 : keyMomentRows (128 : Fin 2886) =
    keyMomentRow128 := by decide +kernel

theorem keyMomentRowsAt129 : keyMomentRows (129 : Fin 2886) =
    keyMomentRow129 := by decide +kernel

theorem keyMomentRowsAt130 : keyMomentRows (130 : Fin 2886) =
    keyMomentRow130 := by decide +kernel

theorem keyMomentRowsAt131 : keyMomentRows (131 : Fin 2886) =
    keyMomentRow131 := by decide +kernel

theorem keyMomentRowsAt132 : keyMomentRows (132 : Fin 2886) =
    keyMomentRow132 := by decide +kernel

theorem keyMomentRowsAt133 : keyMomentRows (133 : Fin 2886) =
    keyMomentRow133 := by decide +kernel

theorem keyMomentRowsAt134 : keyMomentRows (134 : Fin 2886) =
    keyMomentRow134 := by decide +kernel

theorem keyMomentRowsAt135 : keyMomentRows (135 : Fin 2886) =
    keyMomentRow135 := by decide +kernel

theorem keyMomentRowsAt136 : keyMomentRows (136 : Fin 2886) =
    keyMomentRow136 := by decide +kernel

theorem keyMomentRowsAt137 : keyMomentRows (137 : Fin 2886) =
    keyMomentRow137 := by decide +kernel

theorem keyMomentRowsAt138 : keyMomentRows (138 : Fin 2886) =
    keyMomentRow138 := by decide +kernel

theorem keyMomentRowsAt139 : keyMomentRows (139 : Fin 2886) =
    keyMomentRow139 := by decide +kernel

theorem keyMomentRowsAt140 : keyMomentRows (140 : Fin 2886) =
    keyMomentRow140 := by decide +kernel

theorem keyMomentRowsAt141 : keyMomentRows (141 : Fin 2886) =
    keyMomentRow141 := by decide +kernel

theorem keyMomentRowsAt142 : keyMomentRows (142 : Fin 2886) =
    keyMomentRow142 := by decide +kernel

theorem keyMomentRowsAt143 : keyMomentRows (143 : Fin 2886) =
    keyMomentRow143 := by decide +kernel

theorem keyMomentRowsAt144 : keyMomentRows (144 : Fin 2886) =
    keyMomentRow144 := by decide +kernel

theorem keyMomentRowsAt145 : keyMomentRows (145 : Fin 2886) =
    keyMomentRow145 := by decide +kernel

theorem keyMomentRowsAt146 : keyMomentRows (146 : Fin 2886) =
    keyMomentRow146 := by decide +kernel

theorem keyMomentRowsAt147 : keyMomentRows (147 : Fin 2886) =
    keyMomentRow147 := by decide +kernel

theorem keyMomentRowsAt148 : keyMomentRows (148 : Fin 2886) =
    keyMomentRow148 := by decide +kernel

theorem keyMomentRowsAt149 : keyMomentRows (149 : Fin 2886) =
    keyMomentRow149 := by decide +kernel

theorem keyMomentRowsAt150 : keyMomentRows (150 : Fin 2886) =
    keyMomentRow150 := by decide +kernel

theorem keyMomentRowsAt151 : keyMomentRows (151 : Fin 2886) =
    keyMomentRow151 := by decide +kernel

theorem keyMomentRowsAt152 : keyMomentRows (152 : Fin 2886) =
    keyMomentRow152 := by decide +kernel

theorem keyMomentRowsAt153 : keyMomentRows (153 : Fin 2886) =
    keyMomentRow153 := by decide +kernel

theorem keyMomentRowsAt154 : keyMomentRows (154 : Fin 2886) =
    keyMomentRow154 := by decide +kernel

theorem keyMomentRowsAt155 : keyMomentRows (155 : Fin 2886) =
    keyMomentRow155 := by decide +kernel

theorem keyMomentRowsAt156 : keyMomentRows (156 : Fin 2886) =
    keyMomentRow156 := by decide +kernel

theorem keyMomentRowsAt157 : keyMomentRows (157 : Fin 2886) =
    keyMomentRow157 := by decide +kernel

theorem keyMomentRowsAt158 : keyMomentRows (158 : Fin 2886) =
    keyMomentRow158 := by decide +kernel

theorem keyMomentRowsAt159 : keyMomentRows (159 : Fin 2886) =
    keyMomentRow159 := by decide +kernel

theorem keyMomentChunkSound4 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 4) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 128 ∨ k.val = 129 ∨ k.val = 130 ∨ k.val = 131 ∨ k.val = 132 ∨ k.val = 133 ∨ k.val = 134 ∨ k.val = 135 ∨ k.val = 136 ∨ k.val = 137 ∨ k.val = 138 ∨ k.val = 139 ∨ k.val = 140 ∨ k.val = 141 ∨ k.val = 142 ∨ k.val = 143 ∨ k.val = 144 ∨ k.val = 145 ∨ k.val = 146 ∨ k.val = 147 ∨ k.val = 148 ∨ k.val = 149 ∨ k.val = 150 ∨ k.val = 151 ∨ k.val = 152 ∨ k.val = 153 ∨ k.val = 154 ∨ k.val = 155 ∨ k.val = 156 ∨ k.val = 157 ∨ k.val = 158 ∨ k.val = 159 := by omega
  rcases heq with h128 | h129 | h130 | h131 | h132 | h133 | h134 | h135 | h136 | h137 | h138 | h139 | h140 | h141 | h142 | h143 | h144 | h145 | h146 | h147 | h148 | h149 | h150 | h151 | h152 | h153 | h154 | h155 | h156 | h157 | h158 | h159
  · have he : k = (128 : Fin 2886) := Fin.ext h128
    subst k
    rw [keyMomentRowsAt128]
    exact keyMoment128 B hB
  · have he : k = (129 : Fin 2886) := Fin.ext h129
    subst k
    rw [keyMomentRowsAt129]
    exact keyMoment129 B hB
  · have he : k = (130 : Fin 2886) := Fin.ext h130
    subst k
    rw [keyMomentRowsAt130]
    exact keyMoment130 B hB
  · have he : k = (131 : Fin 2886) := Fin.ext h131
    subst k
    rw [keyMomentRowsAt131]
    exact keyMoment131 B hB
  · have he : k = (132 : Fin 2886) := Fin.ext h132
    subst k
    rw [keyMomentRowsAt132]
    exact keyMoment132 B hB
  · have he : k = (133 : Fin 2886) := Fin.ext h133
    subst k
    rw [keyMomentRowsAt133]
    exact keyMoment133 B hB
  · have he : k = (134 : Fin 2886) := Fin.ext h134
    subst k
    rw [keyMomentRowsAt134]
    exact keyMoment134 B hB
  · have he : k = (135 : Fin 2886) := Fin.ext h135
    subst k
    rw [keyMomentRowsAt135]
    exact keyMoment135 B hB
  · have he : k = (136 : Fin 2886) := Fin.ext h136
    subst k
    rw [keyMomentRowsAt136]
    exact keyMoment136 B hB
  · have he : k = (137 : Fin 2886) := Fin.ext h137
    subst k
    rw [keyMomentRowsAt137]
    exact keyMoment137 B hB
  · have he : k = (138 : Fin 2886) := Fin.ext h138
    subst k
    rw [keyMomentRowsAt138]
    exact keyMoment138 B hB
  · have he : k = (139 : Fin 2886) := Fin.ext h139
    subst k
    rw [keyMomentRowsAt139]
    exact keyMoment139 B hB
  · have he : k = (140 : Fin 2886) := Fin.ext h140
    subst k
    rw [keyMomentRowsAt140]
    exact keyMoment140 B hB
  · have he : k = (141 : Fin 2886) := Fin.ext h141
    subst k
    rw [keyMomentRowsAt141]
    exact keyMoment141 B hB
  · have he : k = (142 : Fin 2886) := Fin.ext h142
    subst k
    rw [keyMomentRowsAt142]
    exact keyMoment142 B hB
  · have he : k = (143 : Fin 2886) := Fin.ext h143
    subst k
    rw [keyMomentRowsAt143]
    exact keyMoment143 B hB
  · have he : k = (144 : Fin 2886) := Fin.ext h144
    subst k
    rw [keyMomentRowsAt144]
    exact keyMoment144 B hB
  · have he : k = (145 : Fin 2886) := Fin.ext h145
    subst k
    rw [keyMomentRowsAt145]
    exact keyMoment145 B hB
  · have he : k = (146 : Fin 2886) := Fin.ext h146
    subst k
    rw [keyMomentRowsAt146]
    exact keyMoment146 B hB
  · have he : k = (147 : Fin 2886) := Fin.ext h147
    subst k
    rw [keyMomentRowsAt147]
    exact keyMoment147 B hB
  · have he : k = (148 : Fin 2886) := Fin.ext h148
    subst k
    rw [keyMomentRowsAt148]
    exact keyMoment148 B hB
  · have he : k = (149 : Fin 2886) := Fin.ext h149
    subst k
    rw [keyMomentRowsAt149]
    exact keyMoment149 B hB
  · have he : k = (150 : Fin 2886) := Fin.ext h150
    subst k
    rw [keyMomentRowsAt150]
    exact keyMoment150 B hB
  · have he : k = (151 : Fin 2886) := Fin.ext h151
    subst k
    rw [keyMomentRowsAt151]
    exact keyMoment151 B hB
  · have he : k = (152 : Fin 2886) := Fin.ext h152
    subst k
    rw [keyMomentRowsAt152]
    exact keyMoment152 B hB
  · have he : k = (153 : Fin 2886) := Fin.ext h153
    subst k
    rw [keyMomentRowsAt153]
    exact keyMoment153 B hB
  · have he : k = (154 : Fin 2886) := Fin.ext h154
    subst k
    rw [keyMomentRowsAt154]
    exact keyMoment154 B hB
  · have he : k = (155 : Fin 2886) := Fin.ext h155
    subst k
    rw [keyMomentRowsAt155]
    exact keyMoment155 B hB
  · have he : k = (156 : Fin 2886) := Fin.ext h156
    subst k
    rw [keyMomentRowsAt156]
    exact keyMoment156 B hB
  · have he : k = (157 : Fin 2886) := Fin.ext h157
    subst k
    rw [keyMomentRowsAt157]
    exact keyMoment157 B hB
  · have he : k = (158 : Fin 2886) := Fin.ext h158
    subst k
    rw [keyMomentRowsAt158]
    exact keyMoment158 B hB
  · have he : k = (159 : Fin 2886) := Fin.ext h159
    subst k
    rw [keyMomentRowsAt159]
    exact keyMoment159 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI

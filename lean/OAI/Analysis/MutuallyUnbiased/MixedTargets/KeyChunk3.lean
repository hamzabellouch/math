import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound3
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt96 : keyMomentRows (96 : Fin 2886) =
    keyMomentRow96 := by decide +kernel

theorem keyMomentRowsAt97 : keyMomentRows (97 : Fin 2886) =
    keyMomentRow97 := by decide +kernel

theorem keyMomentRowsAt98 : keyMomentRows (98 : Fin 2886) =
    keyMomentRow98 := by decide +kernel

theorem keyMomentRowsAt99 : keyMomentRows (99 : Fin 2886) =
    keyMomentRow99 := by decide +kernel

theorem keyMomentRowsAt100 : keyMomentRows (100 : Fin 2886) =
    keyMomentRow100 := by decide +kernel

theorem keyMomentRowsAt101 : keyMomentRows (101 : Fin 2886) =
    keyMomentRow101 := by decide +kernel

theorem keyMomentRowsAt102 : keyMomentRows (102 : Fin 2886) =
    keyMomentRow102 := by decide +kernel

theorem keyMomentRowsAt103 : keyMomentRows (103 : Fin 2886) =
    keyMomentRow103 := by decide +kernel

theorem keyMomentRowsAt104 : keyMomentRows (104 : Fin 2886) =
    keyMomentRow104 := by decide +kernel

theorem keyMomentRowsAt105 : keyMomentRows (105 : Fin 2886) =
    keyMomentRow105 := by decide +kernel

theorem keyMomentRowsAt106 : keyMomentRows (106 : Fin 2886) =
    keyMomentRow106 := by decide +kernel

theorem keyMomentRowsAt107 : keyMomentRows (107 : Fin 2886) =
    keyMomentRow107 := by decide +kernel

theorem keyMomentRowsAt108 : keyMomentRows (108 : Fin 2886) =
    keyMomentRow108 := by decide +kernel

theorem keyMomentRowsAt109 : keyMomentRows (109 : Fin 2886) =
    keyMomentRow109 := by decide +kernel

theorem keyMomentRowsAt110 : keyMomentRows (110 : Fin 2886) =
    keyMomentRow110 := by decide +kernel

theorem keyMomentRowsAt111 : keyMomentRows (111 : Fin 2886) =
    keyMomentRow111 := by decide +kernel

theorem keyMomentRowsAt112 : keyMomentRows (112 : Fin 2886) =
    keyMomentRow112 := by decide +kernel

theorem keyMomentRowsAt113 : keyMomentRows (113 : Fin 2886) =
    keyMomentRow113 := by decide +kernel

theorem keyMomentRowsAt114 : keyMomentRows (114 : Fin 2886) =
    keyMomentRow114 := by decide +kernel

theorem keyMomentRowsAt115 : keyMomentRows (115 : Fin 2886) =
    keyMomentRow115 := by decide +kernel

theorem keyMomentRowsAt116 : keyMomentRows (116 : Fin 2886) =
    keyMomentRow116 := by decide +kernel

theorem keyMomentRowsAt117 : keyMomentRows (117 : Fin 2886) =
    keyMomentRow117 := by decide +kernel

theorem keyMomentRowsAt118 : keyMomentRows (118 : Fin 2886) =
    keyMomentRow118 := by decide +kernel

theorem keyMomentRowsAt119 : keyMomentRows (119 : Fin 2886) =
    keyMomentRow119 := by decide +kernel

theorem keyMomentRowsAt120 : keyMomentRows (120 : Fin 2886) =
    keyMomentRow120 := by decide +kernel

theorem keyMomentRowsAt121 : keyMomentRows (121 : Fin 2886) =
    keyMomentRow121 := by decide +kernel

theorem keyMomentRowsAt122 : keyMomentRows (122 : Fin 2886) =
    keyMomentRow122 := by decide +kernel

theorem keyMomentRowsAt123 : keyMomentRows (123 : Fin 2886) =
    keyMomentRow123 := by decide +kernel

theorem keyMomentRowsAt124 : keyMomentRows (124 : Fin 2886) =
    keyMomentRow124 := by decide +kernel

theorem keyMomentRowsAt125 : keyMomentRows (125 : Fin 2886) =
    keyMomentRow125 := by decide +kernel

theorem keyMomentRowsAt126 : keyMomentRows (126 : Fin 2886) =
    keyMomentRow126 := by decide +kernel

theorem keyMomentRowsAt127 : keyMomentRows (127 : Fin 2886) =
    keyMomentRow127 := by decide +kernel

theorem keyMomentChunkSound3 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 3) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 96 ∨ k.val = 97 ∨ k.val = 98 ∨ k.val = 99 ∨ k.val = 100 ∨ k.val = 101 ∨ k.val = 102 ∨ k.val = 103 ∨ k.val = 104 ∨ k.val = 105 ∨ k.val = 106 ∨ k.val = 107 ∨ k.val = 108 ∨ k.val = 109 ∨ k.val = 110 ∨ k.val = 111 ∨ k.val = 112 ∨ k.val = 113 ∨ k.val = 114 ∨ k.val = 115 ∨ k.val = 116 ∨ k.val = 117 ∨ k.val = 118 ∨ k.val = 119 ∨ k.val = 120 ∨ k.val = 121 ∨ k.val = 122 ∨ k.val = 123 ∨ k.val = 124 ∨ k.val = 125 ∨ k.val = 126 ∨ k.val = 127 := by omega
  rcases heq with h96 | h97 | h98 | h99 | h100 | h101 | h102 | h103 | h104 | h105 | h106 | h107 | h108 | h109 | h110 | h111 | h112 | h113 | h114 | h115 | h116 | h117 | h118 | h119 | h120 | h121 | h122 | h123 | h124 | h125 | h126 | h127
  · have he : k = (96 : Fin 2886) := Fin.ext h96
    subst k
    rw [keyMomentRowsAt96]
    exact keyMoment96 B hB
  · have he : k = (97 : Fin 2886) := Fin.ext h97
    subst k
    rw [keyMomentRowsAt97]
    exact keyMoment97 B hB
  · have he : k = (98 : Fin 2886) := Fin.ext h98
    subst k
    rw [keyMomentRowsAt98]
    exact keyMoment98 B hB
  · have he : k = (99 : Fin 2886) := Fin.ext h99
    subst k
    rw [keyMomentRowsAt99]
    exact keyMoment99 B hB
  · have he : k = (100 : Fin 2886) := Fin.ext h100
    subst k
    rw [keyMomentRowsAt100]
    exact keyMoment100 B hB
  · have he : k = (101 : Fin 2886) := Fin.ext h101
    subst k
    rw [keyMomentRowsAt101]
    exact keyMoment101 B hB
  · have he : k = (102 : Fin 2886) := Fin.ext h102
    subst k
    rw [keyMomentRowsAt102]
    exact keyMoment102 B hB
  · have he : k = (103 : Fin 2886) := Fin.ext h103
    subst k
    rw [keyMomentRowsAt103]
    exact keyMoment103 B hB
  · have he : k = (104 : Fin 2886) := Fin.ext h104
    subst k
    rw [keyMomentRowsAt104]
    exact keyMoment104 B hB
  · have he : k = (105 : Fin 2886) := Fin.ext h105
    subst k
    rw [keyMomentRowsAt105]
    exact keyMoment105 B hB
  · have he : k = (106 : Fin 2886) := Fin.ext h106
    subst k
    rw [keyMomentRowsAt106]
    exact keyMoment106 B hB
  · have he : k = (107 : Fin 2886) := Fin.ext h107
    subst k
    rw [keyMomentRowsAt107]
    exact keyMoment107 B hB
  · have he : k = (108 : Fin 2886) := Fin.ext h108
    subst k
    rw [keyMomentRowsAt108]
    exact keyMoment108 B hB
  · have he : k = (109 : Fin 2886) := Fin.ext h109
    subst k
    rw [keyMomentRowsAt109]
    exact keyMoment109 B hB
  · have he : k = (110 : Fin 2886) := Fin.ext h110
    subst k
    rw [keyMomentRowsAt110]
    exact keyMoment110 B hB
  · have he : k = (111 : Fin 2886) := Fin.ext h111
    subst k
    rw [keyMomentRowsAt111]
    exact keyMoment111 B hB
  · have he : k = (112 : Fin 2886) := Fin.ext h112
    subst k
    rw [keyMomentRowsAt112]
    exact keyMoment112 B hB
  · have he : k = (113 : Fin 2886) := Fin.ext h113
    subst k
    rw [keyMomentRowsAt113]
    exact keyMoment113 B hB
  · have he : k = (114 : Fin 2886) := Fin.ext h114
    subst k
    rw [keyMomentRowsAt114]
    exact keyMoment114 B hB
  · have he : k = (115 : Fin 2886) := Fin.ext h115
    subst k
    rw [keyMomentRowsAt115]
    exact keyMoment115 B hB
  · have he : k = (116 : Fin 2886) := Fin.ext h116
    subst k
    rw [keyMomentRowsAt116]
    exact keyMoment116 B hB
  · have he : k = (117 : Fin 2886) := Fin.ext h117
    subst k
    rw [keyMomentRowsAt117]
    exact keyMoment117 B hB
  · have he : k = (118 : Fin 2886) := Fin.ext h118
    subst k
    rw [keyMomentRowsAt118]
    exact keyMoment118 B hB
  · have he : k = (119 : Fin 2886) := Fin.ext h119
    subst k
    rw [keyMomentRowsAt119]
    exact keyMoment119 B hB
  · have he : k = (120 : Fin 2886) := Fin.ext h120
    subst k
    rw [keyMomentRowsAt120]
    exact keyMoment120 B hB
  · have he : k = (121 : Fin 2886) := Fin.ext h121
    subst k
    rw [keyMomentRowsAt121]
    exact keyMoment121 B hB
  · have he : k = (122 : Fin 2886) := Fin.ext h122
    subst k
    rw [keyMomentRowsAt122]
    exact keyMoment122 B hB
  · have he : k = (123 : Fin 2886) := Fin.ext h123
    subst k
    rw [keyMomentRowsAt123]
    exact keyMoment123 B hB
  · have he : k = (124 : Fin 2886) := Fin.ext h124
    subst k
    rw [keyMomentRowsAt124]
    exact keyMoment124 B hB
  · have he : k = (125 : Fin 2886) := Fin.ext h125
    subst k
    rw [keyMomentRowsAt125]
    exact keyMoment125 B hB
  · have he : k = (126 : Fin 2886) := Fin.ext h126
    subst k
    rw [keyMomentRowsAt126]
    exact keyMoment126 B hB
  · have he : k = (127 : Fin 2886) := Fin.ext h127
    subst k
    rw [keyMomentRowsAt127]
    exact keyMoment127 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI

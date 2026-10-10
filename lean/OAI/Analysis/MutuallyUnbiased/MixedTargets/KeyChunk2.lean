import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound2
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt64 : keyMomentRows (64 : Fin 2886) =
    keyMomentRow64 := by decide +kernel

theorem keyMomentRowsAt65 : keyMomentRows (65 : Fin 2886) =
    keyMomentRow65 := by decide +kernel

theorem keyMomentRowsAt66 : keyMomentRows (66 : Fin 2886) =
    keyMomentRow66 := by decide +kernel

theorem keyMomentRowsAt67 : keyMomentRows (67 : Fin 2886) =
    keyMomentRow67 := by decide +kernel

theorem keyMomentRowsAt68 : keyMomentRows (68 : Fin 2886) =
    keyMomentRow68 := by decide +kernel

theorem keyMomentRowsAt69 : keyMomentRows (69 : Fin 2886) =
    keyMomentRow69 := by decide +kernel

theorem keyMomentRowsAt70 : keyMomentRows (70 : Fin 2886) =
    keyMomentRow70 := by decide +kernel

theorem keyMomentRowsAt71 : keyMomentRows (71 : Fin 2886) =
    keyMomentRow71 := by decide +kernel

theorem keyMomentRowsAt72 : keyMomentRows (72 : Fin 2886) =
    keyMomentRow72 := by decide +kernel

theorem keyMomentRowsAt73 : keyMomentRows (73 : Fin 2886) =
    keyMomentRow73 := by decide +kernel

theorem keyMomentRowsAt74 : keyMomentRows (74 : Fin 2886) =
    keyMomentRow74 := by decide +kernel

theorem keyMomentRowsAt75 : keyMomentRows (75 : Fin 2886) =
    keyMomentRow75 := by decide +kernel

theorem keyMomentRowsAt76 : keyMomentRows (76 : Fin 2886) =
    keyMomentRow76 := by decide +kernel

theorem keyMomentRowsAt77 : keyMomentRows (77 : Fin 2886) =
    keyMomentRow77 := by decide +kernel

theorem keyMomentRowsAt78 : keyMomentRows (78 : Fin 2886) =
    keyMomentRow78 := by decide +kernel

theorem keyMomentRowsAt79 : keyMomentRows (79 : Fin 2886) =
    keyMomentRow79 := by decide +kernel

theorem keyMomentRowsAt80 : keyMomentRows (80 : Fin 2886) =
    keyMomentRow80 := by decide +kernel

theorem keyMomentRowsAt81 : keyMomentRows (81 : Fin 2886) =
    keyMomentRow81 := by decide +kernel

theorem keyMomentRowsAt82 : keyMomentRows (82 : Fin 2886) =
    keyMomentRow82 := by decide +kernel

theorem keyMomentRowsAt83 : keyMomentRows (83 : Fin 2886) =
    keyMomentRow83 := by decide +kernel

theorem keyMomentRowsAt84 : keyMomentRows (84 : Fin 2886) =
    keyMomentRow84 := by decide +kernel

theorem keyMomentRowsAt85 : keyMomentRows (85 : Fin 2886) =
    keyMomentRow85 := by decide +kernel

theorem keyMomentRowsAt86 : keyMomentRows (86 : Fin 2886) =
    keyMomentRow86 := by decide +kernel

theorem keyMomentRowsAt87 : keyMomentRows (87 : Fin 2886) =
    keyMomentRow87 := by decide +kernel

theorem keyMomentRowsAt88 : keyMomentRows (88 : Fin 2886) =
    keyMomentRow88 := by decide +kernel

theorem keyMomentRowsAt89 : keyMomentRows (89 : Fin 2886) =
    keyMomentRow89 := by decide +kernel

theorem keyMomentRowsAt90 : keyMomentRows (90 : Fin 2886) =
    keyMomentRow90 := by decide +kernel

theorem keyMomentRowsAt91 : keyMomentRows (91 : Fin 2886) =
    keyMomentRow91 := by decide +kernel

theorem keyMomentRowsAt92 : keyMomentRows (92 : Fin 2886) =
    keyMomentRow92 := by decide +kernel

theorem keyMomentRowsAt93 : keyMomentRows (93 : Fin 2886) =
    keyMomentRow93 := by decide +kernel

theorem keyMomentRowsAt94 : keyMomentRows (94 : Fin 2886) =
    keyMomentRow94 := by decide +kernel

theorem keyMomentRowsAt95 : keyMomentRows (95 : Fin 2886) =
    keyMomentRow95 := by decide +kernel

theorem keyMomentChunkSound2 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 2) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 64 ∨ k.val = 65 ∨ k.val = 66 ∨ k.val = 67 ∨ k.val = 68 ∨ k.val = 69 ∨ k.val = 70 ∨ k.val = 71 ∨ k.val = 72 ∨ k.val = 73 ∨ k.val = 74 ∨ k.val = 75 ∨ k.val = 76 ∨ k.val = 77 ∨ k.val = 78 ∨ k.val = 79 ∨ k.val = 80 ∨ k.val = 81 ∨ k.val = 82 ∨ k.val = 83 ∨ k.val = 84 ∨ k.val = 85 ∨ k.val = 86 ∨ k.val = 87 ∨ k.val = 88 ∨ k.val = 89 ∨ k.val = 90 ∨ k.val = 91 ∨ k.val = 92 ∨ k.val = 93 ∨ k.val = 94 ∨ k.val = 95 := by omega
  rcases heq with h64 | h65 | h66 | h67 | h68 | h69 | h70 | h71 | h72 | h73 | h74 | h75 | h76 | h77 | h78 | h79 | h80 | h81 | h82 | h83 | h84 | h85 | h86 | h87 | h88 | h89 | h90 | h91 | h92 | h93 | h94 | h95
  · have he : k = (64 : Fin 2886) := Fin.ext h64
    subst k
    rw [keyMomentRowsAt64]
    exact keyMoment64 B hB
  · have he : k = (65 : Fin 2886) := Fin.ext h65
    subst k
    rw [keyMomentRowsAt65]
    exact keyMoment65 B hB
  · have he : k = (66 : Fin 2886) := Fin.ext h66
    subst k
    rw [keyMomentRowsAt66]
    exact keyMoment66 B hB
  · have he : k = (67 : Fin 2886) := Fin.ext h67
    subst k
    rw [keyMomentRowsAt67]
    exact keyMoment67 B hB
  · have he : k = (68 : Fin 2886) := Fin.ext h68
    subst k
    rw [keyMomentRowsAt68]
    exact keyMoment68 B hB
  · have he : k = (69 : Fin 2886) := Fin.ext h69
    subst k
    rw [keyMomentRowsAt69]
    exact keyMoment69 B hB
  · have he : k = (70 : Fin 2886) := Fin.ext h70
    subst k
    rw [keyMomentRowsAt70]
    exact keyMoment70 B hB
  · have he : k = (71 : Fin 2886) := Fin.ext h71
    subst k
    rw [keyMomentRowsAt71]
    exact keyMoment71 B hB
  · have he : k = (72 : Fin 2886) := Fin.ext h72
    subst k
    rw [keyMomentRowsAt72]
    exact keyMoment72 B hB
  · have he : k = (73 : Fin 2886) := Fin.ext h73
    subst k
    rw [keyMomentRowsAt73]
    exact keyMoment73 B hB
  · have he : k = (74 : Fin 2886) := Fin.ext h74
    subst k
    rw [keyMomentRowsAt74]
    exact keyMoment74 B hB
  · have he : k = (75 : Fin 2886) := Fin.ext h75
    subst k
    rw [keyMomentRowsAt75]
    exact keyMoment75 B hB
  · have he : k = (76 : Fin 2886) := Fin.ext h76
    subst k
    rw [keyMomentRowsAt76]
    exact keyMoment76 B hB
  · have he : k = (77 : Fin 2886) := Fin.ext h77
    subst k
    rw [keyMomentRowsAt77]
    exact keyMoment77 B hB
  · have he : k = (78 : Fin 2886) := Fin.ext h78
    subst k
    rw [keyMomentRowsAt78]
    exact keyMoment78 B hB
  · have he : k = (79 : Fin 2886) := Fin.ext h79
    subst k
    rw [keyMomentRowsAt79]
    exact keyMoment79 B hB
  · have he : k = (80 : Fin 2886) := Fin.ext h80
    subst k
    rw [keyMomentRowsAt80]
    exact keyMoment80 B hB
  · have he : k = (81 : Fin 2886) := Fin.ext h81
    subst k
    rw [keyMomentRowsAt81]
    exact keyMoment81 B hB
  · have he : k = (82 : Fin 2886) := Fin.ext h82
    subst k
    rw [keyMomentRowsAt82]
    exact keyMoment82 B hB
  · have he : k = (83 : Fin 2886) := Fin.ext h83
    subst k
    rw [keyMomentRowsAt83]
    exact keyMoment83 B hB
  · have he : k = (84 : Fin 2886) := Fin.ext h84
    subst k
    rw [keyMomentRowsAt84]
    exact keyMoment84 B hB
  · have he : k = (85 : Fin 2886) := Fin.ext h85
    subst k
    rw [keyMomentRowsAt85]
    exact keyMoment85 B hB
  · have he : k = (86 : Fin 2886) := Fin.ext h86
    subst k
    rw [keyMomentRowsAt86]
    exact keyMoment86 B hB
  · have he : k = (87 : Fin 2886) := Fin.ext h87
    subst k
    rw [keyMomentRowsAt87]
    exact keyMoment87 B hB
  · have he : k = (88 : Fin 2886) := Fin.ext h88
    subst k
    rw [keyMomentRowsAt88]
    exact keyMoment88 B hB
  · have he : k = (89 : Fin 2886) := Fin.ext h89
    subst k
    rw [keyMomentRowsAt89]
    exact keyMoment89 B hB
  · have he : k = (90 : Fin 2886) := Fin.ext h90
    subst k
    rw [keyMomentRowsAt90]
    exact keyMoment90 B hB
  · have he : k = (91 : Fin 2886) := Fin.ext h91
    subst k
    rw [keyMomentRowsAt91]
    exact keyMoment91 B hB
  · have he : k = (92 : Fin 2886) := Fin.ext h92
    subst k
    rw [keyMomentRowsAt92]
    exact keyMoment92 B hB
  · have he : k = (93 : Fin 2886) := Fin.ext h93
    subst k
    rw [keyMomentRowsAt93]
    exact keyMoment93 B hB
  · have he : k = (94 : Fin 2886) := Fin.ext h94
    subst k
    rw [keyMomentRowsAt94]
    exact keyMoment94 B hB
  · have he : k = (95 : Fin 2886) := Fin.ext h95
    subst k
    rw [keyMomentRowsAt95]
    exact keyMoment95 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI

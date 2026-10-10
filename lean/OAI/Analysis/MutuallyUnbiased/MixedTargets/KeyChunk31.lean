import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound31
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt992 : keyMomentRows (992 : Fin 2886) =
    keyMomentRow992 := by decide +kernel

theorem keyMomentRowsAt993 : keyMomentRows (993 : Fin 2886) =
    keyMomentRow993 := by decide +kernel

theorem keyMomentRowsAt994 : keyMomentRows (994 : Fin 2886) =
    keyMomentRow994 := by decide +kernel

theorem keyMomentRowsAt995 : keyMomentRows (995 : Fin 2886) =
    keyMomentRow995 := by decide +kernel

theorem keyMomentRowsAt996 : keyMomentRows (996 : Fin 2886) =
    keyMomentRow996 := by decide +kernel

theorem keyMomentRowsAt997 : keyMomentRows (997 : Fin 2886) =
    keyMomentRow997 := by decide +kernel

theorem keyMomentRowsAt998 : keyMomentRows (998 : Fin 2886) =
    keyMomentRow998 := by decide +kernel

theorem keyMomentRowsAt999 : keyMomentRows (999 : Fin 2886) =
    keyMomentRow999 := by decide +kernel

theorem keyMomentRowsAt1000 : keyMomentRows (1000 : Fin 2886) =
    keyMomentRow1000 := by decide +kernel

theorem keyMomentRowsAt1001 : keyMomentRows (1001 : Fin 2886) =
    keyMomentRow1001 := by decide +kernel

theorem keyMomentRowsAt1002 : keyMomentRows (1002 : Fin 2886) =
    keyMomentRow1002 := by decide +kernel

theorem keyMomentRowsAt1003 : keyMomentRows (1003 : Fin 2886) =
    keyMomentRow1003 := by decide +kernel

theorem keyMomentRowsAt1004 : keyMomentRows (1004 : Fin 2886) =
    keyMomentRow1004 := by decide +kernel

theorem keyMomentRowsAt1005 : keyMomentRows (1005 : Fin 2886) =
    keyMomentRow1005 := by decide +kernel

theorem keyMomentRowsAt1006 : keyMomentRows (1006 : Fin 2886) =
    keyMomentRow1006 := by decide +kernel

theorem keyMomentRowsAt1007 : keyMomentRows (1007 : Fin 2886) =
    keyMomentRow1007 := by decide +kernel

theorem keyMomentRowsAt1008 : keyMomentRows (1008 : Fin 2886) =
    keyMomentRow1008 := by decide +kernel

theorem keyMomentRowsAt1009 : keyMomentRows (1009 : Fin 2886) =
    keyMomentRow1009 := by decide +kernel

theorem keyMomentRowsAt1010 : keyMomentRows (1010 : Fin 2886) =
    keyMomentRow1010 := by decide +kernel

theorem keyMomentRowsAt1011 : keyMomentRows (1011 : Fin 2886) =
    keyMomentRow1011 := by decide +kernel

theorem keyMomentRowsAt1012 : keyMomentRows (1012 : Fin 2886) =
    keyMomentRow1012 := by decide +kernel

theorem keyMomentRowsAt1013 : keyMomentRows (1013 : Fin 2886) =
    keyMomentRow1013 := by decide +kernel

theorem keyMomentRowsAt1014 : keyMomentRows (1014 : Fin 2886) =
    keyMomentRow1014 := by decide +kernel

theorem keyMomentRowsAt1015 : keyMomentRows (1015 : Fin 2886) =
    keyMomentRow1015 := by decide +kernel

theorem keyMomentRowsAt1016 : keyMomentRows (1016 : Fin 2886) =
    keyMomentRow1016 := by decide +kernel

theorem keyMomentRowsAt1017 : keyMomentRows (1017 : Fin 2886) =
    keyMomentRow1017 := by decide +kernel

theorem keyMomentRowsAt1018 : keyMomentRows (1018 : Fin 2886) =
    keyMomentRow1018 := by decide +kernel

theorem keyMomentRowsAt1019 : keyMomentRows (1019 : Fin 2886) =
    keyMomentRow1019 := by decide +kernel

theorem keyMomentRowsAt1020 : keyMomentRows (1020 : Fin 2886) =
    keyMomentRow1020 := by decide +kernel

theorem keyMomentRowsAt1021 : keyMomentRows (1021 : Fin 2886) =
    keyMomentRow1021 := by decide +kernel

theorem keyMomentRowsAt1022 : keyMomentRows (1022 : Fin 2886) =
    keyMomentRow1022 := by decide +kernel

theorem keyMomentRowsAt1023 : keyMomentRows (1023 : Fin 2886) =
    keyMomentRow1023 := by decide +kernel

theorem keyMomentChunkSound31 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 31) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 992 ∨ k.val = 993 ∨ k.val = 994 ∨ k.val = 995 ∨ k.val = 996 ∨ k.val = 997 ∨ k.val = 998 ∨ k.val = 999 ∨ k.val = 1000 ∨ k.val = 1001 ∨ k.val = 1002 ∨ k.val = 1003 ∨ k.val = 1004 ∨ k.val = 1005 ∨ k.val = 1006 ∨ k.val = 1007 ∨ k.val = 1008 ∨ k.val = 1009 ∨ k.val = 1010 ∨ k.val = 1011 ∨ k.val = 1012 ∨ k.val = 1013 ∨ k.val = 1014 ∨ k.val = 1015 ∨ k.val = 1016 ∨ k.val = 1017 ∨ k.val = 1018 ∨ k.val = 1019 ∨ k.val = 1020 ∨ k.val = 1021 ∨ k.val = 1022 ∨ k.val = 1023 := by omega
  rcases heq with h992 | h993 | h994 | h995 | h996 | h997 | h998 | h999 | h1000 | h1001 | h1002 | h1003 | h1004 | h1005 | h1006 | h1007 | h1008 | h1009 | h1010 | h1011 | h1012 | h1013 | h1014 | h1015 | h1016 | h1017 | h1018 | h1019 | h1020 | h1021 | h1022 | h1023
  · have he : k = (992 : Fin 2886) := Fin.ext h992
    subst k
    rw [keyMomentRowsAt992]
    exact keyMoment992 B hB
  · have he : k = (993 : Fin 2886) := Fin.ext h993
    subst k
    rw [keyMomentRowsAt993]
    exact keyMoment993 B hB
  · have he : k = (994 : Fin 2886) := Fin.ext h994
    subst k
    rw [keyMomentRowsAt994]
    exact keyMoment994 B hB
  · have he : k = (995 : Fin 2886) := Fin.ext h995
    subst k
    rw [keyMomentRowsAt995]
    exact keyMoment995 B hB
  · have he : k = (996 : Fin 2886) := Fin.ext h996
    subst k
    rw [keyMomentRowsAt996]
    exact keyMoment996 B hB
  · have he : k = (997 : Fin 2886) := Fin.ext h997
    subst k
    rw [keyMomentRowsAt997]
    exact keyMoment997 B hB
  · have he : k = (998 : Fin 2886) := Fin.ext h998
    subst k
    rw [keyMomentRowsAt998]
    exact keyMoment998 B hB
  · have he : k = (999 : Fin 2886) := Fin.ext h999
    subst k
    rw [keyMomentRowsAt999]
    exact keyMoment999 B hB
  · have he : k = (1000 : Fin 2886) := Fin.ext h1000
    subst k
    rw [keyMomentRowsAt1000]
    exact keyMoment1000 B hB
  · have he : k = (1001 : Fin 2886) := Fin.ext h1001
    subst k
    rw [keyMomentRowsAt1001]
    exact keyMoment1001 B hB
  · have he : k = (1002 : Fin 2886) := Fin.ext h1002
    subst k
    rw [keyMomentRowsAt1002]
    exact keyMoment1002 B hB
  · have he : k = (1003 : Fin 2886) := Fin.ext h1003
    subst k
    rw [keyMomentRowsAt1003]
    exact keyMoment1003 B hB
  · have he : k = (1004 : Fin 2886) := Fin.ext h1004
    subst k
    rw [keyMomentRowsAt1004]
    exact keyMoment1004 B hB
  · have he : k = (1005 : Fin 2886) := Fin.ext h1005
    subst k
    rw [keyMomentRowsAt1005]
    exact keyMoment1005 B hB
  · have he : k = (1006 : Fin 2886) := Fin.ext h1006
    subst k
    rw [keyMomentRowsAt1006]
    exact keyMoment1006 B hB
  · have he : k = (1007 : Fin 2886) := Fin.ext h1007
    subst k
    rw [keyMomentRowsAt1007]
    exact keyMoment1007 B hB
  · have he : k = (1008 : Fin 2886) := Fin.ext h1008
    subst k
    rw [keyMomentRowsAt1008]
    exact keyMoment1008 B hB
  · have he : k = (1009 : Fin 2886) := Fin.ext h1009
    subst k
    rw [keyMomentRowsAt1009]
    exact keyMoment1009 B hB
  · have he : k = (1010 : Fin 2886) := Fin.ext h1010
    subst k
    rw [keyMomentRowsAt1010]
    exact keyMoment1010 B hB
  · have he : k = (1011 : Fin 2886) := Fin.ext h1011
    subst k
    rw [keyMomentRowsAt1011]
    exact keyMoment1011 B hB
  · have he : k = (1012 : Fin 2886) := Fin.ext h1012
    subst k
    rw [keyMomentRowsAt1012]
    exact keyMoment1012 B hB
  · have he : k = (1013 : Fin 2886) := Fin.ext h1013
    subst k
    rw [keyMomentRowsAt1013]
    exact keyMoment1013 B hB
  · have he : k = (1014 : Fin 2886) := Fin.ext h1014
    subst k
    rw [keyMomentRowsAt1014]
    exact keyMoment1014 B hB
  · have he : k = (1015 : Fin 2886) := Fin.ext h1015
    subst k
    rw [keyMomentRowsAt1015]
    exact keyMoment1015 B hB
  · have he : k = (1016 : Fin 2886) := Fin.ext h1016
    subst k
    rw [keyMomentRowsAt1016]
    exact keyMoment1016 B hB
  · have he : k = (1017 : Fin 2886) := Fin.ext h1017
    subst k
    rw [keyMomentRowsAt1017]
    exact keyMoment1017 B hB
  · have he : k = (1018 : Fin 2886) := Fin.ext h1018
    subst k
    rw [keyMomentRowsAt1018]
    exact keyMoment1018 B hB
  · have he : k = (1019 : Fin 2886) := Fin.ext h1019
    subst k
    rw [keyMomentRowsAt1019]
    exact keyMoment1019 B hB
  · have he : k = (1020 : Fin 2886) := Fin.ext h1020
    subst k
    rw [keyMomentRowsAt1020]
    exact keyMoment1020 B hB
  · have he : k = (1021 : Fin 2886) := Fin.ext h1021
    subst k
    rw [keyMomentRowsAt1021]
    exact keyMoment1021 B hB
  · have he : k = (1022 : Fin 2886) := Fin.ext h1022
    subst k
    rw [keyMomentRowsAt1022]
    exact keyMoment1022 B hB
  · have he : k = (1023 : Fin 2886) := Fin.ext h1023
    subst k
    rw [keyMomentRowsAt1023]
    exact keyMoment1023 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI

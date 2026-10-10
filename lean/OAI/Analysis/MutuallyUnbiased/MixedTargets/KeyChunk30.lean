import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound30
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt960 : keyMomentRows (960 : Fin 2886) =
    keyMomentRow960 := by decide +kernel

theorem keyMomentRowsAt961 : keyMomentRows (961 : Fin 2886) =
    keyMomentRow961 := by decide +kernel

theorem keyMomentRowsAt962 : keyMomentRows (962 : Fin 2886) =
    keyMomentRow962 := by decide +kernel

theorem keyMomentRowsAt963 : keyMomentRows (963 : Fin 2886) =
    keyMomentRow963 := by decide +kernel

theorem keyMomentRowsAt964 : keyMomentRows (964 : Fin 2886) =
    keyMomentRow964 := by decide +kernel

theorem keyMomentRowsAt965 : keyMomentRows (965 : Fin 2886) =
    keyMomentRow965 := by decide +kernel

theorem keyMomentRowsAt966 : keyMomentRows (966 : Fin 2886) =
    keyMomentRow966 := by decide +kernel

theorem keyMomentRowsAt967 : keyMomentRows (967 : Fin 2886) =
    keyMomentRow967 := by decide +kernel

theorem keyMomentRowsAt968 : keyMomentRows (968 : Fin 2886) =
    keyMomentRow968 := by decide +kernel

theorem keyMomentRowsAt969 : keyMomentRows (969 : Fin 2886) =
    keyMomentRow969 := by decide +kernel

theorem keyMomentRowsAt970 : keyMomentRows (970 : Fin 2886) =
    keyMomentRow970 := by decide +kernel

theorem keyMomentRowsAt971 : keyMomentRows (971 : Fin 2886) =
    keyMomentRow971 := by decide +kernel

theorem keyMomentRowsAt972 : keyMomentRows (972 : Fin 2886) =
    keyMomentRow972 := by decide +kernel

theorem keyMomentRowsAt973 : keyMomentRows (973 : Fin 2886) =
    keyMomentRow973 := by decide +kernel

theorem keyMomentRowsAt974 : keyMomentRows (974 : Fin 2886) =
    keyMomentRow974 := by decide +kernel

theorem keyMomentRowsAt975 : keyMomentRows (975 : Fin 2886) =
    keyMomentRow975 := by decide +kernel

theorem keyMomentRowsAt976 : keyMomentRows (976 : Fin 2886) =
    keyMomentRow976 := by decide +kernel

theorem keyMomentRowsAt977 : keyMomentRows (977 : Fin 2886) =
    keyMomentRow977 := by decide +kernel

theorem keyMomentRowsAt978 : keyMomentRows (978 : Fin 2886) =
    keyMomentRow978 := by decide +kernel

theorem keyMomentRowsAt979 : keyMomentRows (979 : Fin 2886) =
    keyMomentRow979 := by decide +kernel

theorem keyMomentRowsAt980 : keyMomentRows (980 : Fin 2886) =
    keyMomentRow980 := by decide +kernel

theorem keyMomentRowsAt981 : keyMomentRows (981 : Fin 2886) =
    keyMomentRow981 := by decide +kernel

theorem keyMomentRowsAt982 : keyMomentRows (982 : Fin 2886) =
    keyMomentRow982 := by decide +kernel

theorem keyMomentRowsAt983 : keyMomentRows (983 : Fin 2886) =
    keyMomentRow983 := by decide +kernel

theorem keyMomentRowsAt984 : keyMomentRows (984 : Fin 2886) =
    keyMomentRow984 := by decide +kernel

theorem keyMomentRowsAt985 : keyMomentRows (985 : Fin 2886) =
    keyMomentRow985 := by decide +kernel

theorem keyMomentRowsAt986 : keyMomentRows (986 : Fin 2886) =
    keyMomentRow986 := by decide +kernel

theorem keyMomentRowsAt987 : keyMomentRows (987 : Fin 2886) =
    keyMomentRow987 := by decide +kernel

theorem keyMomentRowsAt988 : keyMomentRows (988 : Fin 2886) =
    keyMomentRow988 := by decide +kernel

theorem keyMomentRowsAt989 : keyMomentRows (989 : Fin 2886) =
    keyMomentRow989 := by decide +kernel

theorem keyMomentRowsAt990 : keyMomentRows (990 : Fin 2886) =
    keyMomentRow990 := by decide +kernel

theorem keyMomentRowsAt991 : keyMomentRows (991 : Fin 2886) =
    keyMomentRow991 := by decide +kernel

theorem keyMomentChunkSound30 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 30) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 960 ∨ k.val = 961 ∨ k.val = 962 ∨ k.val = 963 ∨ k.val = 964 ∨ k.val = 965 ∨ k.val = 966 ∨ k.val = 967 ∨ k.val = 968 ∨ k.val = 969 ∨ k.val = 970 ∨ k.val = 971 ∨ k.val = 972 ∨ k.val = 973 ∨ k.val = 974 ∨ k.val = 975 ∨ k.val = 976 ∨ k.val = 977 ∨ k.val = 978 ∨ k.val = 979 ∨ k.val = 980 ∨ k.val = 981 ∨ k.val = 982 ∨ k.val = 983 ∨ k.val = 984 ∨ k.val = 985 ∨ k.val = 986 ∨ k.val = 987 ∨ k.val = 988 ∨ k.val = 989 ∨ k.val = 990 ∨ k.val = 991 := by omega
  rcases heq with h960 | h961 | h962 | h963 | h964 | h965 | h966 | h967 | h968 | h969 | h970 | h971 | h972 | h973 | h974 | h975 | h976 | h977 | h978 | h979 | h980 | h981 | h982 | h983 | h984 | h985 | h986 | h987 | h988 | h989 | h990 | h991
  · have he : k = (960 : Fin 2886) := Fin.ext h960
    subst k
    rw [keyMomentRowsAt960]
    exact keyMoment960 B hB
  · have he : k = (961 : Fin 2886) := Fin.ext h961
    subst k
    rw [keyMomentRowsAt961]
    exact keyMoment961 B hB
  · have he : k = (962 : Fin 2886) := Fin.ext h962
    subst k
    rw [keyMomentRowsAt962]
    exact keyMoment962 B hB
  · have he : k = (963 : Fin 2886) := Fin.ext h963
    subst k
    rw [keyMomentRowsAt963]
    exact keyMoment963 B hB
  · have he : k = (964 : Fin 2886) := Fin.ext h964
    subst k
    rw [keyMomentRowsAt964]
    exact keyMoment964 B hB
  · have he : k = (965 : Fin 2886) := Fin.ext h965
    subst k
    rw [keyMomentRowsAt965]
    exact keyMoment965 B hB
  · have he : k = (966 : Fin 2886) := Fin.ext h966
    subst k
    rw [keyMomentRowsAt966]
    exact keyMoment966 B hB
  · have he : k = (967 : Fin 2886) := Fin.ext h967
    subst k
    rw [keyMomentRowsAt967]
    exact keyMoment967 B hB
  · have he : k = (968 : Fin 2886) := Fin.ext h968
    subst k
    rw [keyMomentRowsAt968]
    exact keyMoment968 B hB
  · have he : k = (969 : Fin 2886) := Fin.ext h969
    subst k
    rw [keyMomentRowsAt969]
    exact keyMoment969 B hB
  · have he : k = (970 : Fin 2886) := Fin.ext h970
    subst k
    rw [keyMomentRowsAt970]
    exact keyMoment970 B hB
  · have he : k = (971 : Fin 2886) := Fin.ext h971
    subst k
    rw [keyMomentRowsAt971]
    exact keyMoment971 B hB
  · have he : k = (972 : Fin 2886) := Fin.ext h972
    subst k
    rw [keyMomentRowsAt972]
    exact keyMoment972 B hB
  · have he : k = (973 : Fin 2886) := Fin.ext h973
    subst k
    rw [keyMomentRowsAt973]
    exact keyMoment973 B hB
  · have he : k = (974 : Fin 2886) := Fin.ext h974
    subst k
    rw [keyMomentRowsAt974]
    exact keyMoment974 B hB
  · have he : k = (975 : Fin 2886) := Fin.ext h975
    subst k
    rw [keyMomentRowsAt975]
    exact keyMoment975 B hB
  · have he : k = (976 : Fin 2886) := Fin.ext h976
    subst k
    rw [keyMomentRowsAt976]
    exact keyMoment976 B hB
  · have he : k = (977 : Fin 2886) := Fin.ext h977
    subst k
    rw [keyMomentRowsAt977]
    exact keyMoment977 B hB
  · have he : k = (978 : Fin 2886) := Fin.ext h978
    subst k
    rw [keyMomentRowsAt978]
    exact keyMoment978 B hB
  · have he : k = (979 : Fin 2886) := Fin.ext h979
    subst k
    rw [keyMomentRowsAt979]
    exact keyMoment979 B hB
  · have he : k = (980 : Fin 2886) := Fin.ext h980
    subst k
    rw [keyMomentRowsAt980]
    exact keyMoment980 B hB
  · have he : k = (981 : Fin 2886) := Fin.ext h981
    subst k
    rw [keyMomentRowsAt981]
    exact keyMoment981 B hB
  · have he : k = (982 : Fin 2886) := Fin.ext h982
    subst k
    rw [keyMomentRowsAt982]
    exact keyMoment982 B hB
  · have he : k = (983 : Fin 2886) := Fin.ext h983
    subst k
    rw [keyMomentRowsAt983]
    exact keyMoment983 B hB
  · have he : k = (984 : Fin 2886) := Fin.ext h984
    subst k
    rw [keyMomentRowsAt984]
    exact keyMoment984 B hB
  · have he : k = (985 : Fin 2886) := Fin.ext h985
    subst k
    rw [keyMomentRowsAt985]
    exact keyMoment985 B hB
  · have he : k = (986 : Fin 2886) := Fin.ext h986
    subst k
    rw [keyMomentRowsAt986]
    exact keyMoment986 B hB
  · have he : k = (987 : Fin 2886) := Fin.ext h987
    subst k
    rw [keyMomentRowsAt987]
    exact keyMoment987 B hB
  · have he : k = (988 : Fin 2886) := Fin.ext h988
    subst k
    rw [keyMomentRowsAt988]
    exact keyMoment988 B hB
  · have he : k = (989 : Fin 2886) := Fin.ext h989
    subst k
    rw [keyMomentRowsAt989]
    exact keyMoment989 B hB
  · have he : k = (990 : Fin 2886) := Fin.ext h990
    subst k
    rw [keyMomentRowsAt990]
    exact keyMoment990 B hB
  · have he : k = (991 : Fin 2886) := Fin.ext h991
    subst k
    rw [keyMomentRowsAt991]
    exact keyMoment991 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI

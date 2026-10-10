import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound29
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt928 : keyMomentRows (928 : Fin 2886) =
    keyMomentRow928 := by decide +kernel

theorem keyMomentRowsAt929 : keyMomentRows (929 : Fin 2886) =
    keyMomentRow929 := by decide +kernel

theorem keyMomentRowsAt930 : keyMomentRows (930 : Fin 2886) =
    keyMomentRow930 := by decide +kernel

theorem keyMomentRowsAt931 : keyMomentRows (931 : Fin 2886) =
    keyMomentRow931 := by decide +kernel

theorem keyMomentRowsAt932 : keyMomentRows (932 : Fin 2886) =
    keyMomentRow932 := by decide +kernel

theorem keyMomentRowsAt933 : keyMomentRows (933 : Fin 2886) =
    keyMomentRow933 := by decide +kernel

theorem keyMomentRowsAt934 : keyMomentRows (934 : Fin 2886) =
    keyMomentRow934 := by decide +kernel

theorem keyMomentRowsAt935 : keyMomentRows (935 : Fin 2886) =
    keyMomentRow935 := by decide +kernel

theorem keyMomentRowsAt936 : keyMomentRows (936 : Fin 2886) =
    keyMomentRow936 := by decide +kernel

theorem keyMomentRowsAt937 : keyMomentRows (937 : Fin 2886) =
    keyMomentRow937 := by decide +kernel

theorem keyMomentRowsAt938 : keyMomentRows (938 : Fin 2886) =
    keyMomentRow938 := by decide +kernel

theorem keyMomentRowsAt939 : keyMomentRows (939 : Fin 2886) =
    keyMomentRow939 := by decide +kernel

theorem keyMomentRowsAt940 : keyMomentRows (940 : Fin 2886) =
    keyMomentRow940 := by decide +kernel

theorem keyMomentRowsAt941 : keyMomentRows (941 : Fin 2886) =
    keyMomentRow941 := by decide +kernel

theorem keyMomentRowsAt942 : keyMomentRows (942 : Fin 2886) =
    keyMomentRow942 := by decide +kernel

theorem keyMomentRowsAt943 : keyMomentRows (943 : Fin 2886) =
    keyMomentRow943 := by decide +kernel

theorem keyMomentRowsAt944 : keyMomentRows (944 : Fin 2886) =
    keyMomentRow944 := by decide +kernel

theorem keyMomentRowsAt945 : keyMomentRows (945 : Fin 2886) =
    keyMomentRow945 := by decide +kernel

theorem keyMomentRowsAt946 : keyMomentRows (946 : Fin 2886) =
    keyMomentRow946 := by decide +kernel

theorem keyMomentRowsAt947 : keyMomentRows (947 : Fin 2886) =
    keyMomentRow947 := by decide +kernel

theorem keyMomentRowsAt948 : keyMomentRows (948 : Fin 2886) =
    keyMomentRow948 := by decide +kernel

theorem keyMomentRowsAt949 : keyMomentRows (949 : Fin 2886) =
    keyMomentRow949 := by decide +kernel

theorem keyMomentRowsAt950 : keyMomentRows (950 : Fin 2886) =
    keyMomentRow950 := by decide +kernel

theorem keyMomentRowsAt951 : keyMomentRows (951 : Fin 2886) =
    keyMomentRow951 := by decide +kernel

theorem keyMomentRowsAt952 : keyMomentRows (952 : Fin 2886) =
    keyMomentRow952 := by decide +kernel

theorem keyMomentRowsAt953 : keyMomentRows (953 : Fin 2886) =
    keyMomentRow953 := by decide +kernel

theorem keyMomentRowsAt954 : keyMomentRows (954 : Fin 2886) =
    keyMomentRow954 := by decide +kernel

theorem keyMomentRowsAt955 : keyMomentRows (955 : Fin 2886) =
    keyMomentRow955 := by decide +kernel

theorem keyMomentRowsAt956 : keyMomentRows (956 : Fin 2886) =
    keyMomentRow956 := by decide +kernel

theorem keyMomentRowsAt957 : keyMomentRows (957 : Fin 2886) =
    keyMomentRow957 := by decide +kernel

theorem keyMomentRowsAt958 : keyMomentRows (958 : Fin 2886) =
    keyMomentRow958 := by decide +kernel

theorem keyMomentRowsAt959 : keyMomentRows (959 : Fin 2886) =
    keyMomentRow959 := by decide +kernel

theorem keyMomentChunkSound29 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 29) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 928 ∨ k.val = 929 ∨ k.val = 930 ∨ k.val = 931 ∨ k.val = 932 ∨ k.val = 933 ∨ k.val = 934 ∨ k.val = 935 ∨ k.val = 936 ∨ k.val = 937 ∨ k.val = 938 ∨ k.val = 939 ∨ k.val = 940 ∨ k.val = 941 ∨ k.val = 942 ∨ k.val = 943 ∨ k.val = 944 ∨ k.val = 945 ∨ k.val = 946 ∨ k.val = 947 ∨ k.val = 948 ∨ k.val = 949 ∨ k.val = 950 ∨ k.val = 951 ∨ k.val = 952 ∨ k.val = 953 ∨ k.val = 954 ∨ k.val = 955 ∨ k.val = 956 ∨ k.val = 957 ∨ k.val = 958 ∨ k.val = 959 := by omega
  rcases heq with h928 | h929 | h930 | h931 | h932 | h933 | h934 | h935 | h936 | h937 | h938 | h939 | h940 | h941 | h942 | h943 | h944 | h945 | h946 | h947 | h948 | h949 | h950 | h951 | h952 | h953 | h954 | h955 | h956 | h957 | h958 | h959
  · have he : k = (928 : Fin 2886) := Fin.ext h928
    subst k
    rw [keyMomentRowsAt928]
    exact keyMoment928 B hB
  · have he : k = (929 : Fin 2886) := Fin.ext h929
    subst k
    rw [keyMomentRowsAt929]
    exact keyMoment929 B hB
  · have he : k = (930 : Fin 2886) := Fin.ext h930
    subst k
    rw [keyMomentRowsAt930]
    exact keyMoment930 B hB
  · have he : k = (931 : Fin 2886) := Fin.ext h931
    subst k
    rw [keyMomentRowsAt931]
    exact keyMoment931 B hB
  · have he : k = (932 : Fin 2886) := Fin.ext h932
    subst k
    rw [keyMomentRowsAt932]
    exact keyMoment932 B hB
  · have he : k = (933 : Fin 2886) := Fin.ext h933
    subst k
    rw [keyMomentRowsAt933]
    exact keyMoment933 B hB
  · have he : k = (934 : Fin 2886) := Fin.ext h934
    subst k
    rw [keyMomentRowsAt934]
    exact keyMoment934 B hB
  · have he : k = (935 : Fin 2886) := Fin.ext h935
    subst k
    rw [keyMomentRowsAt935]
    exact keyMoment935 B hB
  · have he : k = (936 : Fin 2886) := Fin.ext h936
    subst k
    rw [keyMomentRowsAt936]
    exact keyMoment936 B hB
  · have he : k = (937 : Fin 2886) := Fin.ext h937
    subst k
    rw [keyMomentRowsAt937]
    exact keyMoment937 B hB
  · have he : k = (938 : Fin 2886) := Fin.ext h938
    subst k
    rw [keyMomentRowsAt938]
    exact keyMoment938 B hB
  · have he : k = (939 : Fin 2886) := Fin.ext h939
    subst k
    rw [keyMomentRowsAt939]
    exact keyMoment939 B hB
  · have he : k = (940 : Fin 2886) := Fin.ext h940
    subst k
    rw [keyMomentRowsAt940]
    exact keyMoment940 B hB
  · have he : k = (941 : Fin 2886) := Fin.ext h941
    subst k
    rw [keyMomentRowsAt941]
    exact keyMoment941 B hB
  · have he : k = (942 : Fin 2886) := Fin.ext h942
    subst k
    rw [keyMomentRowsAt942]
    exact keyMoment942 B hB
  · have he : k = (943 : Fin 2886) := Fin.ext h943
    subst k
    rw [keyMomentRowsAt943]
    exact keyMoment943 B hB
  · have he : k = (944 : Fin 2886) := Fin.ext h944
    subst k
    rw [keyMomentRowsAt944]
    exact keyMoment944 B hB
  · have he : k = (945 : Fin 2886) := Fin.ext h945
    subst k
    rw [keyMomentRowsAt945]
    exact keyMoment945 B hB
  · have he : k = (946 : Fin 2886) := Fin.ext h946
    subst k
    rw [keyMomentRowsAt946]
    exact keyMoment946 B hB
  · have he : k = (947 : Fin 2886) := Fin.ext h947
    subst k
    rw [keyMomentRowsAt947]
    exact keyMoment947 B hB
  · have he : k = (948 : Fin 2886) := Fin.ext h948
    subst k
    rw [keyMomentRowsAt948]
    exact keyMoment948 B hB
  · have he : k = (949 : Fin 2886) := Fin.ext h949
    subst k
    rw [keyMomentRowsAt949]
    exact keyMoment949 B hB
  · have he : k = (950 : Fin 2886) := Fin.ext h950
    subst k
    rw [keyMomentRowsAt950]
    exact keyMoment950 B hB
  · have he : k = (951 : Fin 2886) := Fin.ext h951
    subst k
    rw [keyMomentRowsAt951]
    exact keyMoment951 B hB
  · have he : k = (952 : Fin 2886) := Fin.ext h952
    subst k
    rw [keyMomentRowsAt952]
    exact keyMoment952 B hB
  · have he : k = (953 : Fin 2886) := Fin.ext h953
    subst k
    rw [keyMomentRowsAt953]
    exact keyMoment953 B hB
  · have he : k = (954 : Fin 2886) := Fin.ext h954
    subst k
    rw [keyMomentRowsAt954]
    exact keyMoment954 B hB
  · have he : k = (955 : Fin 2886) := Fin.ext h955
    subst k
    rw [keyMomentRowsAt955]
    exact keyMoment955 B hB
  · have he : k = (956 : Fin 2886) := Fin.ext h956
    subst k
    rw [keyMomentRowsAt956]
    exact keyMoment956 B hB
  · have he : k = (957 : Fin 2886) := Fin.ext h957
    subst k
    rw [keyMomentRowsAt957]
    exact keyMoment957 B hB
  · have he : k = (958 : Fin 2886) := Fin.ext h958
    subst k
    rw [keyMomentRowsAt958]
    exact keyMoment958 B hB
  · have he : k = (959 : Fin 2886) := Fin.ext h959
    subst k
    rw [keyMomentRowsAt959]
    exact keyMoment959 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI

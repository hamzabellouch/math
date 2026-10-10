import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound28
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt896 : keyMomentRows (896 : Fin 2886) =
    keyMomentRow896 := by decide +kernel

theorem keyMomentRowsAt897 : keyMomentRows (897 : Fin 2886) =
    keyMomentRow897 := by decide +kernel

theorem keyMomentRowsAt898 : keyMomentRows (898 : Fin 2886) =
    keyMomentRow898 := by decide +kernel

theorem keyMomentRowsAt899 : keyMomentRows (899 : Fin 2886) =
    keyMomentRow899 := by decide +kernel

theorem keyMomentRowsAt900 : keyMomentRows (900 : Fin 2886) =
    keyMomentRow900 := by decide +kernel

theorem keyMomentRowsAt901 : keyMomentRows (901 : Fin 2886) =
    keyMomentRow901 := by decide +kernel

theorem keyMomentRowsAt902 : keyMomentRows (902 : Fin 2886) =
    keyMomentRow902 := by decide +kernel

theorem keyMomentRowsAt903 : keyMomentRows (903 : Fin 2886) =
    keyMomentRow903 := by decide +kernel

theorem keyMomentRowsAt904 : keyMomentRows (904 : Fin 2886) =
    keyMomentRow904 := by decide +kernel

theorem keyMomentRowsAt905 : keyMomentRows (905 : Fin 2886) =
    keyMomentRow905 := by decide +kernel

theorem keyMomentRowsAt906 : keyMomentRows (906 : Fin 2886) =
    keyMomentRow906 := by decide +kernel

theorem keyMomentRowsAt907 : keyMomentRows (907 : Fin 2886) =
    keyMomentRow907 := by decide +kernel

theorem keyMomentRowsAt908 : keyMomentRows (908 : Fin 2886) =
    keyMomentRow908 := by decide +kernel

theorem keyMomentRowsAt909 : keyMomentRows (909 : Fin 2886) =
    keyMomentRow909 := by decide +kernel

theorem keyMomentRowsAt910 : keyMomentRows (910 : Fin 2886) =
    keyMomentRow910 := by decide +kernel

theorem keyMomentRowsAt911 : keyMomentRows (911 : Fin 2886) =
    keyMomentRow911 := by decide +kernel

theorem keyMomentRowsAt912 : keyMomentRows (912 : Fin 2886) =
    keyMomentRow912 := by decide +kernel

theorem keyMomentRowsAt913 : keyMomentRows (913 : Fin 2886) =
    keyMomentRow913 := by decide +kernel

theorem keyMomentRowsAt914 : keyMomentRows (914 : Fin 2886) =
    keyMomentRow914 := by decide +kernel

theorem keyMomentRowsAt915 : keyMomentRows (915 : Fin 2886) =
    keyMomentRow915 := by decide +kernel

theorem keyMomentRowsAt916 : keyMomentRows (916 : Fin 2886) =
    keyMomentRow916 := by decide +kernel

theorem keyMomentRowsAt917 : keyMomentRows (917 : Fin 2886) =
    keyMomentRow917 := by decide +kernel

theorem keyMomentRowsAt918 : keyMomentRows (918 : Fin 2886) =
    keyMomentRow918 := by decide +kernel

theorem keyMomentRowsAt919 : keyMomentRows (919 : Fin 2886) =
    keyMomentRow919 := by decide +kernel

theorem keyMomentRowsAt920 : keyMomentRows (920 : Fin 2886) =
    keyMomentRow920 := by decide +kernel

theorem keyMomentRowsAt921 : keyMomentRows (921 : Fin 2886) =
    keyMomentRow921 := by decide +kernel

theorem keyMomentRowsAt922 : keyMomentRows (922 : Fin 2886) =
    keyMomentRow922 := by decide +kernel

theorem keyMomentRowsAt923 : keyMomentRows (923 : Fin 2886) =
    keyMomentRow923 := by decide +kernel

theorem keyMomentRowsAt924 : keyMomentRows (924 : Fin 2886) =
    keyMomentRow924 := by decide +kernel

theorem keyMomentRowsAt925 : keyMomentRows (925 : Fin 2886) =
    keyMomentRow925 := by decide +kernel

theorem keyMomentRowsAt926 : keyMomentRows (926 : Fin 2886) =
    keyMomentRow926 := by decide +kernel

theorem keyMomentRowsAt927 : keyMomentRows (927 : Fin 2886) =
    keyMomentRow927 := by decide +kernel

theorem keyMomentChunkSound28 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 28) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 896 ∨ k.val = 897 ∨ k.val = 898 ∨ k.val = 899 ∨ k.val = 900 ∨ k.val = 901 ∨ k.val = 902 ∨ k.val = 903 ∨ k.val = 904 ∨ k.val = 905 ∨ k.val = 906 ∨ k.val = 907 ∨ k.val = 908 ∨ k.val = 909 ∨ k.val = 910 ∨ k.val = 911 ∨ k.val = 912 ∨ k.val = 913 ∨ k.val = 914 ∨ k.val = 915 ∨ k.val = 916 ∨ k.val = 917 ∨ k.val = 918 ∨ k.val = 919 ∨ k.val = 920 ∨ k.val = 921 ∨ k.val = 922 ∨ k.val = 923 ∨ k.val = 924 ∨ k.val = 925 ∨ k.val = 926 ∨ k.val = 927 := by omega
  rcases heq with h896 | h897 | h898 | h899 | h900 | h901 | h902 | h903 | h904 | h905 | h906 | h907 | h908 | h909 | h910 | h911 | h912 | h913 | h914 | h915 | h916 | h917 | h918 | h919 | h920 | h921 | h922 | h923 | h924 | h925 | h926 | h927
  · have he : k = (896 : Fin 2886) := Fin.ext h896
    subst k
    rw [keyMomentRowsAt896]
    exact keyMoment896 B hB
  · have he : k = (897 : Fin 2886) := Fin.ext h897
    subst k
    rw [keyMomentRowsAt897]
    exact keyMoment897 B hB
  · have he : k = (898 : Fin 2886) := Fin.ext h898
    subst k
    rw [keyMomentRowsAt898]
    exact keyMoment898 B hB
  · have he : k = (899 : Fin 2886) := Fin.ext h899
    subst k
    rw [keyMomentRowsAt899]
    exact keyMoment899 B hB
  · have he : k = (900 : Fin 2886) := Fin.ext h900
    subst k
    rw [keyMomentRowsAt900]
    exact keyMoment900 B hB
  · have he : k = (901 : Fin 2886) := Fin.ext h901
    subst k
    rw [keyMomentRowsAt901]
    exact keyMoment901 B hB
  · have he : k = (902 : Fin 2886) := Fin.ext h902
    subst k
    rw [keyMomentRowsAt902]
    exact keyMoment902 B hB
  · have he : k = (903 : Fin 2886) := Fin.ext h903
    subst k
    rw [keyMomentRowsAt903]
    exact keyMoment903 B hB
  · have he : k = (904 : Fin 2886) := Fin.ext h904
    subst k
    rw [keyMomentRowsAt904]
    exact keyMoment904 B hB
  · have he : k = (905 : Fin 2886) := Fin.ext h905
    subst k
    rw [keyMomentRowsAt905]
    exact keyMoment905 B hB
  · have he : k = (906 : Fin 2886) := Fin.ext h906
    subst k
    rw [keyMomentRowsAt906]
    exact keyMoment906 B hB
  · have he : k = (907 : Fin 2886) := Fin.ext h907
    subst k
    rw [keyMomentRowsAt907]
    exact keyMoment907 B hB
  · have he : k = (908 : Fin 2886) := Fin.ext h908
    subst k
    rw [keyMomentRowsAt908]
    exact keyMoment908 B hB
  · have he : k = (909 : Fin 2886) := Fin.ext h909
    subst k
    rw [keyMomentRowsAt909]
    exact keyMoment909 B hB
  · have he : k = (910 : Fin 2886) := Fin.ext h910
    subst k
    rw [keyMomentRowsAt910]
    exact keyMoment910 B hB
  · have he : k = (911 : Fin 2886) := Fin.ext h911
    subst k
    rw [keyMomentRowsAt911]
    exact keyMoment911 B hB
  · have he : k = (912 : Fin 2886) := Fin.ext h912
    subst k
    rw [keyMomentRowsAt912]
    exact keyMoment912 B hB
  · have he : k = (913 : Fin 2886) := Fin.ext h913
    subst k
    rw [keyMomentRowsAt913]
    exact keyMoment913 B hB
  · have he : k = (914 : Fin 2886) := Fin.ext h914
    subst k
    rw [keyMomentRowsAt914]
    exact keyMoment914 B hB
  · have he : k = (915 : Fin 2886) := Fin.ext h915
    subst k
    rw [keyMomentRowsAt915]
    exact keyMoment915 B hB
  · have he : k = (916 : Fin 2886) := Fin.ext h916
    subst k
    rw [keyMomentRowsAt916]
    exact keyMoment916 B hB
  · have he : k = (917 : Fin 2886) := Fin.ext h917
    subst k
    rw [keyMomentRowsAt917]
    exact keyMoment917 B hB
  · have he : k = (918 : Fin 2886) := Fin.ext h918
    subst k
    rw [keyMomentRowsAt918]
    exact keyMoment918 B hB
  · have he : k = (919 : Fin 2886) := Fin.ext h919
    subst k
    rw [keyMomentRowsAt919]
    exact keyMoment919 B hB
  · have he : k = (920 : Fin 2886) := Fin.ext h920
    subst k
    rw [keyMomentRowsAt920]
    exact keyMoment920 B hB
  · have he : k = (921 : Fin 2886) := Fin.ext h921
    subst k
    rw [keyMomentRowsAt921]
    exact keyMoment921 B hB
  · have he : k = (922 : Fin 2886) := Fin.ext h922
    subst k
    rw [keyMomentRowsAt922]
    exact keyMoment922 B hB
  · have he : k = (923 : Fin 2886) := Fin.ext h923
    subst k
    rw [keyMomentRowsAt923]
    exact keyMoment923 B hB
  · have he : k = (924 : Fin 2886) := Fin.ext h924
    subst k
    rw [keyMomentRowsAt924]
    exact keyMoment924 B hB
  · have he : k = (925 : Fin 2886) := Fin.ext h925
    subst k
    rw [keyMomentRowsAt925]
    exact keyMoment925 B hB
  · have he : k = (926 : Fin 2886) := Fin.ext h926
    subst k
    rw [keyMomentRowsAt926]
    exact keyMoment926 B hB
  · have he : k = (927 : Fin 2886) := Fin.ext h927
    subst k
    rw [keyMomentRowsAt927]
    exact keyMoment927 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI

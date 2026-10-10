import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound90
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2880 : keyMomentRows (2880 : Fin 2886) =
    keyMomentRow2880 := by decide +kernel

theorem keyMomentRowsAt2881 : keyMomentRows (2881 : Fin 2886) =
    keyMomentRow2881 := by decide +kernel

theorem keyMomentRowsAt2882 : keyMomentRows (2882 : Fin 2886) =
    keyMomentRow2882 := by decide +kernel

theorem keyMomentRowsAt2883 : keyMomentRows (2883 : Fin 2886) =
    keyMomentRow2883 := by decide +kernel

theorem keyMomentRowsAt2884 : keyMomentRows (2884 : Fin 2886) =
    keyMomentRow2884 := by decide +kernel

theorem keyMomentRowsAt2885 : keyMomentRows (2885 : Fin 2886) =
    keyMomentRow2885 := by decide +kernel

theorem keyMomentChunkSound90 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 90) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2880 ∨ k.val = 2881 ∨ k.val = 2882 ∨ k.val = 2883 ∨ k.val = 2884 ∨ k.val = 2885 := by omega
  rcases heq with h2880 | h2881 | h2882 | h2883 | h2884 | h2885
  · have he : k = (2880 : Fin 2886) := Fin.ext h2880
    subst k
    rw [keyMomentRowsAt2880]
    exact keyMoment2880 B hB
  · have he : k = (2881 : Fin 2886) := Fin.ext h2881
    subst k
    rw [keyMomentRowsAt2881]
    exact keyMoment2881 B hB
  · have he : k = (2882 : Fin 2886) := Fin.ext h2882
    subst k
    rw [keyMomentRowsAt2882]
    exact keyMoment2882 B hB
  · have he : k = (2883 : Fin 2886) := Fin.ext h2883
    subst k
    rw [keyMomentRowsAt2883]
    exact keyMoment2883 B hB
  · have he : k = (2884 : Fin 2886) := Fin.ext h2884
    subst k
    rw [keyMomentRowsAt2884]
    exact keyMoment2884 B hB
  · have he : k = (2885 : Fin 2886) := Fin.ext h2885
    subst k
    rw [keyMomentRowsAt2885]
    exact keyMoment2885 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI

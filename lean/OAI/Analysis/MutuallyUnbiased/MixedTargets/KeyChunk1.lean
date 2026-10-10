import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound1
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt32 : keyMomentRows (32 : Fin 2886) =
    keyMomentRow32 := by decide +kernel

theorem keyMomentRowsAt33 : keyMomentRows (33 : Fin 2886) =
    keyMomentRow33 := by decide +kernel

theorem keyMomentRowsAt34 : keyMomentRows (34 : Fin 2886) =
    keyMomentRow34 := by decide +kernel

theorem keyMomentRowsAt35 : keyMomentRows (35 : Fin 2886) =
    keyMomentRow35 := by decide +kernel

theorem keyMomentRowsAt36 : keyMomentRows (36 : Fin 2886) =
    keyMomentRow36 := by decide +kernel

theorem keyMomentRowsAt37 : keyMomentRows (37 : Fin 2886) =
    keyMomentRow37 := by decide +kernel

theorem keyMomentRowsAt38 : keyMomentRows (38 : Fin 2886) =
    keyMomentRow38 := by decide +kernel

theorem keyMomentRowsAt39 : keyMomentRows (39 : Fin 2886) =
    keyMomentRow39 := by decide +kernel

theorem keyMomentRowsAt40 : keyMomentRows (40 : Fin 2886) =
    keyMomentRow40 := by decide +kernel

theorem keyMomentRowsAt41 : keyMomentRows (41 : Fin 2886) =
    keyMomentRow41 := by decide +kernel

theorem keyMomentRowsAt42 : keyMomentRows (42 : Fin 2886) =
    keyMomentRow42 := by decide +kernel

theorem keyMomentRowsAt43 : keyMomentRows (43 : Fin 2886) =
    keyMomentRow43 := by decide +kernel

theorem keyMomentRowsAt44 : keyMomentRows (44 : Fin 2886) =
    keyMomentRow44 := by decide +kernel

theorem keyMomentRowsAt45 : keyMomentRows (45 : Fin 2886) =
    keyMomentRow45 := by decide +kernel

theorem keyMomentRowsAt46 : keyMomentRows (46 : Fin 2886) =
    keyMomentRow46 := by decide +kernel

theorem keyMomentRowsAt47 : keyMomentRows (47 : Fin 2886) =
    keyMomentRow47 := by decide +kernel

theorem keyMomentRowsAt48 : keyMomentRows (48 : Fin 2886) =
    keyMomentRow48 := by decide +kernel

theorem keyMomentRowsAt49 : keyMomentRows (49 : Fin 2886) =
    keyMomentRow49 := by decide +kernel

theorem keyMomentRowsAt50 : keyMomentRows (50 : Fin 2886) =
    keyMomentRow50 := by decide +kernel

theorem keyMomentRowsAt51 : keyMomentRows (51 : Fin 2886) =
    keyMomentRow51 := by decide +kernel

theorem keyMomentRowsAt52 : keyMomentRows (52 : Fin 2886) =
    keyMomentRow52 := by decide +kernel

theorem keyMomentRowsAt53 : keyMomentRows (53 : Fin 2886) =
    keyMomentRow53 := by decide +kernel

theorem keyMomentRowsAt54 : keyMomentRows (54 : Fin 2886) =
    keyMomentRow54 := by decide +kernel

theorem keyMomentRowsAt55 : keyMomentRows (55 : Fin 2886) =
    keyMomentRow55 := by decide +kernel

theorem keyMomentRowsAt56 : keyMomentRows (56 : Fin 2886) =
    keyMomentRow56 := by decide +kernel

theorem keyMomentRowsAt57 : keyMomentRows (57 : Fin 2886) =
    keyMomentRow57 := by decide +kernel

theorem keyMomentRowsAt58 : keyMomentRows (58 : Fin 2886) =
    keyMomentRow58 := by decide +kernel

theorem keyMomentRowsAt59 : keyMomentRows (59 : Fin 2886) =
    keyMomentRow59 := by decide +kernel

theorem keyMomentRowsAt60 : keyMomentRows (60 : Fin 2886) =
    keyMomentRow60 := by decide +kernel

theorem keyMomentRowsAt61 : keyMomentRows (61 : Fin 2886) =
    keyMomentRow61 := by decide +kernel

theorem keyMomentRowsAt62 : keyMomentRows (62 : Fin 2886) =
    keyMomentRow62 := by decide +kernel

theorem keyMomentRowsAt63 : keyMomentRows (63 : Fin 2886) =
    keyMomentRow63 := by decide +kernel

theorem keyMomentChunkSound1 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 1) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 32 ∨ k.val = 33 ∨ k.val = 34 ∨ k.val = 35 ∨ k.val = 36 ∨ k.val = 37 ∨ k.val = 38 ∨ k.val = 39 ∨ k.val = 40 ∨ k.val = 41 ∨ k.val = 42 ∨ k.val = 43 ∨ k.val = 44 ∨ k.val = 45 ∨ k.val = 46 ∨ k.val = 47 ∨ k.val = 48 ∨ k.val = 49 ∨ k.val = 50 ∨ k.val = 51 ∨ k.val = 52 ∨ k.val = 53 ∨ k.val = 54 ∨ k.val = 55 ∨ k.val = 56 ∨ k.val = 57 ∨ k.val = 58 ∨ k.val = 59 ∨ k.val = 60 ∨ k.val = 61 ∨ k.val = 62 ∨ k.val = 63 := by omega
  rcases heq with h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57 | h58 | h59 | h60 | h61 | h62 | h63
  · have he : k = (32 : Fin 2886) := Fin.ext h32
    subst k
    rw [keyMomentRowsAt32]
    exact keyMoment32 B hB
  · have he : k = (33 : Fin 2886) := Fin.ext h33
    subst k
    rw [keyMomentRowsAt33]
    exact keyMoment33 B hB
  · have he : k = (34 : Fin 2886) := Fin.ext h34
    subst k
    rw [keyMomentRowsAt34]
    exact keyMoment34 B hB
  · have he : k = (35 : Fin 2886) := Fin.ext h35
    subst k
    rw [keyMomentRowsAt35]
    exact keyMoment35 B hB
  · have he : k = (36 : Fin 2886) := Fin.ext h36
    subst k
    rw [keyMomentRowsAt36]
    exact keyMoment36 B hB
  · have he : k = (37 : Fin 2886) := Fin.ext h37
    subst k
    rw [keyMomentRowsAt37]
    exact keyMoment37 B hB
  · have he : k = (38 : Fin 2886) := Fin.ext h38
    subst k
    rw [keyMomentRowsAt38]
    exact keyMoment38 B hB
  · have he : k = (39 : Fin 2886) := Fin.ext h39
    subst k
    rw [keyMomentRowsAt39]
    exact keyMoment39 B hB
  · have he : k = (40 : Fin 2886) := Fin.ext h40
    subst k
    rw [keyMomentRowsAt40]
    exact keyMoment40 B hB
  · have he : k = (41 : Fin 2886) := Fin.ext h41
    subst k
    rw [keyMomentRowsAt41]
    exact keyMoment41 B hB
  · have he : k = (42 : Fin 2886) := Fin.ext h42
    subst k
    rw [keyMomentRowsAt42]
    exact keyMoment42 B hB
  · have he : k = (43 : Fin 2886) := Fin.ext h43
    subst k
    rw [keyMomentRowsAt43]
    exact keyMoment43 B hB
  · have he : k = (44 : Fin 2886) := Fin.ext h44
    subst k
    rw [keyMomentRowsAt44]
    exact keyMoment44 B hB
  · have he : k = (45 : Fin 2886) := Fin.ext h45
    subst k
    rw [keyMomentRowsAt45]
    exact keyMoment45 B hB
  · have he : k = (46 : Fin 2886) := Fin.ext h46
    subst k
    rw [keyMomentRowsAt46]
    exact keyMoment46 B hB
  · have he : k = (47 : Fin 2886) := Fin.ext h47
    subst k
    rw [keyMomentRowsAt47]
    exact keyMoment47 B hB
  · have he : k = (48 : Fin 2886) := Fin.ext h48
    subst k
    rw [keyMomentRowsAt48]
    exact keyMoment48 B hB
  · have he : k = (49 : Fin 2886) := Fin.ext h49
    subst k
    rw [keyMomentRowsAt49]
    exact keyMoment49 B hB
  · have he : k = (50 : Fin 2886) := Fin.ext h50
    subst k
    rw [keyMomentRowsAt50]
    exact keyMoment50 B hB
  · have he : k = (51 : Fin 2886) := Fin.ext h51
    subst k
    rw [keyMomentRowsAt51]
    exact keyMoment51 B hB
  · have he : k = (52 : Fin 2886) := Fin.ext h52
    subst k
    rw [keyMomentRowsAt52]
    exact keyMoment52 B hB
  · have he : k = (53 : Fin 2886) := Fin.ext h53
    subst k
    rw [keyMomentRowsAt53]
    exact keyMoment53 B hB
  · have he : k = (54 : Fin 2886) := Fin.ext h54
    subst k
    rw [keyMomentRowsAt54]
    exact keyMoment54 B hB
  · have he : k = (55 : Fin 2886) := Fin.ext h55
    subst k
    rw [keyMomentRowsAt55]
    exact keyMoment55 B hB
  · have he : k = (56 : Fin 2886) := Fin.ext h56
    subst k
    rw [keyMomentRowsAt56]
    exact keyMoment56 B hB
  · have he : k = (57 : Fin 2886) := Fin.ext h57
    subst k
    rw [keyMomentRowsAt57]
    exact keyMoment57 B hB
  · have he : k = (58 : Fin 2886) := Fin.ext h58
    subst k
    rw [keyMomentRowsAt58]
    exact keyMoment58 B hB
  · have he : k = (59 : Fin 2886) := Fin.ext h59
    subst k
    rw [keyMomentRowsAt59]
    exact keyMoment59 B hB
  · have he : k = (60 : Fin 2886) := Fin.ext h60
    subst k
    rw [keyMomentRowsAt60]
    exact keyMoment60 B hB
  · have he : k = (61 : Fin 2886) := Fin.ext h61
    subst k
    rw [keyMomentRowsAt61]
    exact keyMoment61 B hB
  · have he : k = (62 : Fin 2886) := Fin.ext h62
    subst k
    rw [keyMomentRowsAt62]
    exact keyMoment62 B hB
  · have he : k = (63 : Fin 2886) := Fin.ext h63
    subst k
    rw [keyMomentRowsAt63]
    exact keyMoment63 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI

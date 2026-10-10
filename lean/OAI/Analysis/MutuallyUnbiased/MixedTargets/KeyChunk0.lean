import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound0
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt0 : keyMomentRows (0 : Fin 2886) =
    keyMomentRow0 := by decide +kernel

theorem keyMomentRowsAt1 : keyMomentRows (1 : Fin 2886) =
    keyMomentRow1 := by decide +kernel

theorem keyMomentRowsAt2 : keyMomentRows (2 : Fin 2886) =
    keyMomentRow2 := by decide +kernel

theorem keyMomentRowsAt3 : keyMomentRows (3 : Fin 2886) =
    keyMomentRow3 := by decide +kernel

theorem keyMomentRowsAt4 : keyMomentRows (4 : Fin 2886) =
    keyMomentRow4 := by decide +kernel

theorem keyMomentRowsAt5 : keyMomentRows (5 : Fin 2886) =
    keyMomentRow5 := by decide +kernel

theorem keyMomentRowsAt6 : keyMomentRows (6 : Fin 2886) =
    keyMomentRow6 := by decide +kernel

theorem keyMomentRowsAt7 : keyMomentRows (7 : Fin 2886) =
    keyMomentRow7 := by decide +kernel

theorem keyMomentRowsAt8 : keyMomentRows (8 : Fin 2886) =
    keyMomentRow8 := by decide +kernel

theorem keyMomentRowsAt9 : keyMomentRows (9 : Fin 2886) =
    keyMomentRow9 := by decide +kernel

theorem keyMomentRowsAt10 : keyMomentRows (10 : Fin 2886) =
    keyMomentRow10 := by decide +kernel

theorem keyMomentRowsAt11 : keyMomentRows (11 : Fin 2886) =
    keyMomentRow11 := by decide +kernel

theorem keyMomentRowsAt12 : keyMomentRows (12 : Fin 2886) =
    keyMomentRow12 := by decide +kernel

theorem keyMomentRowsAt13 : keyMomentRows (13 : Fin 2886) =
    keyMomentRow13 := by decide +kernel

theorem keyMomentRowsAt14 : keyMomentRows (14 : Fin 2886) =
    keyMomentRow14 := by decide +kernel

theorem keyMomentRowsAt15 : keyMomentRows (15 : Fin 2886) =
    keyMomentRow15 := by decide +kernel

theorem keyMomentRowsAt16 : keyMomentRows (16 : Fin 2886) =
    keyMomentRow16 := by decide +kernel

theorem keyMomentRowsAt17 : keyMomentRows (17 : Fin 2886) =
    keyMomentRow17 := by decide +kernel

theorem keyMomentRowsAt18 : keyMomentRows (18 : Fin 2886) =
    keyMomentRow18 := by decide +kernel

theorem keyMomentRowsAt19 : keyMomentRows (19 : Fin 2886) =
    keyMomentRow19 := by decide +kernel

theorem keyMomentRowsAt20 : keyMomentRows (20 : Fin 2886) =
    keyMomentRow20 := by decide +kernel

theorem keyMomentRowsAt21 : keyMomentRows (21 : Fin 2886) =
    keyMomentRow21 := by decide +kernel

theorem keyMomentRowsAt22 : keyMomentRows (22 : Fin 2886) =
    keyMomentRow22 := by decide +kernel

theorem keyMomentRowsAt23 : keyMomentRows (23 : Fin 2886) =
    keyMomentRow23 := by decide +kernel

theorem keyMomentRowsAt24 : keyMomentRows (24 : Fin 2886) =
    keyMomentRow24 := by decide +kernel

theorem keyMomentRowsAt25 : keyMomentRows (25 : Fin 2886) =
    keyMomentRow25 := by decide +kernel

theorem keyMomentRowsAt26 : keyMomentRows (26 : Fin 2886) =
    keyMomentRow26 := by decide +kernel

theorem keyMomentRowsAt27 : keyMomentRows (27 : Fin 2886) =
    keyMomentRow27 := by decide +kernel

theorem keyMomentRowsAt28 : keyMomentRows (28 : Fin 2886) =
    keyMomentRow28 := by decide +kernel

theorem keyMomentRowsAt29 : keyMomentRows (29 : Fin 2886) =
    keyMomentRow29 := by decide +kernel

theorem keyMomentRowsAt30 : keyMomentRows (30 : Fin 2886) =
    keyMomentRow30 := by decide +kernel

theorem keyMomentRowsAt31 : keyMomentRows (31 : Fin 2886) =
    keyMomentRow31 := by decide +kernel

theorem keyMomentChunkSound0 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 0) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3 ∨ k.val = 4 ∨ k.val = 5 ∨ k.val = 6 ∨ k.val = 7 ∨ k.val = 8 ∨ k.val = 9 ∨ k.val = 10 ∨ k.val = 11 ∨ k.val = 12 ∨ k.val = 13 ∨ k.val = 14 ∨ k.val = 15 ∨ k.val = 16 ∨ k.val = 17 ∨ k.val = 18 ∨ k.val = 19 ∨ k.val = 20 ∨ k.val = 21 ∨ k.val = 22 ∨ k.val = 23 ∨ k.val = 24 ∨ k.val = 25 ∨ k.val = 26 ∨ k.val = 27 ∨ k.val = 28 ∨ k.val = 29 ∨ k.val = 30 ∨ k.val = 31 := by omega
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31
  · have he : k = (0 : Fin 2886) := Fin.ext h0
    subst k
    rw [keyMomentRowsAt0]
    exact keyMoment0 B hB
  · have he : k = (1 : Fin 2886) := Fin.ext h1
    subst k
    rw [keyMomentRowsAt1]
    exact keyMoment1 B hB
  · have he : k = (2 : Fin 2886) := Fin.ext h2
    subst k
    rw [keyMomentRowsAt2]
    exact keyMoment2 B hB
  · have he : k = (3 : Fin 2886) := Fin.ext h3
    subst k
    rw [keyMomentRowsAt3]
    exact keyMoment3 B hB
  · have he : k = (4 : Fin 2886) := Fin.ext h4
    subst k
    rw [keyMomentRowsAt4]
    exact keyMoment4 B hB
  · have he : k = (5 : Fin 2886) := Fin.ext h5
    subst k
    rw [keyMomentRowsAt5]
    exact keyMoment5 B hB
  · have he : k = (6 : Fin 2886) := Fin.ext h6
    subst k
    rw [keyMomentRowsAt6]
    exact keyMoment6 B hB
  · have he : k = (7 : Fin 2886) := Fin.ext h7
    subst k
    rw [keyMomentRowsAt7]
    exact keyMoment7 B hB
  · have he : k = (8 : Fin 2886) := Fin.ext h8
    subst k
    rw [keyMomentRowsAt8]
    exact keyMoment8 B hB
  · have he : k = (9 : Fin 2886) := Fin.ext h9
    subst k
    rw [keyMomentRowsAt9]
    exact keyMoment9 B hB
  · have he : k = (10 : Fin 2886) := Fin.ext h10
    subst k
    rw [keyMomentRowsAt10]
    exact keyMoment10 B hB
  · have he : k = (11 : Fin 2886) := Fin.ext h11
    subst k
    rw [keyMomentRowsAt11]
    exact keyMoment11 B hB
  · have he : k = (12 : Fin 2886) := Fin.ext h12
    subst k
    rw [keyMomentRowsAt12]
    exact keyMoment12 B hB
  · have he : k = (13 : Fin 2886) := Fin.ext h13
    subst k
    rw [keyMomentRowsAt13]
    exact keyMoment13 B hB
  · have he : k = (14 : Fin 2886) := Fin.ext h14
    subst k
    rw [keyMomentRowsAt14]
    exact keyMoment14 B hB
  · have he : k = (15 : Fin 2886) := Fin.ext h15
    subst k
    rw [keyMomentRowsAt15]
    exact keyMoment15 B hB
  · have he : k = (16 : Fin 2886) := Fin.ext h16
    subst k
    rw [keyMomentRowsAt16]
    exact keyMoment16 B hB
  · have he : k = (17 : Fin 2886) := Fin.ext h17
    subst k
    rw [keyMomentRowsAt17]
    exact keyMoment17 B hB
  · have he : k = (18 : Fin 2886) := Fin.ext h18
    subst k
    rw [keyMomentRowsAt18]
    exact keyMoment18 B hB
  · have he : k = (19 : Fin 2886) := Fin.ext h19
    subst k
    rw [keyMomentRowsAt19]
    exact keyMoment19 B hB
  · have he : k = (20 : Fin 2886) := Fin.ext h20
    subst k
    rw [keyMomentRowsAt20]
    exact keyMoment20 B hB
  · have he : k = (21 : Fin 2886) := Fin.ext h21
    subst k
    rw [keyMomentRowsAt21]
    exact keyMoment21 B hB
  · have he : k = (22 : Fin 2886) := Fin.ext h22
    subst k
    rw [keyMomentRowsAt22]
    exact keyMoment22 B hB
  · have he : k = (23 : Fin 2886) := Fin.ext h23
    subst k
    rw [keyMomentRowsAt23]
    exact keyMoment23 B hB
  · have he : k = (24 : Fin 2886) := Fin.ext h24
    subst k
    rw [keyMomentRowsAt24]
    exact keyMoment24 B hB
  · have he : k = (25 : Fin 2886) := Fin.ext h25
    subst k
    rw [keyMomentRowsAt25]
    exact keyMoment25 B hB
  · have he : k = (26 : Fin 2886) := Fin.ext h26
    subst k
    rw [keyMomentRowsAt26]
    exact keyMoment26 B hB
  · have he : k = (27 : Fin 2886) := Fin.ext h27
    subst k
    rw [keyMomentRowsAt27]
    exact keyMoment27 B hB
  · have he : k = (28 : Fin 2886) := Fin.ext h28
    subst k
    rw [keyMomentRowsAt28]
    exact keyMoment28 B hB
  · have he : k = (29 : Fin 2886) := Fin.ext h29
    subst k
    rw [keyMomentRowsAt29]
    exact keyMoment29 B hB
  · have he : k = (30 : Fin 2886) := Fin.ext h30
    subst k
    rw [keyMomentRowsAt30]
    exact keyMoment30 B hB
  · have he : k = (31 : Fin 2886) := Fin.ext h31
    subst k
    rw [keyMomentRowsAt31]
    exact keyMoment31 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI

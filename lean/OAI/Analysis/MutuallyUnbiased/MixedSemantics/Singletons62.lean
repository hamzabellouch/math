import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical5

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall3969 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3969 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3969 node3969Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node511 node511Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw586 singletonSmall3969
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3969) = raw586Labels := by decide +kernel
  rw [hl, canonical586 B hB] at h
  have hc0 : mixedMoment B raw586 (Fin.cases (0 : Fin 1) singletonSmall3969) =
      mixedMoment B node511 node511Labels := by
    have ha : raw586 = raw587 := by apply Matrix.ext; unfold raw586 raw587; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3969 = raw587Labels := by decide +kernel
    rw [ha, hj, canonical587 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3970 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3970 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3970 node3970Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node454 node454Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw588 singletonSmall3970
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3970) = raw588Labels := by decide +kernel
  rw [hl, canonical588 B hB] at h
  have hc0 : mixedMoment B raw588 (Fin.cases (0 : Fin 1) singletonSmall3970) =
      mixedMoment B node454 node454Labels := by
    have ha : raw588 = raw589 := by apply Matrix.ext; unfold raw588 raw589; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3970 = raw589Labels := by decide +kernel
    rw [ha, hj, canonical589 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3977 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3977 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3977 node3977Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node461 node461Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw590 singletonSmall3977
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3977) = raw590Labels := by decide +kernel
  rw [hl, canonical590 B hB] at h
  have hc0 : mixedMoment B raw590 (Fin.cases (0 : Fin 1) singletonSmall3977) =
      mixedMoment B node461 node461Labels := by
    have ha : raw590 = raw591 := by apply Matrix.ext; unfold raw590 raw591; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3977 = raw591Labels := by decide +kernel
    rw [ha, hj, canonical591 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3980 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3980 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3980 node3980Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node520 node520Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw592 singletonSmall3980
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3980) = raw592Labels := by decide +kernel
  rw [hl, canonical592 B hB] at h
  have hc0 : mixedMoment B raw592 (Fin.cases (0 : Fin 1) singletonSmall3980) =
      mixedMoment B node520 node520Labels := by
    have ha : raw592 = raw593 := by apply Matrix.ext; unfold raw592 raw593; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3980 = raw593Labels := by decide +kernel
    rw [ha, hj, canonical593 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3981 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3981 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3981 node3981Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node521 node521Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw594 singletonSmall3981
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3981) = raw594Labels := by decide +kernel
  rw [hl, canonical594 B hB] at h
  have hc0 : mixedMoment B raw594 (Fin.cases (0 : Fin 1) singletonSmall3981) =
      mixedMoment B node521 node521Labels := by
    have ha : raw594 = raw595 := by apply Matrix.ext; unfold raw594 raw595; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3981 = raw595Labels := by decide +kernel
    rw [ha, hj, canonical595 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3982 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3982 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3982 node3982Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node489 node489Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw596 singletonSmall3982
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3982) = raw596Labels := by decide +kernel
  rw [hl, canonical596 B hB] at h
  have hc0 : mixedMoment B raw596 (Fin.cases (0 : Fin 1) singletonSmall3982) =
      mixedMoment B node489 node489Labels := by
    have ha : raw596 = raw597 := by apply Matrix.ext; unfold raw596 raw597; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3982 = raw597Labels := by decide +kernel
    rw [ha, hj, canonical597 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3984 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3984 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3984 node3984Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node523 node523Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw598 singletonSmall3984
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3984) = raw598Labels := by decide +kernel
  rw [hl, canonical598 B hB] at h
  have hc0 : mixedMoment B raw598 (Fin.cases (0 : Fin 1) singletonSmall3984) =
      mixedMoment B node523 node523Labels := by
    have ha : raw598 = raw599 := by apply Matrix.ext; unfold raw598 raw599; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3984 = raw599Labels := by decide +kernel
    rw [ha, hj, canonical599 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3987 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3987 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3987 node3987Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node503 node503Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw600 singletonSmall3987
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3987) = raw600Labels := by decide +kernel
  rw [hl, canonical600 B hB] at h
  have hc0 : mixedMoment B raw600 (Fin.cases (0 : Fin 1) singletonSmall3987) =
      mixedMoment B node503 node503Labels := by
    have ha : raw600 = raw601 := by apply Matrix.ext; unfold raw600 raw601; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3987 = raw601Labels := by decide +kernel
    rw [ha, hj, canonical601 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3990 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3990 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3990 node3990Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node479 node479Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw602 singletonSmall3990
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3990) = raw602Labels := by decide +kernel
  rw [hl, canonical602 B hB] at h
  have hc0 : mixedMoment B raw602 (Fin.cases (0 : Fin 1) singletonSmall3990) =
      mixedMoment B node479 node479Labels := by
    have ha : raw602 = raw603 := by apply Matrix.ext; unfold raw602 raw603; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3990 = raw603Labels := by decide +kernel
    rw [ha, hj, canonical603 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3992 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3992 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3992 node3992Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node520 node520Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw604 singletonSmall3992
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3992) = raw604Labels := by decide +kernel
  rw [hl, canonical604 B hB] at h
  have hc0 : mixedMoment B raw604 (Fin.cases (0 : Fin 1) singletonSmall3992) =
      mixedMoment B node520 node520Labels := by
    have ha : raw604 = raw605 := by apply Matrix.ext; unfold raw604 raw605; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3992 = raw605Labels := by decide +kernel
    rw [ha, hj, canonical605 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3993 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3993 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3993 node3993Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node493 node493Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw606 singletonSmall3993
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3993) = raw606Labels := by decide +kernel
  rw [hl, canonical606 B hB] at h
  have hc0 : mixedMoment B raw606 (Fin.cases (0 : Fin 1) singletonSmall3993) =
      mixedMoment B node493 node493Labels := by
    have ha : raw606 = raw607 := by apply Matrix.ext; unfold raw606 raw607; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3993 = raw607Labels := by decide +kernel
    rw [ha, hj, canonical607 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3994 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3994 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3994 node3994Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node519 node519Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw608 singletonSmall3994
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3994) = raw608Labels := by decide +kernel
  rw [hl, canonical608 B hB] at h
  have hc0 : mixedMoment B raw608 (Fin.cases (0 : Fin 1) singletonSmall3994) =
      mixedMoment B node519 node519Labels := by
    have ha : raw608 = raw609 := by apply Matrix.ext; unfold raw608 raw609; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3994 = raw609Labels := by decide +kernel
    rw [ha, hj, canonical609 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3995 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3995 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3995 node3995Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node514 node514Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw610 singletonSmall3995
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3995) = raw610Labels := by decide +kernel
  rw [hl, canonical610 B hB] at h
  have hc0 : mixedMoment B raw610 (Fin.cases (0 : Fin 1) singletonSmall3995) =
      mixedMoment B node514 node514Labels := by
    have ha : raw610 = raw611 := by apply Matrix.ext; unfold raw610 raw611; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3995 = raw611Labels := by decide +kernel
    rw [ha, hj, canonical611 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3997 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3997 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3997 node3997Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node522 node522Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw612 singletonSmall3997
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3997) = raw612Labels := by decide +kernel
  rw [hl, canonical612 B hB] at h
  have hc0 : mixedMoment B raw612 (Fin.cases (0 : Fin 1) singletonSmall3997) =
      mixedMoment B node522 node522Labels := by
    have ha : raw612 = raw613 := by apply Matrix.ext; unfold raw612 raw613; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3997 = raw613Labels := by decide +kernel
    rw [ha, hj, canonical613 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall3998 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3998 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3998 node3998Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node523 node523Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw614 singletonSmall3998
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3998) = raw614Labels := by decide +kernel
  rw [hl, canonical614 B hB] at h
  have hc0 : mixedMoment B raw614 (Fin.cases (0 : Fin 1) singletonSmall3998) =
      mixedMoment B node523 node523Labels := by
    have ha : raw614 = raw615 := by apply Matrix.ext; unfold raw614 raw615; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3998 = raw615Labels := by decide +kernel
    rw [ha, hj, canonical615 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall4002 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton4002 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4002 node4002Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node513 node513Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw616 singletonSmall4002
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4002) = raw616Labels := by decide +kernel
  rw [hl, canonical616 B hB] at h
  have hc0 : mixedMoment B raw616 (Fin.cases (0 : Fin 1) singletonSmall4002) =
      mixedMoment B node513 node513Labels := by
    have ha : raw616 = raw617 := by apply Matrix.ext; unfold raw616 raw617; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4002 = raw617Labels := by decide +kernel
    rw [ha, hj, canonical617 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall4003 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton4003 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4003 node4003Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node483 node483Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw618 singletonSmall4003
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4003) = raw618Labels := by decide +kernel
  rw [hl, canonical618 B hB] at h
  have hc0 : mixedMoment B raw618 (Fin.cases (0 : Fin 1) singletonSmall4003) =
      mixedMoment B node483 node483Labels := by
    have ha : raw618 = raw619 := by apply Matrix.ext; unfold raw618 raw619; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4003 = raw619Labels := by decide +kernel
    rw [ha, hj, canonical619 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall4004 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton4004 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4004 node4004Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node516 node516Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw620 singletonSmall4004
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4004) = raw620Labels := by decide +kernel
  rw [hl, canonical620 B hB] at h
  have hc0 : mixedMoment B raw620 (Fin.cases (0 : Fin 1) singletonSmall4004) =
      mixedMoment B node516 node516Labels := by
    have ha : raw620 = raw621 := by apply Matrix.ext; unfold raw620 raw621; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4004 = raw621Labels := by decide +kernel
    rw [ha, hj, canonical621 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall4012 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton4012 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4012 node4012Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node494 node494Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw622 singletonSmall4012
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4012) = raw622Labels := by decide +kernel
  rw [hl, canonical622 B hB] at h
  have hc0 : mixedMoment B raw622 (Fin.cases (0 : Fin 1) singletonSmall4012) =
      mixedMoment B node494 node494Labels := by
    have ha : raw622 = raw623 := by apply Matrix.ext; unfold raw622 raw623; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4012 = raw623Labels := by decide +kernel
    rw [ha, hj, canonical623 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall4013 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton4013 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4013 node4013Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node526 node526Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw624 singletonSmall4013
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4013) = raw624Labels := by decide +kernel
  rw [hl, canonical624 B hB] at h
  have hc0 : mixedMoment B raw624 (Fin.cases (0 : Fin 1) singletonSmall4013) =
      mixedMoment B node526 node526Labels := by
    have ha : raw624 = raw625 := by apply Matrix.ext; unfold raw624 raw625; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4013 = raw625Labels := by decide +kernel
    rw [ha, hj, canonical625 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall4014 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton4014 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4014 node4014Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node527 node527Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw626 singletonSmall4014
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4014) = raw626Labels := by decide +kernel
  rw [hl, canonical626 B hB] at h
  have hc0 : mixedMoment B raw626 (Fin.cases (0 : Fin 1) singletonSmall4014) =
      mixedMoment B node527 node527Labels := by
    have ha : raw626 = raw627 := by apply Matrix.ext; unfold raw626 raw627; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4014 = raw627Labels := by decide +kernel
    rw [ha, hj, canonical627 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall4015 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton4015 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4015 node4015Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node528 node528Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw628 singletonSmall4015
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4015) = raw628Labels := by decide +kernel
  rw [hl, canonical628 B hB] at h
  have hc0 : mixedMoment B raw628 (Fin.cases (0 : Fin 1) singletonSmall4015) =
      mixedMoment B node528 node528Labels := by
    have ha : raw628 = raw629 := by apply Matrix.ext; unfold raw628 raw629; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4015 = raw629Labels := by decide +kernel
    rw [ha, hj, canonical629 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall4017 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton4017 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4017 node4017Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node528 node528Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw630 singletonSmall4017
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4017) = raw630Labels := by decide +kernel
  rw [hl, canonical630 B hB] at h
  have hc0 : mixedMoment B raw630 (Fin.cases (0 : Fin 1) singletonSmall4017) =
      mixedMoment B node528 node528Labels := by
    have ha : raw630 = raw631 := by apply Matrix.ext; unfold raw630 raw631; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4017 = raw631Labels := by decide +kernel
    rw [ha, hj, canonical631 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall4020 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton4020 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4020 node4020Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node530 node530Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw632 singletonSmall4020
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4020) = raw632Labels := by decide +kernel
  rw [hl, canonical632 B hB] at h
  have hc0 : mixedMoment B raw632 (Fin.cases (0 : Fin 1) singletonSmall4020) =
      mixedMoment B node530 node530Labels := by
    have ha : raw632 = raw633 := by apply Matrix.ext; unfold raw632 raw633; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4020 = raw633Labels := by decide +kernel
    rw [ha, hj, canonical633 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall4023 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton4023 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4023 node4023Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node456 node456Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw634 singletonSmall4023
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4023) = raw634Labels := by decide +kernel
  rw [hl, canonical634 B hB] at h
  have hc0 : mixedMoment B raw634 (Fin.cases (0 : Fin 1) singletonSmall4023) =
      mixedMoment B node456 node456Labels := by
    have ha : raw634 = raw635 := by apply Matrix.ext; unfold raw634 raw635; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4023 = raw635Labels := by decide +kernel
    rw [ha, hj, canonical635 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall4026 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton4026 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4026 node4026Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node486 node486Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw636 singletonSmall4026
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4026) = raw636Labels := by decide +kernel
  rw [hl, canonical636 B hB] at h
  have hc0 : mixedMoment B raw636 (Fin.cases (0 : Fin 1) singletonSmall4026) =
      mixedMoment B node486 node486Labels := by
    have ha : raw636 = raw637 := by apply Matrix.ext; unfold raw636 raw637; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4026 = raw637Labels := by decide +kernel
    rw [ha, hj, canonical637 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall4027 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton4027 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4027 node4027Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node487 node487Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw638 singletonSmall4027
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4027) = raw638Labels := by decide +kernel
  rw [hl, canonical638 B hB] at h
  have hc0 : mixedMoment B raw638 (Fin.cases (0 : Fin 1) singletonSmall4027) =
      mixedMoment B node487 node487Labels := by
    have ha : raw638 = raw639 := by apply Matrix.ext; unfold raw638 raw639; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4027 = raw639Labels := by decide +kernel
    rw [ha, hj, canonical639 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall4028 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton4028 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4028 node4028Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node500 node500Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw640 singletonSmall4028
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4028) = raw640Labels := by decide +kernel
  rw [hl, canonical640 B hB] at h
  have hc0 : mixedMoment B raw640 (Fin.cases (0 : Fin 1) singletonSmall4028) =
      mixedMoment B node500 node500Labels := by
    have ha : raw640 = raw641 := by apply Matrix.ext; unfold raw640 raw641; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4028 = raw641Labels := by decide +kernel
    rw [ha, hj, canonical641 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall4029 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton4029 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4029 node4029Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node502 node502Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw642 singletonSmall4029
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4029) = raw642Labels := by decide +kernel
  rw [hl, canonical642 B hB] at h
  have hc0 : mixedMoment B raw642 (Fin.cases (0 : Fin 1) singletonSmall4029) =
      mixedMoment B node502 node502Labels := by
    have ha : raw642 = raw643 := by apply Matrix.ext; unfold raw642 raw643; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4029 = raw643Labels := by decide +kernel
    rw [ha, hj, canonical643 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall4030 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton4030 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4030 node4030Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node501 node501Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw644 singletonSmall4030
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4030) = raw644Labels := by decide +kernel
  rw [hl, canonical644 B hB] at h
  have hc0 : mixedMoment B raw644 (Fin.cases (0 : Fin 1) singletonSmall4030) =
      mixedMoment B node501 node501Labels := by
    have ha : raw644 = raw645 := by apply Matrix.ext; unfold raw644 raw645; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4030 = raw645Labels := by decide +kernel
    rw [ha, hj, canonical645 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall4031 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton4031 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4031 node4031Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node471 node471Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw646 singletonSmall4031
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4031) = raw646Labels := by decide +kernel
  rw [hl, canonical646 B hB] at h
  have hc0 : mixedMoment B raw646 (Fin.cases (0 : Fin 1) singletonSmall4031) =
      mixedMoment B node471 node471Labels := by
    have ha : raw646 = raw647 := by apply Matrix.ext; unfold raw646 raw647; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4031 = raw647Labels := by decide +kernel
    rw [ha, hj, canonical647 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI

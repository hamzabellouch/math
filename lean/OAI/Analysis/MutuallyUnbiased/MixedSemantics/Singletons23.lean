import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical1

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall1472 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1472 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1472 node1472Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node55 node55Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw178 singletonSmall1472
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1472) = raw178Labels := by decide +kernel
  rw [hl, canonical178 B hB] at h
  have hc0 : mixedMoment B raw178 (Fin.cases (0 : Fin 1) singletonSmall1472) =
      mixedMoment B node55 node55Labels := by
    have ha : raw178 = raw179 := by apply Matrix.ext; unfold raw178 raw179; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1472 = raw179Labels := by decide +kernel
    rw [ha, hj, canonical179 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1473 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1473 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1473 node1473Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node56 node56Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw180 singletonSmall1473
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1473) = raw180Labels := by decide +kernel
  rw [hl, canonical180 B hB] at h
  have hc0 : mixedMoment B raw180 (Fin.cases (0 : Fin 1) singletonSmall1473) =
      mixedMoment B node56 node56Labels := by
    have ha : raw180 = raw181 := by apply Matrix.ext; unfold raw180 raw181; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1473 = raw181Labels := by decide +kernel
    rw [ha, hj, canonical181 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1475 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1475 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1475 node1475Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node44 node44Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw182 singletonSmall1475
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1475) = raw182Labels := by decide +kernel
  rw [hl, canonical182 B hB] at h
  have hc0 : mixedMoment B raw182 (Fin.cases (0 : Fin 1) singletonSmall1475) =
      mixedMoment B node44 node44Labels := by
    have ha : raw182 = raw183 := by apply Matrix.ext; unfold raw182 raw183; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1475 = raw183Labels := by decide +kernel
    rw [ha, hj, canonical183 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1476 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1476 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1476 node1476Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node46 node46Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw184 singletonSmall1476
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1476) = raw184Labels := by decide +kernel
  rw [hl, canonical184 B hB] at h
  have hc0 : mixedMoment B raw184 (Fin.cases (0 : Fin 1) singletonSmall1476) =
      mixedMoment B node46 node46Labels := by
    have ha : raw184 = raw185 := by apply Matrix.ext; unfold raw184 raw185; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1476 = raw185Labels := by decide +kernel
    rw [ha, hj, canonical185 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1477 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1477 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1477 node1477Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node43 node43Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw186 singletonSmall1477
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1477) = raw186Labels := by decide +kernel
  rw [hl, canonical186 B hB] at h
  have hc0 : mixedMoment B raw186 (Fin.cases (0 : Fin 1) singletonSmall1477) =
      mixedMoment B node43 node43Labels := by
    have ha : raw186 = raw187 := by apply Matrix.ext; unfold raw186 raw187; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1477 = raw187Labels := by decide +kernel
    rw [ha, hj, canonical187 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1478 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1478 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1478 node1478Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node45 node45Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw188 singletonSmall1478
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1478) = raw188Labels := by decide +kernel
  rw [hl, canonical188 B hB] at h
  have hc0 : mixedMoment B raw188 (Fin.cases (0 : Fin 1) singletonSmall1478) =
      mixedMoment B node45 node45Labels := by
    have ha : raw188 = raw189 := by apply Matrix.ext; unfold raw188 raw189; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1478 = raw189Labels := by decide +kernel
    rw [ha, hj, canonical189 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1479 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1479 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1479 node1479Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node48 node48Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw190 singletonSmall1479
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1479) = raw190Labels := by decide +kernel
  rw [hl, canonical190 B hB] at h
  have hc0 : mixedMoment B raw190 (Fin.cases (0 : Fin 1) singletonSmall1479) =
      mixedMoment B node48 node48Labels := by
    have ha : raw190 = raw191 := by apply Matrix.ext; unfold raw190 raw191; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1479 = raw191Labels := by decide +kernel
    rw [ha, hj, canonical191 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1480 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1480 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1480 node1480Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node50 node50Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw192 singletonSmall1480
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1480) = raw192Labels := by decide +kernel
  rw [hl, canonical192 B hB] at h
  have hc0 : mixedMoment B raw192 (Fin.cases (0 : Fin 1) singletonSmall1480) =
      mixedMoment B node50 node50Labels := by
    have ha : raw192 = raw193 := by apply Matrix.ext; unfold raw192 raw193; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1480 = raw193Labels := by decide +kernel
    rw [ha, hj, canonical193 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1481 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1481 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1481 node1481Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node52 node52Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw194 singletonSmall1481
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1481) = raw194Labels := by decide +kernel
  rw [hl, canonical194 B hB] at h
  have hc0 : mixedMoment B raw194 (Fin.cases (0 : Fin 1) singletonSmall1481) =
      mixedMoment B node52 node52Labels := by
    have ha : raw194 = raw195 := by apply Matrix.ext; unfold raw194 raw195; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1481 = raw195Labels := by decide +kernel
    rw [ha, hj, canonical195 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI

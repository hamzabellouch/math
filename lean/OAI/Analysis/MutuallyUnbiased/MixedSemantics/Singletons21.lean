import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical0

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall1344 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1344 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1344 node1344Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node69 node69Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw106 singletonSmall1344
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1344) = raw106Labels := by decide +kernel
  rw [hl, canonical106 B hB] at h
  have hc0 : mixedMoment B raw106 (Fin.cases (0 : Fin 1) singletonSmall1344) =
      mixedMoment B node69 node69Labels := by
    have ha : raw106 = raw107 := by apply Matrix.ext; unfold raw106 raw107; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1344 = raw107Labels := by decide +kernel
    rw [ha, hj, canonical107 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1346 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1346 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1346 node1346Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node62 node62Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw108 singletonSmall1346
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1346) = raw108Labels := by decide +kernel
  rw [hl, canonical108 B hB] at h
  have hc0 : mixedMoment B raw108 (Fin.cases (0 : Fin 1) singletonSmall1346) =
      mixedMoment B node62 node62Labels := by
    have ha : raw108 = raw109 := by apply Matrix.ext; unfold raw108 raw109; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1346 = raw109Labels := by decide +kernel
    rw [ha, hj, canonical109 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1349 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1349 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1349 node1349Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node71 node71Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw110 singletonSmall1349
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1349) = raw110Labels := by decide +kernel
  rw [hl, canonical110 B hB] at h
  have hc0 : mixedMoment B raw110 (Fin.cases (0 : Fin 1) singletonSmall1349) =
      mixedMoment B node71 node71Labels := by
    have ha : raw110 = raw111 := by apply Matrix.ext; unfold raw110 raw111; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1349 = raw111Labels := by decide +kernel
    rw [ha, hj, canonical111 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1395 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1395 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1395 node1395Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node79 node79Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw112 singletonSmall1395
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1395) = raw112Labels := by decide +kernel
  rw [hl, canonical112 B hB] at h
  have hc0 : mixedMoment B raw112 (Fin.cases (0 : Fin 1) singletonSmall1395) =
      mixedMoment B node79 node79Labels := by
    have ha : raw112 = raw113 := by apply Matrix.ext; unfold raw112 raw113; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1395 = raw113Labels := by decide +kernel
    rw [ha, hj, canonical113 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1396 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1396 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1396 node1396Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node77 node77Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw114 singletonSmall1396
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1396) = raw114Labels := by decide +kernel
  rw [hl, canonical114 B hB] at h
  have hc0 : mixedMoment B raw114 (Fin.cases (0 : Fin 1) singletonSmall1396) =
      mixedMoment B node77 node77Labels := by
    have ha : raw114 = raw115 := by apply Matrix.ext; unfold raw114 raw115; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1396 = raw115Labels := by decide +kernel
    rw [ha, hj, canonical115 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1397 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1397 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1397 node1397Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node80 node80Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw116 singletonSmall1397
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1397) = raw116Labels := by decide +kernel
  rw [hl, canonical116 B hB] at h
  have hc0 : mixedMoment B raw116 (Fin.cases (0 : Fin 1) singletonSmall1397) =
      mixedMoment B node80 node80Labels := by
    have ha : raw116 = raw117 := by apply Matrix.ext; unfold raw116 raw117; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1397 = raw117Labels := by decide +kernel
    rw [ha, hj, canonical117 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1399 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1399 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1399 node1399Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node78 node78Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw118 singletonSmall1399
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1399) = raw118Labels := by decide +kernel
  rw [hl, canonical118 B hB] at h
  have hc0 : mixedMoment B raw118 (Fin.cases (0 : Fin 1) singletonSmall1399) =
      mixedMoment B node78 node78Labels := by
    have ha : raw118 = raw119 := by apply Matrix.ext; unfold raw118 raw119; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1399 = raw119Labels := by decide +kernel
    rw [ha, hj, canonical119 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1401 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1401 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1401 node1401Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node81 node81Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw120 singletonSmall1401
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1401) = raw120Labels := by decide +kernel
  rw [hl, canonical120 B hB] at h
  have hc0 : mixedMoment B raw120 (Fin.cases (0 : Fin 1) singletonSmall1401) =
      mixedMoment B node81 node81Labels := by
    have ha : raw120 = raw121 := by apply Matrix.ext; unfold raw120 raw121; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1401 = raw121Labels := by decide +kernel
    rw [ha, hj, canonical121 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1402 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1402 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1402 node1402Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node82 node82Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw122 singletonSmall1402
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1402) = raw122Labels := by decide +kernel
  rw [hl, canonical122 B hB] at h
  have hc0 : mixedMoment B raw122 (Fin.cases (0 : Fin 1) singletonSmall1402) =
      mixedMoment B node82 node82Labels := by
    have ha : raw122 = raw123 := by apply Matrix.ext; unfold raw122 raw123; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1402 = raw123Labels := by decide +kernel
    rw [ha, hj, canonical123 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI

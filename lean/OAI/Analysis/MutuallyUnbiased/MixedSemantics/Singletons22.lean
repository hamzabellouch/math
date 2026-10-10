import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical1

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall1409 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1409 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1409 node1409Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node91 node91Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw124 singletonSmall1409
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1409) = raw124Labels := by decide +kernel
  rw [hl, canonical124 B hB] at h
  have hc0 : mixedMoment B raw124 (Fin.cases (0 : Fin 1) singletonSmall1409) =
      mixedMoment B node91 node91Labels := by
    have ha : raw124 = raw125 := by apply Matrix.ext; unfold raw124 raw125; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1409 = raw125Labels := by decide +kernel
    rw [ha, hj, canonical125 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1410 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1410 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1410 node1410Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node95 node95Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw126 singletonSmall1410
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1410) = raw126Labels := by decide +kernel
  rw [hl, canonical126 B hB] at h
  have hc0 : mixedMoment B raw126 (Fin.cases (0 : Fin 1) singletonSmall1410) =
      mixedMoment B node95 node95Labels := by
    have ha : raw126 = raw127 := by apply Matrix.ext; unfold raw126 raw127; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1410 = raw127Labels := by decide +kernel
    rw [ha, hj, canonical127 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1411 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1411 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1411 node1411Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node93 node93Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw128 singletonSmall1411
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1411) = raw128Labels := by decide +kernel
  rw [hl, canonical128 B hB] at h
  have hc0 : mixedMoment B raw128 (Fin.cases (0 : Fin 1) singletonSmall1411) =
      mixedMoment B node93 node93Labels := by
    have ha : raw128 = raw129 := by apply Matrix.ext; unfold raw128 raw129; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1411 = raw129Labels := by decide +kernel
    rw [ha, hj, canonical129 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1412 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1412 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1412 node1412Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node89 node89Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw130 singletonSmall1412
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1412) = raw130Labels := by decide +kernel
  rw [hl, canonical130 B hB] at h
  have hc0 : mixedMoment B raw130 (Fin.cases (0 : Fin 1) singletonSmall1412) =
      mixedMoment B node89 node89Labels := by
    have ha : raw130 = raw131 := by apply Matrix.ext; unfold raw130 raw131; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1412 = raw131Labels := by decide +kernel
    rw [ha, hj, canonical131 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1413 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1413 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1413 node1413Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node96 node96Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw132 singletonSmall1413
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1413) = raw132Labels := by decide +kernel
  rw [hl, canonical132 B hB] at h
  have hc0 : mixedMoment B raw132 (Fin.cases (0 : Fin 1) singletonSmall1413) =
      mixedMoment B node96 node96Labels := by
    have ha : raw132 = raw133 := by apply Matrix.ext; unfold raw132 raw133; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1413 = raw133Labels := by decide +kernel
    rw [ha, hj, canonical133 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1414 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1414 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1414 node1414Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node92 node92Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw134 singletonSmall1414
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1414) = raw134Labels := by decide +kernel
  rw [hl, canonical134 B hB] at h
  have hc0 : mixedMoment B raw134 (Fin.cases (0 : Fin 1) singletonSmall1414) =
      mixedMoment B node92 node92Labels := by
    have ha : raw134 = raw135 := by apply Matrix.ext; unfold raw134 raw135; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1414 = raw135Labels := by decide +kernel
    rw [ha, hj, canonical135 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1416 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1416 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1416 node1416Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node94 node94Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw136 singletonSmall1416
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1416) = raw136Labels := by decide +kernel
  rw [hl, canonical136 B hB] at h
  have hc0 : mixedMoment B raw136 (Fin.cases (0 : Fin 1) singletonSmall1416) =
      mixedMoment B node94 node94Labels := by
    have ha : raw136 = raw137 := by apply Matrix.ext; unfold raw136 raw137; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1416 = raw137Labels := by decide +kernel
    rw [ha, hj, canonical137 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1417 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1417 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1417 node1417Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node90 node90Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw138 singletonSmall1417
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1417) = raw138Labels := by decide +kernel
  rw [hl, canonical138 B hB] at h
  have hc0 : mixedMoment B raw138 (Fin.cases (0 : Fin 1) singletonSmall1417) =
      mixedMoment B node90 node90Labels := by
    have ha : raw138 = raw139 := by apply Matrix.ext; unfold raw138 raw139; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1417 = raw139Labels := by decide +kernel
    rw [ha, hj, canonical139 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1419 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1419 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1419 node1419Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node98 node98Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw140 singletonSmall1419
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1419) = raw140Labels := by decide +kernel
  rw [hl, canonical140 B hB] at h
  have hc0 : mixedMoment B raw140 (Fin.cases (0 : Fin 1) singletonSmall1419) =
      mixedMoment B node98 node98Labels := by
    have ha : raw140 = raw141 := by apply Matrix.ext; unfold raw140 raw141; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1419 = raw141Labels := by decide +kernel
    rw [ha, hj, canonical141 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1420 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1420 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1420 node1420Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node99 node99Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw142 singletonSmall1420
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1420) = raw142Labels := by decide +kernel
  rw [hl, canonical142 B hB] at h
  have hc0 : mixedMoment B raw142 (Fin.cases (0 : Fin 1) singletonSmall1420) =
      mixedMoment B node99 node99Labels := by
    have ha : raw142 = raw143 := by apply Matrix.ext; unfold raw142 raw143; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1420 = raw143Labels := by decide +kernel
    rw [ha, hj, canonical143 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1426 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1426 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1426 node1426Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node84 node84Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw144 singletonSmall1426
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1426) = raw144Labels := by decide +kernel
  rw [hl, canonical144 B hB] at h
  have hc0 : mixedMoment B raw144 (Fin.cases (0 : Fin 1) singletonSmall1426) =
      mixedMoment B node84 node84Labels := by
    have ha : raw144 = raw145 := by apply Matrix.ext; unfold raw144 raw145; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1426 = raw145Labels := by decide +kernel
    rw [ha, hj, canonical145 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1427 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1427 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1427 node1427Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node83 node83Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw146 singletonSmall1427
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1427) = raw146Labels := by decide +kernel
  rw [hl, canonical146 B hB] at h
  have hc0 : mixedMoment B raw146 (Fin.cases (0 : Fin 1) singletonSmall1427) =
      mixedMoment B node83 node83Labels := by
    have ha : raw146 = raw147 := by apply Matrix.ext; unfold raw146 raw147; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1427 = raw147Labels := by decide +kernel
    rw [ha, hj, canonical147 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1429 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1429 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1429 node1429Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node85 node85Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw148 singletonSmall1429
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1429) = raw148Labels := by decide +kernel
  rw [hl, canonical148 B hB] at h
  have hc0 : mixedMoment B raw148 (Fin.cases (0 : Fin 1) singletonSmall1429) =
      mixedMoment B node85 node85Labels := by
    have ha : raw148 = raw149 := by apply Matrix.ext; unfold raw148 raw149; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1429 = raw149Labels := by decide +kernel
    rw [ha, hj, canonical149 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1430 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1430 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1430 node1430Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node86 node86Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw150 singletonSmall1430
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1430) = raw150Labels := by decide +kernel
  rw [hl, canonical150 B hB] at h
  have hc0 : mixedMoment B raw150 (Fin.cases (0 : Fin 1) singletonSmall1430) =
      mixedMoment B node86 node86Labels := by
    have ha : raw150 = raw151 := by apply Matrix.ext; unfold raw150 raw151; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1430 = raw151Labels := by decide +kernel
    rw [ha, hj, canonical151 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1441 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1441 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1441 node1441Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node108 node108Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw152 singletonSmall1441
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1441) = raw152Labels := by decide +kernel
  rw [hl, canonical152 B hB] at h
  have hc0 : mixedMoment B raw152 (Fin.cases (0 : Fin 1) singletonSmall1441) =
      mixedMoment B node108 node108Labels := by
    have ha : raw152 = raw153 := by apply Matrix.ext; unfold raw152 raw153; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1441 = raw153Labels := by decide +kernel
    rw [ha, hj, canonical153 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1442 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1442 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1442 node1442Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node111 node111Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw154 singletonSmall1442
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1442) = raw154Labels := by decide +kernel
  rw [hl, canonical154 B hB] at h
  have hc0 : mixedMoment B raw154 (Fin.cases (0 : Fin 1) singletonSmall1442) =
      mixedMoment B node111 node111Labels := by
    have ha : raw154 = raw155 := by apply Matrix.ext; unfold raw154 raw155; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1442 = raw155Labels := by decide +kernel
    rw [ha, hj, canonical155 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1443 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1443 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1443 node1443Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node110 node110Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw156 singletonSmall1443
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1443) = raw156Labels := by decide +kernel
  rw [hl, canonical156 B hB] at h
  have hc0 : mixedMoment B raw156 (Fin.cases (0 : Fin 1) singletonSmall1443) =
      mixedMoment B node110 node110Labels := by
    have ha : raw156 = raw157 := by apply Matrix.ext; unfold raw156 raw157; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1443 = raw157Labels := by decide +kernel
    rw [ha, hj, canonical157 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1444 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1444 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1444 node1444Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node106 node106Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw158 singletonSmall1444
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1444) = raw158Labels := by decide +kernel
  rw [hl, canonical158 B hB] at h
  have hc0 : mixedMoment B raw158 (Fin.cases (0 : Fin 1) singletonSmall1444) =
      mixedMoment B node106 node106Labels := by
    have ha : raw158 = raw159 := by apply Matrix.ext; unfold raw158 raw159; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1444 = raw159Labels := by decide +kernel
    rw [ha, hj, canonical159 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1445 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1445 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1445 node1445Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node112 node112Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw160 singletonSmall1445
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1445) = raw160Labels := by decide +kernel
  rw [hl, canonical160 B hB] at h
  have hc0 : mixedMoment B raw160 (Fin.cases (0 : Fin 1) singletonSmall1445) =
      mixedMoment B node112 node112Labels := by
    have ha : raw160 = raw161 := by apply Matrix.ext; unfold raw160 raw161; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1445 = raw161Labels := by decide +kernel
    rw [ha, hj, canonical161 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1449 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1449 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1449 node1449Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node105 node105Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw162 singletonSmall1449
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1449) = raw162Labels := by decide +kernel
  rw [hl, canonical162 B hB] at h
  have hc0 : mixedMoment B raw162 (Fin.cases (0 : Fin 1) singletonSmall1449) =
      mixedMoment B node105 node105Labels := by
    have ha : raw162 = raw163 := by apply Matrix.ext; unfold raw162 raw163; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1449 = raw163Labels := by decide +kernel
    rw [ha, hj, canonical163 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1451 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1451 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1451 node1451Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node109 node109Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw164 singletonSmall1451
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1451) = raw164Labels := by decide +kernel
  rw [hl, canonical164 B hB] at h
  have hc0 : mixedMoment B raw164 (Fin.cases (0 : Fin 1) singletonSmall1451) =
      mixedMoment B node109 node109Labels := by
    have ha : raw164 = raw165 := by apply Matrix.ext; unfold raw164 raw165; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1451 = raw165Labels := by decide +kernel
    rw [ha, hj, canonical165 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1453 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1453 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1453 node1453Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node107 node107Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw166 singletonSmall1453
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1453) = raw166Labels := by decide +kernel
  rw [hl, canonical166 B hB] at h
  have hc0 : mixedMoment B raw166 (Fin.cases (0 : Fin 1) singletonSmall1453) =
      mixedMoment B node107 node107Labels := by
    have ha : raw166 = raw167 := by apply Matrix.ext; unfold raw166 raw167; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1453 = raw167Labels := by decide +kernel
    rw [ha, hj, canonical167 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1454 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1454 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1454 node1454Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node113 node113Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw168 singletonSmall1454
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1454) = raw168Labels := by decide +kernel
  rw [hl, canonical168 B hB] at h
  have hc0 : mixedMoment B raw168 (Fin.cases (0 : Fin 1) singletonSmall1454) =
      mixedMoment B node113 node113Labels := by
    have ha : raw168 = raw169 := by apply Matrix.ext; unfold raw168 raw169; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1454 = raw169Labels := by decide +kernel
    rw [ha, hj, canonical169 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1468 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1468 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1468 node1468Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node51 node51Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw170 singletonSmall1468
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1468) = raw170Labels := by decide +kernel
  rw [hl, canonical170 B hB] at h
  have hc0 : mixedMoment B raw170 (Fin.cases (0 : Fin 1) singletonSmall1468) =
      mixedMoment B node51 node51Labels := by
    have ha : raw170 = raw171 := by apply Matrix.ext; unfold raw170 raw171; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1468 = raw171Labels := by decide +kernel
    rw [ha, hj, canonical171 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1469 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1469 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1469 node1469Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node54 node54Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw172 singletonSmall1469
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1469) = raw172Labels := by decide +kernel
  rw [hl, canonical172 B hB] at h
  have hc0 : mixedMoment B raw172 (Fin.cases (0 : Fin 1) singletonSmall1469) =
      mixedMoment B node54 node54Labels := by
    have ha : raw172 = raw173 := by apply Matrix.ext; unfold raw172 raw173; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1469 = raw173Labels := by decide +kernel
    rw [ha, hj, canonical173 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1470 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1470 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1470 node1470Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node47 node47Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw174 singletonSmall1470
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1470) = raw174Labels := by decide +kernel
  rw [hl, canonical174 B hB] at h
  have hc0 : mixedMoment B raw174 (Fin.cases (0 : Fin 1) singletonSmall1470) =
      mixedMoment B node47 node47Labels := by
    have ha : raw174 = raw175 := by apply Matrix.ext; unfold raw174 raw175; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1470 = raw175Labels := by decide +kernel
    rw [ha, hj, canonical175 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall1471 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton1471 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1471 node1471Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node53 node53Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw176 singletonSmall1471
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1471) = raw176Labels := by decide +kernel
  rw [hl, canonical176 B hB] at h
  have hc0 : mixedMoment B raw176 (Fin.cases (0 : Fin 1) singletonSmall1471) =
      mixedMoment B node53 node53Labels := by
    have ha : raw176 = raw177 := by apply Matrix.ext; unfold raw176 raw177; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1471 = raw177Labels := by decide +kernel
    rw [ha, hj, canonical177 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI

import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical2

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall2828 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2828 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2828 node2828Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node273 node273Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw286 singletonSmall2828
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2828) = raw286Labels := by decide +kernel
  rw [hl, canonical286 B hB] at h
  have hc0 : mixedMoment B raw286 (Fin.cases (0 : Fin 1) singletonSmall2828) =
      mixedMoment B node273 node273Labels := by
    have ha : raw286 = raw287 := by apply Matrix.ext; unfold raw286 raw287; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2828 = raw287Labels := by decide +kernel
    rw [ha, hj, canonical287 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2829 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2829 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2829 node2829Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node275 node275Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw288 singletonSmall2829
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2829) = raw288Labels := by decide +kernel
  rw [hl, canonical288 B hB] at h
  have hc0 : mixedMoment B raw288 (Fin.cases (0 : Fin 1) singletonSmall2829) =
      mixedMoment B node275 node275Labels := by
    have ha : raw288 = raw289 := by apply Matrix.ext; unfold raw288 raw289; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2829 = raw289Labels := by decide +kernel
    rw [ha, hj, canonical289 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2830 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2830 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2830 node2830Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node276 node276Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw290 singletonSmall2830
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2830) = raw290Labels := by decide +kernel
  rw [hl, canonical290 B hB] at h
  have hc0 : mixedMoment B raw290 (Fin.cases (0 : Fin 1) singletonSmall2830) =
      mixedMoment B node276 node276Labels := by
    have ha : raw290 = raw291 := by apply Matrix.ext; unfold raw290 raw291; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2830 = raw291Labels := by decide +kernel
    rw [ha, hj, canonical291 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

def singletonSmall2832 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton2832 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2832 node2832Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node186 node186Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw292 singletonSmall2832
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2832) = raw292Labels := by decide +kernel
  rw [hl, canonical292 B hB] at h
  have hc0 : mixedMoment B raw292 (Fin.cases (0 : Fin 1) singletonSmall2832) =
      mixedMoment B node186 node186Labels := by
    have ha : raw292 = raw293 := by apply Matrix.ext; unfold raw292 raw293; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2832 = raw293Labels := by decide +kernel
    rw [ha, hj, canonical293 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI

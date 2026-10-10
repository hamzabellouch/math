import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical3

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall3711 : Fin 2 → Fin 1 := ![0, 0]

theorem singleton3711 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3711 node3711Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node424 node424Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw480 singletonSmall3711
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3711) = raw480Labels := by decide +kernel
  rw [hl, canonical480 B hB] at h
  have hc0 : mixedMoment B raw480 (Fin.cases (0 : Fin 1) singletonSmall3711) =
      mixedMoment B node424 node424Labels := by
    have ha : raw480 = raw481 := by apply Matrix.ext; unfold raw480 raw481; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3711 = raw481Labels := by decide +kernel
    rw [ha, hj, canonical481 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI

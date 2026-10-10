import OAI.Analysis.MarkovType.MarkedLetters

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {S E : Type*} [Fintype S] [Fintype E]

theorem sum_stationaryEdgeMass (C : FiniteMarkedChain S E) :
    ∑ e, C.π (C.src e) * C.q e = 1 := by
  have h := markedExpect_last_edge C 0 (fun _ => (1 : ℝ))
  simpa only [markedExpect_const, mul_one] using h.symm

theorem stationaryEdgeCost_eq_one {V : Type*} [NormedAddCommGroup V]
    (C : FiniteMarkedChain S E) (g : E → V) (p : ℝ) (hg : ∀ e, ‖g e‖ = 1) :
    stationaryEdgeCost C g p = 1 := by
  have hp : Real.rpow 1 p = 1 := Real.one_rpow p
  simp only [stationaryEdgeCost, hg, hp, mul_one]
  exact sum_stationaryEdgeMass C

end MarkovSuperreflexivity

end

end OAI

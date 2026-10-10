import OAI.NumberTheory.TwoPoint.Circuits.CircuitDyadicComparison
import OAI.NumberTheory.TwoPoint.Circuits.CircuitLogarithmicBudget

namespace OAI

/-! Braverman’s bounded-independence theorem at depth twenty-two follows
from finite circuit approximation and switching estimates. -/

namespace TwoPointCorrelations

theorem bravermanDepth22Input : BravermanDepth22Input := by
  obtain ⟨K, C, hK, hC, hbudget⟩ := bravermanDegree_logarithmic_budget
  refine ⟨K, C, hK, hC, ?_⟩
  intro n c hc ε hε hεhalf t ht g hg hmean hwise
  obtain ⟨j, hmj, hεj, htj⟩ := hbudget c.size c.size_pos ε hε hεhalf t ht
  exact (c.dyadic_comparison hc hmj htj g hg hmean hwise).trans hεj

end TwoPointCorrelations

end OAI

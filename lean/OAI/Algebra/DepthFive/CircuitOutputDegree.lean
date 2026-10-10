import OAI.Algebra.DepthFive.Homogeneity
import OAI.Algebra.DepthFive.ImmDegree

namespace OAI

noncomputable section

namespace Problem335

/-- A nonzero IMM output forces the assigned syntactic output degree to be the layer count. -/
theorem outputDegree_eq_of_circuitValue_eq_imm {K : Type*} [CommSemiring K]
    [Nontrivial K] {n : ℕ} (hn : 0 < n) (c : Depth5Circuit K n)
    (hc : circuitValue c = imm K n) : c.outputDegree = n := by
  have hh := circuitValue_isHomogeneous c
  rw [hc] at hh
  exact hh.inj_right (imm_isHomogeneous K n) (imm_ne_zero K n hn)

/-- Every upper product contributing to an IMM circuit has formal degree `n`. -/
theorem upper_degree_eq_of_circuitValue_eq_imm {K : Type*} [CommSemiring K]
    [Nontrivial K] {n : ℕ} (hn : 0 < n) (c : Depth5Circuit K n)
    (hc : circuitValue c = imm K n) (entry : K × Fin c.upperCount)
    (he : entry ∈ c.outputInputs) :
    ((c.upperInputs entry.2).map c.middleDegree).sum = n := by
  rw [c.outputHomogeneous entry he, outputDegree_eq_of_circuitValue_eq_imm hn c hc]

/-- Nonzero IMM cannot be computed by an empty output sum. -/
theorem outputInputs_ne_nil_of_circuitValue_eq_imm {K : Type*} [CommSemiring K]
    [Nontrivial K] {n : ℕ} (hn : 0 < n) (c : Depth5Circuit K n)
    (hc : circuitValue c = imm K n) : c.outputInputs ≠ [] := by
  intro he
  have hdeg := c.outputEmpty he
  rw [outputDegree_eq_of_circuitValue_eq_imm hn c hc] at hdeg
  omega

end Problem335

end

end OAI

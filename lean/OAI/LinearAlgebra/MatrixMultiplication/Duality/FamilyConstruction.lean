import OAI.LinearAlgebra.MatrixMultiplication.Duality.ExponentConsumer
import OAI.LinearAlgebra.MatrixMultiplication.Duality.FiniteRates
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ConditionalContinuity

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualFiniteRealization

open MatrixMultiplication.Foundation CompletionHierarchyWords Filter
open scoped BigOperators Topology Classical

variable {A X Y Z : Type} [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
variable (H : ReadableHierarchy A X Y Z) (counts : A → ℕ)
variable (hD : 0 < ∑ a, counts a)
variable (complete : Function.Injective (labelRecordOf H.labels H.depth))
variable (p : FiniteLaw A)
variable (mass : ∀ a, p.mass a = (counts a : ℝ) / (∑ b, counts b : ℕ))
variable {T : Tensor ℂ X Y Z} {R d D : ℕ}
variable (source : Tensor.PolynomialApproximation T R d D) (hR : 0 < R)
variable (supported : ∀ x y z, T x y z ≠ 0 →
  ∃ a, H.x a = x ∧ H.y a = y ∧ H.z a = z)
variable (unit : ∀ a, T (H.x a) (H.y a) (H.z a) = 1)

def actualFamily {k budget : ℝ}
    (positive : 0 < pairRate H p .xy + pairRate H p .xz)
    (aspect : k * (pairRate H p .xy + pairRate H p .xz) < 2 * pairRate H p .yz)
    (cost : 2 * Real.log R ≤ budget * (pairRate H p .xy + pairRate H p .xz)) :
    DualExponentBound.ActualFamily k budget where
  witness := fun t => witness H counts t complete source hR supported unit
  scale := fun t => (t : ℝ) * (∑ a, counts a : ℕ)
  outerRate := pairRate H p .xy + pairRate H p .xz
  innerRate := 2 * pairRate H p .yz
  multiplicityRate := 2 * finiteEntropy p.mass
  rankRate := 2 * (Real.log R + finiteEntropy p.mass)
  scale_positive := by
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with t ht
    exact mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero ht)) (Nat.cast_pos.mpr hD)
  outer_positive := positive
  outer_limit := witness_outer_limit H counts hD complete p mass source hR supported unit
  inner_limit := witness_inner_limit H counts hD complete p mass source hR supported unit
  multiplicity_limit := witness_multiplicity_limit H counts hD complete p mass source hR supported unit
  rank_limit := witness_rank_limit H counts hD complete p mass source hR supported unit
  aspect_gap := aspect
  cost_bound := by simpa only [mul_add, add_sub_cancel_right] using cost

include complete source hR supported unit in

theorem arbitrarily_close_families_of_exact_incident {k : ℝ}
    (log_positive : 0 < Real.log R)
    (incident : pairRate H p .xy + pairRate H p .xz = Real.log R)
    (aspect : k * (pairRate H p .xy + pairRate H p .xz) < 2 * pairRate H p .yz) :
    ∀ ε : ℝ, 0 < ε → Nonempty (DualExponentBound.ActualFamily k (2 + ε)) := by
  intro ε hε
  have positive : 0 < pairRate H p .xy + pairRate H p .xz := by
    rw [incident]
    exact log_positive
  have cost : 2 * Real.log R < (2 + ε) * (pairRate H p .xy + pairRate H p .xz) := by
    rw [incident]
    nlinarith
  obtain ⟨q, hpositive, haspect, hcost⟩ :=
    ConditionalLabels.exists_rational_with_strict_margins p H.labels H.depth
      (fun n => H.pair n.val) positive aspect cost
  obtain ⟨population, hpopulation, hmass⟩ := q.exists_type_representation
  refine ⟨actualFamily H population hpopulation complete q.toFiniteLaw ?_
    source hR supported unit hpositive haspect hcost.le⟩
  intro a
  exact (hmass a).symm

end MatrixMultiplication.DualFiniteRealization

end

end OAI

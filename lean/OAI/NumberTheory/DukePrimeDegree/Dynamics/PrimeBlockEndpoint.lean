import OAI.NumberTheory.DukePrimeDegree.Dynamics.PrimeBlockRationality

namespace OAI

/-!
# Prime-degree block rigidity

Real-span rationality of the block centralizer forces a nontrivial block
partition in prime degree to be the universal partition.
-/

noncomputable section
open Matrix Module Set
open scoped Classical

namespace DukePrimeDegree
open PrimeDegreePackets

/-- The real span of the rational block centralizer in lattice coordinates. -/
def rationalBlockRealSpan {n : ℕ} (g : G n) (r : Setoid (Fin n)) :
    Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ (Set.range (fun a : rationalBlockStabilizer g r => a.val))

/-- If the rational block centralizer consists only of scalars, every
function in its real span has equal coordinate values. -/
theorem coordinate_eq_of_mem_rationalBlockRealSpan {n : ℕ}
    (g : G n) (r : Setoid (Fin n))
    (hbot : rationalBlockStabilizer g r = ⊥)
    {v : Fin n → ℝ} (hv : v ∈ rationalBlockRealSpan g r) (i j : Fin n) :
    v i = v j := by
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj j
  have hsub : rationalBlockRealSpan g r ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    have ha : a.val ∈ (⊥ : Subalgebra ℚ (Fin n → ℝ)) := by
      rw [← hbot]
      exact a.property
    obtain ⟨q, hq⟩ := Algebra.mem_bot.mp ha
    change a.val i - a.val j = 0
    rw [← hq]
    simp
  have he := hsub hv
  change v i - v j = 0 at he
  exact sub_eq_zero.mp he

/-- Prime dimension and real-span rationality force a nontrivial root
partition to have a single block. The premise refers to the concrete
intersection of the rational lattice stabilizer and block centralizer. -/
theorem root_partition_universal_of_rational_span {n : ℕ}
    (hn : n.Prime) (g : G n)
    (hzero : ∀ v ∈ rowLattice g.val, v ≠ 0 → ∀ j, v j ≠ 0)
    (r : Setoid (Fin n)) (hblock : ∃ i j, i ≠ j ∧ r i j)
    (hspan : ∀ c ∈ blockCoordinateAlgebra r, c ∈ rationalBlockRealSpan g r) :
    ∀ i j, r i j := by
  have hbot := rationalBlockStabilizer_eq_bot hn g hzero r hblock
  intro i j
  by_contra hij
  let c : Fin n → ℝ := fun k => if Quotient.mk r k = Quotient.mk r i then 1 else 0
  have hc : c ∈ blockCoordinateAlgebra r := by
    intro k l hkl
    change (if Quotient.mk r k = Quotient.mk r i then (1 : ℝ) else 0) =
      (if Quotient.mk r l = Quotient.mk r i then 1 else 0)
    rw [Quotient.sound hkl]
  have hq : Quotient.mk r j ≠ Quotient.mk r i := by
    intro he
    exact hij (r.symm (Quotient.exact he))
  have he := coordinate_eq_of_mem_rationalBlockRealSpan g r hbot (hspan c hc) i j
  simp [c, hq] at he

end DukePrimeDegree

end

end OAI

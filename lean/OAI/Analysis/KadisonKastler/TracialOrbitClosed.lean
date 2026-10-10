import OAI.Analysis.FactorGeneration.Expectations
import OAI.Analysis.FactorGeneration.HilbertLimits

namespace OAI

/-! # Bounded tracial vectors in a subalgebra orbit closure

The constructed conditional expectation shows that a bounded algebra
element whose trace vector belongs to the subalgebra's closed orbit
already belongs to that subalgebra.
-/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial UltrapowerBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M R : VonNeumannAlgebra H}

theorem mem_subalgebra_of_tracial_vector_mem_orbitClosure
    (τ : TracialRepresentation M) (hRM : R ≤ M) (a : M.toStarSubalgebra)
    (ha : a.val τ.vector ∈ vectorOrbitClosure R.toStarSubalgebra τ.vector) :
    a.val ∈ R := by
  let c := conditionalExpectation τ hRM a
  have hc : c.val ∈ R := conditionalExpectation_mem τ hRM a
  let ξ := (a - c).val τ.vector
  have hξ : ξ ∈ vectorOrbitClosure R.toStarSubalgebra τ.vector := by
    change a.val τ.vector - c.val τ.vector ∈ _
    exact (vectorOrbitClosure R.toStarSubalgebra τ.vector).sub_mem ha
      (Submodule.le_topologicalClosure _ ⟨⟨c.val, hc⟩, rfl⟩)
  have ho (r : R.toStarSubalgebra) : inner ℂ (r.val τ.vector) ξ = 0 := by
    have ht := conditionalExpectation_orthogonal τ hRM a
      ⟨star (coordinateInclusion hRM r), star_mem r.property⟩
    change inner ℂ τ.vector ((star r.val * (a - c).val) τ.vector) = 0 at ht
    simpa only [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right] using ht
  have hz : inner ℂ ξ ξ = 0 := by
    have hclosed : IsClosed {x : H | inner ℂ x ξ = 0} :=
      isClosed_eq (continuous_id.inner continuous_const) continuous_const
    have hs : closure (Set.range (fun r : R.toStarSubalgebra => r.val τ.vector)) ⊆
        {x : H | inner ℂ x ξ = 0} :=
      closure_minimal (by rintro _ ⟨r, rfl⟩; exact ho r) hclosed
    exact hs hξ
  have hzero : ξ = 0 := inner_self_eq_zero.mp hz
  have hac : a = c := sub_eq_zero.mp (τ.separating (a - c) hzero)
  simpa only [hac] using hc

end

end KadisonKastler

end OAI

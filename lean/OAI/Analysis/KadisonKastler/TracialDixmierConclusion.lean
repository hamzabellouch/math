import OAI.Analysis.KadisonKastler.FiniteTracialAveraging

namespace OAI

/-! # The exact Dixmier conclusion for diffuse tracial factors -/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] {M : VonNeumannAlgebra H}

omit [Nontrivial H] in
theorem FiniteInnerAverage.trace_algebraApply (A : FiniteInnerAverage M)
    (τ : TracialRepresentation M) (x : Algebra M) :
    τ.trace (A.algebraApply x) = τ.trace x := by
  have ht (i : A.Index) :
      τ.trace ((A.unitary i : Algebra M) * x * star (A.unitary i : Algebra M)) = τ.trace x := by
    rw [τ.trace_mul_comm, ← mul_assoc, Unitary.star_mul_self_of_mem (A.unitary i).property,
      one_mul]
  let L := coordinateTraceLinear τ
  change L ((Fintype.card A.Index : ℂ)⁻¹ •
    ∑ i, (A.unitary i : Algebra M) * x * star (A.unitary i : Algebra M)) = τ.trace x
  rw [L.map_smul, map_sum]
  change (Fintype.card A.Index : ℂ)⁻¹ •
    (∑ i, τ.trace ((A.unitary i : Algebra M) * x * star (A.unitary i : Algebra M))) = _
  simp only [ht]
  exact finiteAverage_const (G := A.Index) _

omit [Nontrivial H] in
theorem FiniteInnerAverage.trace_error_le (A : FiniteInnerAverage M)
    (τ : TracialRepresentation M) (x : Algebra M) (z : ℂ) :
    ‖τ.trace x - z‖ ≤ ‖A.apply x.val - z • (1 : H →L[ℂ] H)‖ := by
  have h := (τ.norm_trace_le_norm₂ (A.algebraApply x - z • (1 : Algebra M))).trans
    (τ.norm₂_le_norm _)
  rw [trace_sub, A.trace_algebraApply, cornerTrace_smul, τ.trace_one, mul_one] at h
  have he : ‖A.algebraApply x - z • (1 : Algebra M)‖ =
      ‖A.apply x.val - z • (1 : H →L[ℂ] H)‖ := by
    change ‖(A.algebraApply x).val - z • (1 : H →L[ℂ] H)‖ = _
    rw [A.algebraApply_val]
  exact he ▸ h

/-- The scalar of the norm-closed orbit hull is exactly the represented trace. -/
theorem trace_scalar_mem_norm_orbitHull (τ : TracialRepresentation M)
    (hfactor : ∀ c : Algebra M, (∀ a : Algebra M, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra M))
    (hdiff : ∀ p : Algebra M, IsStarProjection p → p ≠ 0 →
      ∃ q : Algebra M, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (x : Algebra M) :
    τ.trace x • (1 : H →L[ℂ] H) ∈ closure (convexHull ℝ (innerUnitaryOrbit M x.val)) := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨A, z, hA⟩ := exists_tracial_scalar_average τ hfactor hdiff x (ε / 2) (by positivity)
  have hz := A.trace_error_le τ x z
  have hscalar : ‖z • (1 : H →L[ℂ] H) - τ.trace x • 1‖ = ‖τ.trace x - z‖ := by
    rw [← sub_smul, norm_smul, norm_one, mul_one, norm_sub_rev]
  refine ⟨A.apply x.val, A.apply_mem_orbitHull x.val, ?_⟩
  have hb := norm_sub_le_norm_sub_add_norm_sub (A.apply x.val)
    (z • (1 : H →L[ℂ] H)) (τ.trace x • (1 : H →L[ℂ] H))
  rw [hscalar] at hb
  rw [dist_eq_norm, norm_sub_rev]
  linarith

/-- Finite inner averages of a represented diffuse finite factor approximate
scalars, using its faithful tracial vector. -/
theorem publishedDixmierOfTracialFactor (τ : TracialRepresentation M)
    (hfactor : ∀ c : Algebra M, (∀ a : Algebra M, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra M))
    (hdiff : ∀ p : Algebra M, IsStarProjection p → p ≠ 0 →
      ∃ q : Algebra M, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q) :
    PublishedDixmierAveraging M := by
  intro x hx
  let a : Algebra M := ⟨x, hx.1⟩
  refine ⟨τ.trace a • (1 : H →L[ℂ] H), ?_, trace_scalar_mem_norm_orbitHull τ hfactor hdiff a⟩
  exact (concreteCenter M).toStarSubalgebra.smul_mem (concreteCenter M).one_mem _

end

end KadisonKastler

end OAI

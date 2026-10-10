import OAI.Analysis.KadisonKastler.CentralVectorSupport

namespace OAI

/-! # A central line detects scalars on its support corner -/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem scalar_on_support_of_central_line
    (A : ℕ → FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : ξ ∈ matrixCentralVectorSpace A J)
    (hline : matrixCentralVectorSpace A J ≤ Submodule.span ℂ {ξ})
    (a : Algebra M) (ha : a * (vectorSupportProjection M ξ).val = a)
    (hcomm : ∀ n i j, (A n).units.entry i j * a = a * (A n).units.entry i j) :
    ∃ z : ℂ, a = z • (vectorSupportProjection M ξ).val := by
  have hax : a.val ξ ∈ matrixCentralVectorSpace A J := by
    apply (Submodule.mem_iInf _).mpr
    intro n
    apply centralVectorSpace_invariant J
      (fun b => hright (coordinateInclusion (matrixUnitConcreteAlgebra_le (A n).units) (star b)))
      a.val a.property
    · intro b
      let b' := coordinateInclusion (matrixUnitConcreteAlgebra_le (A n).units) b
      have hb' : b' ∈ (A n).units.algebra :=
        ((A n).units.mem_concreteAlgebra b').mp b.property
      have hc := ((A n).units.commute_algebra_iff a).mpr (fun i j => hcomm n i j) b' hb'
      exact congrArg (fun c : Algebra M => c.val) hc.eq
    · exact matrixCentralVectorSpace_le A J n hξ
  obtain ⟨z,hz⟩ := Submodule.mem_span_singleton.mp (hline hax)
  refine ⟨z, ?_⟩
  have hzero : a - z • (vectorSupportProjection M ξ).val = 0 := by
    apply vectorSupport_faithful_corner M ξ
    · change ((a - z • (vectorSupportProjection M ξ).val) *
        (vectorSupportProjection M ξ).val).val = (a - z • (vectorSupportProjection M ξ).val).val
      rw [sub_mul,smul_mul_assoc,ha,(vectorSupportProjection M ξ).property.isIdempotentElem.eq]
    · change a.val ξ - z • ((vectorSupportProjection M ξ).val.val ξ) = 0
      rw [vectorSupportProjection_apply,← hz,sub_self]
  exact sub_eq_zero.mp hzero

end

end KadisonKastler

end OAI

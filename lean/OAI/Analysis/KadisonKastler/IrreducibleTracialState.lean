import OAI.Analysis.KadisonKastler.RelativeNormalFunctional
import OAI.Analysis.KadisonKastler.ConcreteTraceHilbert
import OAI.Analysis.KadisonKastler.StandardTracialPosition
import OAI.Analysis.FactorGeneration.TraceTransport

namespace OAI

/-! # Relative centrality determines the vector trace of a finite factor -/

namespace KadisonKastler

noncomputable section

open Generator.Tracial UltrapowerBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Commuting right representatives of the common algebra make the
vector state central over that algebra. -/
theorem vector_state_central_of_commuting_right_representatives
    (M R : VonNeumannAlgebra H) (hRM : R ≤ M) (ξ : H)
    (hright : ∀ r : Algebra R, ∃ b : H →L[ℂ] H,
      b ∈ M.commutant ∧ b ξ = r.val ξ ∧ star b ξ = star r.val ξ)
    (r : Algebra R) (a : Algebra M) :
    inner ℂ ξ ((coordinateInclusion hRM r * a).val ξ) =
      inner ℂ ξ ((a * coordinateInclusion hRM r).val ξ) := by
  obtain ⟨b, hb, hbr, hbstar⟩ := hright r
  have hcomm : a.val * b = b * a.val :=
    VonNeumannAlgebra.mem_commutant_iff.mp hb a.val a.property
  change inner ℂ ξ (r.val (a.val ξ)) = inner ℂ ξ (a.val (r.val ξ))
  calc
    inner ℂ ξ (r.val (a.val ξ)) = inner ℂ (star r.val ξ) (a.val ξ) := by
      simpa only [ContinuousLinearMap.star_eq_adjoint] using
        (ContinuousLinearMap.adjoint_inner_left r.val (a.val ξ) ξ).symm
    _ = inner ℂ (star b ξ) (a.val ξ) := by rw [hbstar]
    _ = inner ℂ ξ (b (a.val ξ)) := by
      simpa only [ContinuousLinearMap.star_eq_adjoint] using
        ContinuousLinearMap.adjoint_inner_left b (a.val ξ) ξ
    _ = inner ℂ ξ (a.val (b ξ)) := by
      have he := congrArg (fun T : H →L[ℂ] H => T ξ) hcomm
      exact congrArg (fun v : H => inner ℂ ξ v) he.symm
    _ = inner ℂ ξ (a.val (r.val ξ)) := by rw [hbr]

theorem ii1_vector_state_eq_trace_of_relative_central
    (M R : VonNeumannAlgebra H) (hRM : R ≤ M)
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hirr : ∀ a : Algebra M, a.val ∈ R.commutant → ∃ c : ℂ, a = c • 1)
    (ξ : H) (hξ : ‖ξ‖ = 1)
    (hcentral : ∀ (r : Algebra R) (a : Algebra M),
      inner ℂ ξ ((coordinateInclusion hRM r * a).val ξ) =
      inner ℂ ξ ((a * coordinateInclusion hRM r).val ξ))
    (x : Algebra M) : inner ℂ ξ (x.val ξ) = (concreteFactorTrace hM).toLinearMap x := by
  let hf := traceHilbert_factor hM
  let hu := traceHilbert_nonzero hM
  let P := traceFreeHilbertClosure hf hM.diffuse hM.finite hu
  let e := traceFreeHilbertEquiv hf hM.diffuse hM.finite hu
  let τ : TracialRepresentation P := traceFreeHilbertClosureTrace hf hM.diffuse hM.finite hu
  calc
    inner ℂ ξ (x.val ξ) = τ.trace (e x) :=
      vector_state_eq_trace_of_relative_central M R hRM P e τ
        (traceFreeHilbertBallMap_continuous hf hM.diffuse hM.finite hu)
        hirr ξ hξ hcentral x
    _ = (concreteFactorTrace hM).toLinearMap x :=
      traceFreeHilbertClosureTrace_copy hf hM.diffuse hM.finite hu x

/-- Once cyclicity is known, relative centrality supplies all remaining
standard tracial position data. -/
def standardTracialPosition_of_relative_central
    (M R : VonNeumannAlgebra H) (hRM : R ≤ M)
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hirr : ∀ a : Algebra M, a.val ∈ R.commutant → ∃ c : ℂ, a = c • 1)
    (ξ : H) (hξ : ‖ξ‖ = 1)
    (hcentral : ∀ (r : Algebra R) (a : Algebra M),
      inner ℂ ξ ((coordinateInclusion hRM r * a).val ξ) =
      inner ℂ ξ ((a * coordinateInclusion hRM r).val ξ))
    (hcyclic : DenseRange (algebraVectorMap M ξ)) : StandardTracialPosition M where
  trace := concreteFactorTrace hM
  vector := ξ
  trace_eq x := (ii1_vector_state_eq_trace_of_relative_central M R hRM hM hirr
    ξ hξ hcentral x).symm
  cyclic := hcyclic

end

end KadisonKastler

end OAI

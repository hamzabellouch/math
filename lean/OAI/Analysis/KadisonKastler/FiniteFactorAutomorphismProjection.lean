import OAI.Analysis.KadisonKastler.StarEquivTraceTransport

namespace OAI

/-! # Automorphisms preserve projection equivalence in a finite diffuse factor

The normalized trace and the constructed projection dimension identify
a projection with its image under any star-algebra automorphism. This
will compare a core window projection with its dual-character image.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance finiteAutomorphismOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance finiteAutomorphismPreorder : Preorder (Algebra M) :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance finiteAutomorphismLE : LE (Algebra M) := (CStarAlgebra.spectralOrder _).toLE
local instance finiteAutomorphismStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

theorem equivalent_automorphism_projection
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra M) (p : AlgebraProjection M) :
    p.Equivalent ⟨e p.val, p.property.map e⟩ := by
  let q : AlgebraProjection M := ⟨e p.val, p.property.map e⟩
  let τ := concreteFactorTrace hM
  have hf (c : Algebra M) (hc : ∀ a : Algebra M, a * c = c * a) :
      ∃ z : ℂ, c = z • (1 : Algebra M) := by
    obtain ⟨z, hz⟩ := hM.factor c hc
    exact ⟨z, by simpa only [Algebra.algebraMap_eq_smul_one] using hz⟩
  have hu : (1 : Algebra M) ≠ 0 := by
    intro h
    exact hM.nonzero (congrArg Subtype.val h).symm
  have hd (r : AlgebraProjection M) :
      (τ.toLinearMap r.val).re = traceFreeDimension hf hM.diffuse r := by
    exact tracialFunctional_projection_dimension_re hf hM.diffuse hM.finite hu
      τ.toContinuousLinearMap τ.map_one (fun _ hx => τ.nonneg hx) τ.tracial r
  have ht : τ.toLinearMap q.val = τ.toLinearMap p.val :=
    trace_starAlgEquiv hM τ τ e p.val
  have he : traceFreeDimension hf hM.diffuse p = traceFreeDimension hf hM.diffuse q := by
    rw [← hd p, ← hd q, ht]
  apply AlgebraProjection.equivalent_of_mutual_subequivalent hM.finite
  · exact (traceFreeDimension_le_iff_subequivalent hf hM.diffuse hM.finite hu p q).mp he.le
  · exact (traceFreeDimension_le_iff_subequivalent hf hM.diffuse hM.finite hu q p).mp he.ge

end

end KadisonKastler

end OAI

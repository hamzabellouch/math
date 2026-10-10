import OAI.Analysis.KadisonKastler.TomitaLinearPolarCoordinates

namespace OAI

/-! # The full adjoint Tomita graph in positive coordinates

The equation between the two bounded square roots determines the whole
adjoint graph. Its solution uses their commuting squares summing to one.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

omit [CompleteSpace H] in
private theorem linearIsometry_inner_right (U : H ≃ₗᵢ[ℂ] H) (x y : H) :
    inner ℂ (U x) y = inner ℂ x (U.symm y) := by
  have h := U.inner_map_map x (U.symm y)
  rwa [U.apply_symm_apply] at h

private theorem inner_selfAdjoint_left (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (x y : H) :
    inner ℂ (A x) y = inner ℂ x (A y) := by
  rw [← ContinuousLinearMap.adjoint_inner_right]
  have hs : A.adjoint = A := hA.star_eq
  rw [hs]

/-- Membership in the adjoint graph is an equation of bounded operators. -/
theorem tomitaAdjoint_graph_equation (y z : H) :
    (y, z) ∈ (tomitaClosedLinearOperator M J Ω 1).adjoint.graph ↔
      tomitaGraphComplementRoot (M := M) J Ω
        ((tomitaLinearPolarUnitary J Ω hsep hcyc).symm y) =
      tomitaGraphRoot (M := M) J Ω z := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (tomitaClosedLinearOperator_dense J Ω 1 hsep hcyc),
    Submodule.mem_adjoint_iff]
  constructor
  · intro h
    apply ext_inner_left ℂ
    intro a
    have ha := h _ _ ((tomitaClosedLinearOperator_positive_graph_iff J Ω hsep hcyc _ _).mpr
      ⟨a, rfl, rfl⟩)
    rw [linearIsometry_inner_right,
      inner_selfAdjoint_left _ (tomitaGraphComplementRoot_nonneg J Ω).isSelfAdjoint,
      inner_selfAdjoint_left _ (tomitaGraphRoot_selfAdjoint J Ω)] at ha
    exact sub_eq_zero.mp ha
  · intro h x v hxv
    obtain ⟨a, rfl, rfl⟩ :=
      (tomitaClosedLinearOperator_positive_graph_iff J Ω hsep hcyc x v).mp hxv
    rw [linearIsometry_inner_right,
      inner_selfAdjoint_left _ (tomitaGraphComplementRoot_nonneg J Ω).isSelfAdjoint,
      inner_selfAdjoint_left _ (tomitaGraphRoot_selfAdjoint J Ω), h, sub_self]

/-- The adjoint graph is the complementary positive column. -/
theorem tomitaAdjoint_graph_iff (y z : H) :
    (y, z) ∈ (tomitaClosedLinearOperator M J Ω 1).adjoint.graph ↔
      ∃ a : H,
        tomitaLinearPolarUnitary J Ω hsep hcyc (tomitaGraphRoot (M := M) J Ω a) = y ∧
        tomitaGraphComplementRoot (M := M) J Ω a = z := by
  rw [tomitaAdjoint_graph_equation J Ω hsep hcyc]
  let R := tomitaGraphRoot (M := M) J Ω
  let Q := tomitaGraphComplementRoot (M := M) J Ω
  let U := tomitaLinearPolarUnitary J Ω hsep hcyc
  have hRQ (a : H) : R (Q a) = Q (R a) :=
    congrArg (fun T : H →L[ℂ] H => T a) (tomitaGraphRoots_commute J Ω).eq
  have hsum (a : H) : R (R a) + Q (Q a) = a := by
    change (R * R + Q * Q) a = a
    have he : R * R + Q * Q = 1 := by
      rw [tomitaGraphRoot_square, tomitaGraphComplementRoot_square J Ω hsep hcyc]
      abel
    rw [he, one_apply_eq_self]
  constructor
  · intro h
    let w := U.symm y
    change Q w = R z at h
    refine ⟨R w + Q z, ?_, ?_⟩
    · have he : R (R w + Q z) = w := by
        rw [map_add, hRQ, ← h]
        exact hsum w
      change U (R (R w + Q z)) = y
      rw [he]
      exact U.apply_symm_apply y
    · change Q (R w + Q z) = z
      rw [map_add, ← hRQ, h]
      exact hsum z
  · rintro ⟨a, ha, hb⟩
    change Q (U.symm y) = R z
    rw [← ha, U.symm_apply_apply, ← hb]
    exact (hRQ a).symm

end

end KadisonKastler

end OAI

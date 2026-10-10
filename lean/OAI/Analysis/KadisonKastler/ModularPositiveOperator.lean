import OAI.Analysis.KadisonKastler.TomitaAdjointCoordinates

namespace OAI

/-! # The positive self-adjoint square root of the modular operator

Removing the linear polar unitary from the closed Tomita operator gives an
unbounded operator with graph `(r a, q a)`, where the two commuting positive
roots satisfy `r² + q² = 1`. These coordinates prove self-adjointness directly.
-/

namespace KadisonKastler

noncomputable section

open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

/-- The positive part of the closed Tomita operator. -/
def modularPositiveOperator : H →ₗ.[ℂ] H :=
  (tomitaLinearPolarUnitary J Ω hsep hcyc).symm.toLinearEquiv.toLinearMap.compPMap
    (tomitaClosedLinearOperator M J Ω 1)

private theorem modularPositiveOperator_graph_transport (x y : H) :
    (x, y) ∈ (modularPositiveOperator J Ω hsep hcyc).graph ↔
      (x, tomitaLinearPolarUnitary J Ω hsep hcyc y) ∈
        (tomitaClosedLinearOperator M J Ω 1).graph := by
  simp only [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨v, hv, hy⟩
    refine ⟨v, hv, ?_⟩
    change (tomitaClosedLinearOperator M J Ω 1) v = _
    rw [← hy]
    exact ((tomitaLinearPolarUnitary J Ω hsep hcyc).apply_symm_apply _).symm
  · rintro ⟨v, hv, hy⟩
    refine ⟨v, hv, ?_⟩
    change (tomitaLinearPolarUnitary J Ω hsep hcyc).symm
      ((tomitaClosedLinearOperator M J Ω 1) v) = y
    rw [hy, LinearIsometryEquiv.symm_apply_apply]

theorem modularPositiveOperator_graph_iff (x y : H) :
    (x, y) ∈ (modularPositiveOperator J Ω hsep hcyc).graph ↔
      ∃ a : H, tomitaGraphRoot (M := M) J Ω a = x ∧
        tomitaGraphComplementRoot (M := M) J Ω a = y := by
  rw [modularPositiveOperator_graph_transport,
    tomitaClosedLinearOperator_positive_graph_iff J Ω hsep hcyc]
  exact exists_congr fun a => and_congr_right fun _ =>
    (tomitaLinearPolarUnitary J Ω hsep hcyc).injective.eq_iff

theorem modularPositiveOperator_dense :
    Dense ((modularPositiveOperator J Ω hsep hcyc).domain : Set H) :=
  tomitaClosedLinearOperator_dense J Ω 1 hsep hcyc

private theorem modularPositiveOperator_adjoint_equation (y z : H) :
    (y, z) ∈ (modularPositiveOperator J Ω hsep hcyc).adjoint.graph ↔
      tomitaGraphComplementRoot (M := M) J Ω y = tomitaGraphRoot (M := M) J Ω z := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (modularPositiveOperator_dense J Ω hsep hcyc),
    Submodule.mem_adjoint_iff]
  have hi (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (x y : H) :
      inner ℂ (A x) y = inner ℂ x (A y) := by
    rw [← ContinuousLinearMap.adjoint_inner_right]
    have hs : A.adjoint = A := hA.star_eq
    rw [hs]
  constructor
  · intro h
    apply ext_inner_left ℂ
    intro a
    have ha := h _ _ ((modularPositiveOperator_graph_iff J Ω hsep hcyc _ _).mpr
      ⟨a, rfl, rfl⟩)
    rw [hi _ (tomitaGraphComplementRoot_nonneg J Ω).isSelfAdjoint,
      hi _ (tomitaGraphRoot_selfAdjoint J Ω)] at ha
    exact sub_eq_zero.mp ha
  · intro h x v hxv
    obtain ⟨a, rfl, rfl⟩ := (modularPositiveOperator_graph_iff J Ω hsep hcyc x v).mp hxv
    rw [hi _ (tomitaGraphComplementRoot_nonneg J Ω).isSelfAdjoint,
      hi _ (tomitaGraphRoot_selfAdjoint J Ω), h, sub_self]

/-- The graph parametrization is unchanged by taking the adjoint. -/
theorem modularPositiveOperator_adjoint_graph_iff (y z : H) :
    (y, z) ∈ (modularPositiveOperator J Ω hsep hcyc).adjoint.graph ↔
      ∃ a : H, tomitaGraphRoot (M := M) J Ω a = y ∧
        tomitaGraphComplementRoot (M := M) J Ω a = z := by
  rw [modularPositiveOperator_adjoint_equation J Ω hsep hcyc]
  let R := tomitaGraphRoot (M := M) J Ω
  let Q := tomitaGraphComplementRoot (M := M) J Ω
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
    refine ⟨R y + Q z, ?_, ?_⟩
    · change R (R y + Q z) = y
      rw [map_add, hRQ, ← h]
      exact hsum y
    · change Q (R y + Q z) = z
      rw [map_add, ← hRQ, h]
      exact hsum z
  · rintro ⟨a, rfl, rfl⟩
    exact (hRQ a).symm

theorem modularPositiveOperator_selfAdjoint :
    IsSelfAdjoint (modularPositiveOperator J Ω hsep hcyc) := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply LinearPMap.eq_of_eq_graph
  ext ⟨x, y⟩
  rw [modularPositiveOperator_adjoint_graph_iff, modularPositiveOperator_graph_iff]

theorem modularPositiveOperator_closed :
    (modularPositiveOperator J Ω hsep hcyc).IsClosed :=
  (modularPositiveOperator_selfAdjoint J Ω hsep hcyc).isClosed

/-- Positivity on the whole domain, not only the algebraic core. -/
theorem modularPositiveOperator_inner_nonneg (x : (modularPositiveOperator J Ω hsep hcyc).domain) :
    0 ≤ inner ℂ (modularPositiveOperator J Ω hsep hcyc x) (x : H) := by
  obtain ⟨a, ha, hb⟩ := (modularPositiveOperator_graph_iff J Ω hsep hcyc _ _).mp
    (LinearPMap.mem_graph _ x)
  rw [← ha, ← hb, ← ContinuousLinearMap.adjoint_inner_right]
  have hs : (tomitaGraphComplementRoot (M := M) J Ω).adjoint =
      tomitaGraphComplementRoot (M := M) J Ω :=
    (tomitaGraphComplementRoot_nonneg J Ω).isSelfAdjoint.star_eq
  rw [hs]
  have hp : 0 ≤ tomitaGraphComplementRoot (M := M) J Ω * tomitaGraphRoot (M := M) J Ω :=
    Commute.mul_nonneg (tomitaGraphComplementRoot_nonneg J Ω) (CFC.sqrt_nonneg _)
      (tomitaGraphRoots_commute J Ω).symm
  exact (ContinuousLinearMap.nonneg_iff_isPositive.mp hp).inner_nonneg_right a

end

end KadisonKastler

end OAI

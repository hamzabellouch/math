import OAI.Analysis.PureInfiniteness.NonunitalFunctionalRepresentation
import OAI.Analysis.Nuclearity.UnitizedCoefficients

namespace OAI

/-! The finite cyclic-vector approximation in KR02 Lemma 7.18. The cyclic
representation is on the unitization, so this applies to nonunital algebras
without assuming cyclicity of their restricted representations. -/

noncomputable section
open scoped BigOperators InnerProductSpace Topology ComplexOrder

namespace WeakPureInfiniteness

variable {D H I J : Type*} [NonUnitalCStarAlgebra D]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype I] [Fintype J]

lemma finite_quadratic_coefficient_approximation
    (π : Unitization ℂ D →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcyc : DenseRange (fun a => π a ξ))
    (L : J → I → I → H →L[ℂ] H) (k : I → H) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : I → Unitization ℂ D,
      ‖(fun j => ∑ i, ∑ r, ⟪k i, L j i r (k r)⟫_ℂ) -
        (fun j => ∑ i, ∑ r, ⟪π (a i) ξ, L j i r (π (a r) ξ)⟫_ℂ)‖ < ε := by
  let Q : (I → H) → J → ℂ := fun z j => ∑ i, ∑ r, ⟪z i, L j i r (z r)⟫_ℂ
  have hQ : Continuous Q := by
    apply continuous_pi
    intro j
    fun_prop
  have hQat : ContinuousAt Q k := hQ.continuousAt
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hQat ε hε
  have hd : DenseRange (fun a : I → Unitization ℂ D => fun i => π (a i) ξ) :=
    DenseRange.piMap (fun _ => hcyc)
  obtain ⟨a, ha⟩ := Metric.denseRange_iff.mp hd k δ hδ
  refine ⟨a, ?_⟩
  have h := hclose (by simpa only [dist_comm] using ha)
  simpa only [dist_eq_norm, norm_sub_rev, Q] using h

lemma unitized_coefficient_representation
    {B : Type*} [NonUnitalCStarAlgebra B]
    (π : Unitization ℂ D →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (T : B → D) (a : I → Unitization ℂ D) (c : I → B) (b : B)
    (e : H →L[ℂ] H) (he : ∀ d, Commute (π d) e) :
    ⟪ξ, π ((unitizedCoefficientEnlargement T a c b : D) : Unitization ℂ D) (e ξ)⟫_ℂ =
      ∑ i, ∑ j, ⟪π (a i) ξ,
        π ((T (star (c i) * b * c j) : D) : Unitization ℂ D) (e (π (a j) ξ))⟫_ℂ := by
  rw [inr_unitizedCoefficientEnlargement]
  simp only [map_sum, sum_apply, inner_sum, map_mul, map_star,
    ContinuousLinearMap.star_eq_adjoint, mul_apply_eq_comp]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [ContinuousLinearMap.adjoint_inner_right]
  congr 2
  exact congrArg (fun f : H →L[ℂ] H => f ξ) (he (a j)).eq

end WeakPureInfiniteness

end

end OAI

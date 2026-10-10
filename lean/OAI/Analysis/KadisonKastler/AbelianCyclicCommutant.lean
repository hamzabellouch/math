import OAI.Analysis.KadisonKastler.CommonRightAction
import OAI.Analysis.KadisonKastler.BoundaryFiniteIsomorphism

namespace OAI

/-! # A cyclic commutative von Neumann algebra is maximal abelian

The proof uses only the cyclic vector. On the commutant, the norms of
an operator and its adjoint at this vector agree. This controls right
multiplication while approximating by the original commutative algebra.
-/

namespace KadisonKastler

open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (M : VonNeumannAlgebra H) (ξ : H)
  (hcomm : ∀ a b : Algebra M, a * b = b * a)
  (hcyclic : DenseRange (fun a : Algebra M => a.val ξ))

include hcomm

private theorem abelian_operator_norm_star (a : Algebra M) (x : H) :
    ‖star a.val x‖ = ‖a.val x‖ := by
  have ha : IsStarNormal a.val := ⟨congrArg Subtype.val (hcomm (star a) a)⟩
  exact (ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint.mp ha x).symm

include hcyclic

private theorem commutant_adjoint_vector_le (S : H →L[ℂ] H) (hS : S ∈ M.commutant) :
    ‖star S ξ‖ ≤ ‖S ξ‖ := by
  have hbound (a : Algebra M) :
      ‖inner ℂ (a.val ξ) (star S ξ)‖ ≤ ‖a.val ξ‖ * ‖S ξ‖ := by
    have hSa : S * a.val = a.val * S :=
      (VonNeumannAlgebra.mem_commutant_iff.mp hS a.val a.property).symm
    calc
      ‖inner ℂ (a.val ξ) (star S ξ)‖ = ‖inner ℂ (S (a.val ξ)) ξ‖ := by
        rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
      _ = ‖inner ℂ (a.val (S ξ)) ξ‖ := by
        rw [← mul_apply_eq_comp, hSa, mul_apply_eq_comp]
      _ = ‖inner ℂ (S ξ) (star a.val ξ)‖ := by
        rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
      _ ≤ ‖S ξ‖ * ‖star a.val ξ‖ := norm_inner_le_norm _ _
      _ = ‖a.val ξ‖ * ‖S ξ‖ := by rw [abelian_operator_norm_star M hcomm]; ring
  have hclosed : IsClosed {y : H | ‖inner ℂ y (star S ξ)‖ ≤ ‖y‖ * ‖S ξ‖} :=
    isClosed_le (continuous_id.inner continuous_const).norm
      (continuous_id.norm.mul continuous_const)
  have hall (y : H) : ‖inner ℂ y (star S ξ)‖ ≤ ‖y‖ * ‖S ξ‖ :=
    (closure_minimal (by rintro _ ⟨a, rfl⟩; exact hbound a) hclosed) (hcyclic y)
  have h := hall (star S ξ)
  rw [← inner_self_re_eq_norm, inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (star S ξ), norm_nonneg (S ξ)]

theorem commutant_vector_norm_star (S : H →L[ℂ] H) (hS : S ∈ M.commutant) :
    ‖star S ξ‖ = ‖S ξ‖ := by
  apply le_antisymm (commutant_adjoint_vector_le M ξ hcomm hcyclic S hS)
  simpa only [star_star] using commutant_adjoint_vector_le M ξ hcomm hcyclic
    (star S) (M.commutant.toStarSubalgebra.star_mem' hS)

theorem commutant_mul_comm_of_cyclic_commutative (S T : H →L[ℂ] H)
    (hS : S ∈ M.commutant) (hT : T ∈ M.commutant) : S * T = T * S := by
  have hzero : (S * T - T * S) ξ = 0 := by
    apply norm_eq_zero.mp
    by_contra hn
    have hpos : 0 < ‖(S * T - T * S) ξ‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    let ε := ‖(S * T - T * S) ξ‖ / (2 * ‖T‖ + 1)
    have hε : 0 < ε := div_pos hpos (by positivity)
    obtain ⟨_, ⟨a, rfl⟩, ha⟩ := Metric.mem_closure_iff.mp (hcyclic (S ξ)) ε hε
    rw [dist_eq_norm] at ha
    change ‖(S - a.val) ξ‖ < ε at ha
    have ha' : a.val ∈ M.commutant := by
      apply VonNeumannAlgebra.mem_commutant_iff.mpr
      intro b hb
      exact congrArg Subtype.val (hcomm ⟨b, hb⟩ a)
    have hdiff : S - a.val ∈ M.commutant := sub_mem hS ha'
    have hright : ‖((S - a.val) * T) ξ‖ ≤ ‖T‖ * ‖(S - a.val) ξ‖ := by
      rw [← commutant_vector_norm_star M ξ hcomm hcyclic _ (mul_mem hdiff hT),
        star_mul, mul_apply_eq_comp]
      calc
        ‖star T (star (S - a.val) ξ)‖ ≤ ‖star T‖ * ‖star (S - a.val) ξ‖ :=
          (star T).le_opNorm _
        _ = ‖T‖ * ‖(S - a.val) ξ‖ := by
          rw [norm_star, commutant_vector_norm_star M ξ hcomm hcyclic _ hdiff]
    have hleft : ‖(T * (S - a.val)) ξ‖ ≤ ‖T‖ * ‖(S - a.val) ξ‖ := T.le_opNorm _
    have he : S * T - T * S = (S - a.val) * T - T * (S - a.val) := by
      have haT := VonNeumannAlgebra.mem_commutant_iff.mp hT a.val a.property
      simp only [sub_mul, mul_sub]
      rw [haT]
      abel
    have hbound : ‖(S * T - T * S) ξ‖ ≤ 2 * ‖T‖ * ‖(S - a.val) ξ‖ := by
      rw [he, sub_apply]
      exact (norm_sub_le _ _).trans (by linarith [hright, hleft])
    have hlt : (2 * ‖T‖ + 1) * ‖(S - a.val) ξ‖ < ‖(S * T - T * S) ξ‖ := by
      have hh := mul_lt_mul_of_pos_left ha (show 0 < 2 * ‖T‖ + 1 by positivity)
      dsimp [ε] at hh
      rwa [mul_div_cancel₀ _ (show 2 * ‖T‖ + 1 ≠ 0 by positivity)] at hh
    nlinarith [norm_nonneg ((S - a.val) ξ)]
  apply operator_eq_of_mem_commutant_of_eq_on_cyclicVector M ξ hcyclic
    (S * T) (T * S) (mul_mem hS hT) (mul_mem hT hS)
  exact sub_eq_zero.mp hzero

/-- In a cyclic representation, a commutative algebra equals its commutant. -/
theorem mem_of_mem_commutant_of_cyclic_commutative (S : H →L[ℂ] H)
    (hS : S ∈ M.commutant) : S ∈ M := by
  change S ∈ (M : Set (H →L[ℂ] H))
  rw [← M.centralizer_centralizer]
  intro T hT
  exact commutant_mul_comm_of_cyclic_commutative M ξ hcomm hcyclic T S
    (VonNeumannAlgebra.mem_commutant_iff.mpr hT) hS

end

end KadisonKastler

end OAI

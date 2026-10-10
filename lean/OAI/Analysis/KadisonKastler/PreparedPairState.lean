import OAI.Analysis.KadisonKastler.PreparedPairCyclicity
import OAI.Analysis.FactorGeneration.LocalizedStates

namespace OAI

/-! # The common vector functional centralizes the shared algebra

Matching left and right vector actions, including their adjoints, gives
the centralizer identity directly by the Hilbert-space adjoint formula.
The source's common conjugation supplies these matches on unitaries;
the four-unitary span then gives every element of the common algebra.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Matching a left operator and its adjoint on the vector with one
commutant operator proves the vector-functional centralizer identity. -/
theorem vector_functional_commutes_of_right_vector
    (N : VonNeumannAlgebra H) (Ω : H) (r s : H →L[ℂ] H)
    (hs : s ∈ N.commutant)
    (hvector : r Ω = s Ω) (hstar : (star r) Ω = (star s) Ω)
    (x : Algebra N) :
    inner ℂ Ω ((r * x.val) Ω) = inner ℂ Ω ((x.val * r) Ω) := by
  calc
    inner ℂ Ω ((r * x.val) Ω) = inner ℂ ((star r) Ω) (x.val Ω) := by
      simp only [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_left]
    _ = inner ℂ ((star s) Ω) (x.val Ω) := by rw [hstar]
    _ = inner ℂ Ω ((s * x.val) Ω) := by
      simp only [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_left]
    _ = inner ℂ Ω ((x.val * s) Ω) := by
      rw [← VonNeumannAlgebra.mem_commutant_iff.mp hs x.val x.property]
    _ = inner ℂ Ω ((x.val * r) Ω) := by
      simp only [mul_apply_eq_comp]
      rw [← hvector]

/-- It suffices to identify the right vector actions on unitaries of the
common algebra: these unitaries span every element. -/
theorem vector_functional_centralizes_of_right_unitaries
    (R N : VonNeumannAlgebra H) (hRN : R ≤ N) (Ω : H)
    (hright : ∀ u : unitary (Algebra R), ∃ s ∈ N.commutant,
      (u : Algebra R).val Ω = s Ω ∧
      (star (u : Algebra R)).val Ω = (star s) Ω)
    (r : Algebra R) (x : Algebra N) :
    inner ℂ Ω ((r.val * x.val) Ω) = inner ℂ Ω ((x.val * r.val) Ω) := by
  let ι : Algebra R →⋆ₐ[ℂ] Algebra N := StarSubalgebra.inclusion hRN
  let φ := Generator.Tracial.vectorFunctional (M := N) Ω
  let T : Algebra R →ₗ[ℂ] ℂ := φ.toLinearMap.comp
    ((LinearMap.mulRight ℂ x - LinearMap.mulLeft ℂ x).comp ι.toAlgHom.toLinearMap)
  have hT (u : unitary (Algebra R)) : ‖T (u : Algebra R)‖ ≤ 0 := by
    obtain ⟨s, hs, hv, hvs⟩ := hright u
    have he := vector_functional_commutes_of_right_vector N Ω
      (u : Algebra R).val s hs hv hvs x
    have hz : T (u : Algebra R) = 0 := by
      change inner ℂ Ω (((u : Algebra R).val * x.val - x.val * (u : Algebra R).val) Ω) = 0
      rw [sub_apply, inner_sub_right, he, sub_self]
    rw [hz, norm_zero]
  have hn := norm_le_twice_unitary_bound T hT r
  have hz : T r = 0 := norm_eq_zero.mp (le_antisymm (by simpa only [mul_zero, zero_mul] using hn)
    (norm_nonneg _))
  change inner ℂ Ω ((r.val * x.val - x.val * r.val) Ω) = 0 at hz
  rw [sub_apply, inner_sub_right] at hz
  exact sub_eq_zero.mp hz

/-- The actual conjugate right algebra and central-vector relation in the
prepared-pair construction imply that the vector functional on `N`
centralizes `R`. -/
theorem vector_functional_centralizes_of_conjugate_right
    (R N : VonNeumannAlgebra H) (hRN : R ≤ N)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) (Ω : H)
    (hright : ∀ r : Algebra R, conjugationOperator J r.val ∈ N.commutant)
    (hcentral : ∀ r : Algebra R,
      r.val Ω = conjugationOperator J (star r).val Ω)
    (r : Algebra R) (x : Algebra N) :
    inner ℂ Ω ((r.val * x.val) Ω) = inner ℂ Ω ((x.val * r.val) Ω) := by
  apply vector_functional_centralizes_of_right_unitaries R N hRN Ω ?_ r x
  intro u
  let u₀ : unitary (H →L[ℂ] H) :=
    Unitary.map (StarMonoidHom.ofClass R.toStarSubalgebra.subtype) u
  refine ⟨conjugationOperator J (star (u : Algebra R)).val,
    hright (star (u : Algebra R)), hcentral (u : Algebra R), ?_⟩
  have hs : star (conjugationOperator J (star (u : Algebra R)).val) =
      conjugationOperator J (u : Algebra R).val := by
    change star (conjugationOperator J (star (u₀ : H →L[ℂ] H))) =
      conjugationOperator J (u₀ : H →L[ℂ] H)
    simpa only [Unitary.coe_star, star_star] using
      conjugationOperator_star_unitary J hJ (star u₀)
  rw [hs]
  simpa only [star_star] using hcentral (star (u : Algebra R))

end

end KadisonKastler

end OAI

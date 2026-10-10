import OAI.Analysis.KadisonKastler.StateOrbitNeighborhood
import OAI.Analysis.KadisonKastler.StateOrbitNorm

namespace OAI

/-! # Uniform unitary tests from a singleton asymptotic orbit hull -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem unitary_commutator_vector_norm_eq (ξ : H) (a : Algebra M)
    (u : unitary (Algebra M)) :
    ‖(u.val*a-a*u.val).val ξ‖=‖(star u.val*a*u.val).val ξ-a.val ξ‖ := by
  have he : u.val.val ((star u.val*a*u.val).val ξ-a.val ξ) =
      -(u.val*a-a*u.val).val ξ := by
    change u.val.val (((star u.val*a*u.val).val-a.val) ξ) = _
    rw [← mul_apply_eq_comp]
    have ha : u.val*(star u.val*a*u.val-a) = -(u.val*a-a*u.val) := by
      rw [mul_sub,← mul_assoc,← mul_assoc,u.property.2,one_mul]
      abel
    exact congrArg (fun b : Algebra M => b.val ξ) ha
  have h := Unitary.norm_map (ambientAlgebraUnitary u)
    ((star u.val*a*u.val).val ξ-a.val ξ)
  change ‖u.val.val ((star u.val*a*u.val).val ξ-a.val ξ)‖=_ at h
  rwa [he,norm_neg] at h

theorem singleton_stateOrbitCore_unitary_control (ξ : H) (a : Algebra M)
    (hcore : stateOrbitCore ξ a={ContinuousLinearMapWOT.ofCLM a.val})
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : unitary (Algebra M),
      ‖vectorStateCommutator ξ u.val‖ ≤ δ → ‖(u.val*a-a*u.val).val ξ‖ < ε := by
  let U : Set (H →WOT[ℂ] H) :=
    {T | ‖a.val ξ‖^2-ε^2/4 < (inner ℂ (a.val ξ) (T ξ)).re}
  have hU : IsOpen U := isOpen_lt continuous_const
    (Complex.continuous_re.comp (ContinuousLinearMapWOT.continuous_inner_apply
      continuous_id ξ (a.val ξ)))
  have hsub : stateOrbitCore ξ a ⊆ U := by
    intro T hT
    rw [hcore,Set.mem_singleton_iff] at hT
    subst T
    change ‖a.val ξ‖^2-ε^2/4 < (inner ℂ (a.val ξ) (a.val ξ)).re
    rw [inner_self_eq_norm_sq_to_K]
    have hre (r : ℝ) : ((r : ℂ)^2).re=r^2 := by
      norm_num [pow_two,Complex.mul_re]
    change ‖a.val ξ‖^2-ε^2/4 < ((‖a.val ξ‖ : ℂ)^2).re
    rw [hre]
    nlinarith only [sq_pos_of_pos hε]
  obtain ⟨d,hd,hdU⟩ := exists_stateOrbitHull_subset_open ξ a hU hsub
  let δ := min d (ε^2/(4*(‖a‖^2+1)))
  have hδ : 0 < δ := lt_min hd (div_pos (sq_pos_of_pos hε) (by positivity))
  refine ⟨δ,hδ,?_⟩
  intro u hu
  let T := ContinuousLinearMapWOT.ofCLM (star u.val*a*u.val).val
  have hT : T ∈ closedConvexHull ℝ (stateUnitaryOrbit ξ a d) :=
    subset_closedConvexHull ⟨u,hu.trans (min_le_left _ _),rfl⟩
  have hi : ‖a.val ξ‖^2-ε^2/4 < (inner ℂ (a.val ξ) (T ξ)).re := hdU hT
  have hv := stateConjugate_vector_norm_sq_le ξ a u
  have hdn : ‖vectorStateCommutator ξ u.val‖*(4*(‖a‖^2+1)) ≤ ε^2 :=
    (le_div_iff₀ (by positivity)).mp (hu.trans (min_le_right _ _))
  have hprod : ‖vectorStateCommutator ξ u.val‖*‖a‖^2 ≤ ε^2/4 := by
    nlinarith only [hdn,norm_nonneg (vectorStateCommutator ξ u.val)]
  have hs := norm_sub_sq (𝕜 := ℂ) (a.val ξ) (T ξ)
  change ‖a.val ξ-T ξ‖^2 = ‖a.val ξ‖^2-
    2*(inner ℂ (a.val ξ) (T ξ)).re+‖T ξ‖^2 at hs
  rw [unitary_commutator_vector_norm_eq,norm_sub_rev]
  change ‖a.val ξ-T ξ‖ < ε
  change ‖T ξ‖^2 ≤ _ at hv
  nlinarith only [hi,hv,hprod,hs,hε,norm_nonneg (a.val ξ-T ξ)]

end

end KadisonKastler

end OAI

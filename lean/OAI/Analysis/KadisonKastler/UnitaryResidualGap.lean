import OAI.Analysis.KadisonKastler.StateOrbitGap
import OAI.Analysis.KadisonKastler.CenteredVectorApproximation

namespace OAI

/-! # Near-central unitaries with a uniform residual gap

The scalar hull conclusion of Haagerup's Proposition 1.3 gives the
unitary gap in Lemma 3.2. Centered cyclic approximation extends the
operator-vector calculation to every vector orthogonal to the reference.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance unitaryResidualRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

private theorem centered_unitary_gap
    (J : H ≃ₗᵢ⋆[ℂ] H)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H)
    (hbound : ∀ u : unitary (Algebra M),
      ‖centralVectorDefect J ξ u.val.val‖^2 ≤ ‖vectorStateCommutator ξ u.val‖)
    (a : Algebra M) (hcenter : vectorFunctional ξ a=0) (haξ : a.val ξ≠0)
    (hhull : ∀ δ : ℝ, 0 < δ → ∃ z : ℂ,
      ContinuousLinearMapWOT.ofCLM (z • (1 : H →L[ℂ] H)) ∈
        closedConvexHull ℝ (stateUnitaryOrbit ξ a δ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ u : unitary (Algebra M), ‖centralVectorDefect J ξ u.val.val‖ < ε ∧
      (3/4:ℝ)*‖a.val ξ‖ < ‖centralVectorDefect J (a.val ξ) u.val.val‖ := by
  have hn : 0 < ‖a.val ξ‖ := norm_pos_iff.mpr haξ
  let e := min ε (‖a.val ξ‖/(16*(‖a‖+1)))
  have he : 0 < e := lt_min hε (div_pos hn (by positivity))
  let δ := e^2/2
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨z,hz⟩ := hhull δ hδ
  obtain ⟨u,hustate,hugap⟩ := exists_unitary_gap_of_scalar_state_orbit_hull
    ξ a hcenter haξ δ (7/8) (by norm_num) (by norm_num) z hz
  have hsq := hbound u
  have hu : ‖centralVectorDefect J ξ u.val.val‖ < e := by
    dsimp only [δ] at hustate
    nlinarith only [hsq,hustate,he,norm_nonneg (centralVectorDefect J ξ u.val.val)]
  have hden : 0 < 16*(‖a‖+1) := by positivity
  have hprod : ‖a‖*‖centralVectorDefect J ξ u.val.val‖ ≤ ‖a.val ξ‖/16 := by
    have hle := hu.le.trans (min_le_right ε (‖a.val ξ‖/(16*(‖a‖+1))))
    have hm := (le_div_iff₀ hden).mp hle
    nlinarith only [hm,norm_nonneg (centralVectorDefect J ξ u.val.val)]
  have hcomm := commutator_vector_norm_le_central_defects J hright ξ a u.val
  refine ⟨u,hu.trans_le (min_le_left _ _),?_⟩
  linarith only [hugap,hcomm,hprod,hn]

theorem exists_unitary_residual_gap_of_state_defect_bound
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hunit : ‖ξ‖=1)
    (hbound : ∀ u : unitary (Algebra M),
      ‖centralVectorDefect J ξ u.val.val‖^2 ≤ ‖vectorStateCommutator ξ u.val‖)
    (hhull : ∀ a : Algebra M, ∀ δ : ℝ, 0 < δ → ∃ z : ℂ,
      ContinuousLinearMapWOT.ofCLM (z • (1 : H →L[ℂ] H)) ∈
        closedConvexHull ℝ (stateUnitaryOrbit ξ a δ))
    (η : H) (hη : η≠0) (horth : inner ℂ ξ η=0)
    (hηclosure : η ∈ closure (Set.range (algebraVectorMap M ξ)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ u : unitary (Algebra M), ‖centralVectorDefect J ξ u.val.val‖ < ε ∧
      ‖η‖/2 ≤ ‖centralVectorDefect J η u.val.val‖ := by
  have hn : 0 < ‖η‖ := norm_pos_iff.mpr hη
  obtain ⟨a,hcenter,hnear⟩ := exists_centered_algebra_vector_near_of_mem_closure ξ hunit η horth hηclosure
    (‖η‖/64) (by positivity)
  have haξ : a.val ξ≠0 := by
    intro hz
    rw [hz,zero_sub,norm_neg] at hnear
    linarith
  have hnorm : ‖η‖ ≤ ‖a.val ξ‖+‖a.val ξ-η‖ := by
    have h := norm_le_insert (a.val ξ) η
    simpa only [norm_sub_rev,add_comm] using h
  obtain ⟨u,hu,hugap⟩ := centered_unitary_gap J hright ξ hbound
    a hcenter haξ (hhull a) ε hε
  have hLip := centralVectorDefect_vector_lipschitz J hJ (a.val ξ) η u.val.val
  have hU : ‖u.val.val‖ ≤ 1 := by
    change ‖u.val‖ ≤ 1
    exact norm_unitary_le_one u
  have hnearD : ‖centralVectorDefect J (a.val ξ) u.val.val‖ ≤
      ‖centralVectorDefect J η u.val.val‖+2*‖a.val ξ-η‖ := by
    exact hLip.trans (add_le_add le_rfl
      (mul_le_of_le_one_right (by positivity) hU))
  refine ⟨u,hu,?_⟩
  linarith only [hugap,hnearD,hnorm,hnear,hn]

theorem exists_unitary_residual_gap_of_scalar_state_hulls
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (hunit : ‖ξ‖=1)
    (hcyc : DenseRange (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (hhull : ∀ a : Algebra M, ∀ δ : ℝ, 0 < δ → ∃ z : ℂ,
      ContinuousLinearMapWOT.ofCLM (z • (1 : H →L[ℂ] H)) ∈
        closedConvexHull ℝ (stateUnitaryOrbit ξ a δ))
    (η : H) (hη : η≠0) (horth : inner ℂ ξ η=0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ u : unitary (Algebra M), ‖centralVectorDefect J ξ u.val.val‖ < ε ∧
      ‖η‖/2 ≤ ‖centralVectorDefect J η u.val.val‖ :=
  exists_unitary_residual_gap_of_state_defect_bound J hJ hright ξ hunit
    (centralVectorDefect_unitary_sq_le_stateCommutator J hJ hright hleft ξ hξ hcyc hpos)
    hhull η hη horth (hcyc η) ε hε

end

end KadisonKastler

end OAI

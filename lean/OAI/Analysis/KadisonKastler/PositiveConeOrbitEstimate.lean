import OAI.Analysis.KadisonKastler.PositiveConeUnitaryOrbit

namespace OAI

/-! # A quantitative comparison of positive cone vectors

Acuteness applied to the quadratic action of `1 - J u J` controls the
distance of two positive unit vectors by their distance after a commutant
unitary. This is a local vector estimate; no state representation or
homogeneity theorem is assumed here.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance positiveOrbitEstimateRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem positiveCone_unitary_orbit_norm_sq_le
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ = ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {η ζ : H} (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (hζ : ζ ∈ modularPositiveCone (M := M) J ξ)
    (hηnorm : ‖η‖ = 1) (hζnorm : ‖ζ‖ = 1)
    (u : unitary (H →L[ℂ] H)) (hu : (u : H →L[ℂ] H) ∈ M.commutant) :
    ‖ζ-η‖ ^ 2 ≤ 4 * ‖(u : H →L[ℂ] H) η-ζ‖ := by
  let q := conjugationUnitary J hJ u
  let δ := ‖(u : H →L[ℂ] H) η-ζ‖
  have hqM : (q : H →L[ℂ] H) ∈ M := hleft ⟨u,hu⟩
  have hηJ := modularPositiveCone_fixed J hright ξ hξ hη
  have hζJ := modularPositiveCone_fixed J hright ξ hξ hζ
  have hqgap : ‖(q : H →L[ℂ] H) η-ζ‖ = δ := by
    change ‖J ((u : H →L[ℂ] H) (J η))-ζ‖ = δ
    rw [hηJ,← hζJ,← map_sub,J.norm_map]
  have hunorm : ‖(u : H →L[ℂ] H) η‖ = 1 := (Unitary.norm_map u η).trans hηnorm
  have hqunorm : ‖(q : H →L[ℂ] H) ((u : H →L[ℂ] H) η)‖ = 1 :=
    (Unitary.norm_map q _).trans hunorm
  have hfirst : 1-δ ≤ inner ℝ ζ ((u : H →L[ℂ] H) η) := by
    have h := real_inner_le_norm ζ (ζ-(u : H →L[ℂ] H) η)
    rw [inner_sub_right,real_inner_self_eq_norm_sq,hζnorm,norm_sub_rev] at h
    change 1 ^ 2 - inner ℝ ζ ((u : H →L[ℂ] H) η) ≤ 1 * δ at h
    linarith
  have hsecond : 1-δ ≤ inner ℝ ζ ((q : H →L[ℂ] H) η) := by
    have h := real_inner_le_norm ζ (ζ-(q : H →L[ℂ] H) η)
    rw [inner_sub_right,real_inner_self_eq_norm_sq,hζnorm,norm_sub_rev,hqgap] at h
    linarith
  have hthird : inner ℝ ζ ((q : H →L[ℂ] H) ((u : H →L[ℂ] H) η)) ≤
      inner ℝ ζ η + 2*δ := by
    have h₁ := real_inner_le_norm (ζ-(q : H →L[ℂ] H) η)
      ((q : H →L[ℂ] H) ((u : H →L[ℂ] H) η))
    rw [inner_sub_left,norm_sub_rev,hqgap,hqunorm] at h₁
    have he : inner ℝ ((q : H →L[ℂ] H) η)
        ((q : H →L[ℂ] H) ((u : H →L[ℂ] H) η)) =
        inner ℝ η ((u : H →L[ℂ] H) η) :=
      congrArg Complex.re (Unitary.inner_map_map q η ((u : H →L[ℂ] H) η))
    rw [he] at h₁
    have h₂ := real_inner_le_norm η ((u : H →L[ℂ] H) η-ζ)
    rw [inner_sub_right,hηnorm] at h₂
    change inner ℝ η ((u : H →L[ℂ] H) η) - inner ℝ η ζ ≤ 1*δ at h₂
    have hs : inner ℝ η ζ = inner ℝ ζ η := real_inner_comm ζ η
    rw [hs] at h₂
    linarith
  let a : Algebra M := 1-⟨q,hqM⟩
  have hrighta : conjugationOperator J a.val = 1-(u : H →L[ℂ] H) := by
    change conjugationOperator J (1-conjugationOperator J u) = _
    rw [conjugationOperator_sub,conjugationOperator_one J hJ,
      conjugationOperator_twice J hJ]
  have haη : modularQuadratic J a η =
      η-(u : H →L[ℂ] H) η-(q : H →L[ℂ] H) η+
        (q : H →L[ℂ] H) ((u : H →L[ℂ] H) η) := by
    change (1-(q : H →L[ℂ] H)) (conjugationOperator J a.val η) = _
    rw [hrighta,sub_apply,one_apply_eq_self]
    simp only [sub_apply,one_apply_eq_self,map_sub]
    abel
  have hp := modularPositiveCone_acute J hJ hright ξ hpos hζ
    (modularQuadratic_preserves_positiveCone J hJ hright ξ a hη)
  rw [haη,inner_add_right,inner_sub_right,inner_sub_right] at hp
  have he := norm_sub_sq_real ζ η
  rw [hζnorm,hηnorm] at he
  change ‖ζ-η‖ ^ 2 ≤ 4*δ
  nlinarith only [hp,hfirst,hsecond,hthird,he]

/-- The orbit comparison gives a square-root modulus on positive unit vectors. -/
theorem positiveCone_norm_sub_le_of_orbit_bound
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ = ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {η ζ : H} (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (hζ : ζ ∈ modularPositiveCone (M := M) J ξ)
    (hηnorm : ‖η‖ = 1) (hζnorm : ‖ζ‖ = 1)
    (u : unitary (H →L[ℂ] H)) (hu : (u : H →L[ℂ] H) ∈ M.commutant)
    {ε : ℝ} (hε : 0 ≤ ε) (hclose : ‖(u : H →L[ℂ] H) η-ζ‖ ≤ ε^2/4) :
    ‖ζ-η‖ ≤ ε := by
  have h := positiveCone_unitary_orbit_norm_sq_le J hJ hright hleft ξ hξ hpos
    hη hζ hηnorm hζnorm u hu
  nlinarith only [h,hclose,hε,norm_nonneg (ζ-η)]

/-- Zero distance between the two commutant-unitary orbits forces equality,
without needing a minimizing unitary. -/
theorem positiveCone_eq_of_orbit_distance_zero
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ = ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {η ζ : H} (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (hζ : ζ ∈ modularPositiveCone (M := M) J ξ)
    (hηnorm : ‖η‖ = 1) (hζnorm : ‖ζ‖ = 1)
    (hclose : ∀ δ : ℝ, 0 < δ → ∃ u : unitary (H →L[ℂ] H),
      (u : H →L[ℂ] H) ∈ M.commutant ∧ ‖(u : H →L[ℂ] H) η-ζ‖ ≤ δ) :
    ζ = η := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨u,hu,h⟩ := hclose (ε^2/4) (by positivity)
  simpa only [zero_add] using positiveCone_norm_sub_le_of_orbit_bound
    J hJ hright hleft ξ hξ hpos hη hζ hηnorm hζnorm u hu hε.le h

end

end KadisonKastler

end OAI

import OAI.Geometry.EinsteinFour.Quotient
import OAI.Geometry.EinsteinFour.Statement

namespace OAI

/-! Transport the metric quotient construction through an arbitrary
identification of the orientation cover with the round sphere. -/

namespace PositiveEinsteinFour

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The round-cover branch of the unoriented argument. All hypotheses refer
to the covering projection and its deck involution. -/
theorem classified_of_round_double_cover
    (g : SmoothMetric M) (a : ℝ) (ha : 0 < a)
    (e : N ≃ RoundSphere4) (τ : N → N)
    (hτ : Function.Involutive τ) (hfree : ∀ x, τ x ≠ x)
    (hτdistance : ∀ x y, roundDistance (e (τ x)) (e (τ y)) =
      roundDistance (e x) (e y))
    (p : N → M) (hp : Function.Surjective p)
    (hfibers : ∀ x y, p x = p y ↔ x = y ∨ x = τ y)
    (hdistance : ∀ x y, scaledEDistance g a (p x) (p y) =
      ENNReal.ofReal (min (roundDistance (e x) (e y))
        (roundDistance (e x) (e (τ y))))) : Classified g := by
  let τ' : RoundSphere4 → RoundSphere4 := fun x => e (τ (e.symm x))
  let p' : RoundSphere4 → M := fun x => p (e.symm x)
  have hτ' : Function.Involutive τ' := by
    intro x
    simp only [τ', Equiv.symm_apply_apply]
    rw [hτ (e.symm x), e.apply_symm_apply]
  have hfree' : ∀ x, τ' x ≠ x := by
    intro x hx
    apply hfree (e.symm x)
    have h := congrArg e.symm hx
    simpa only [τ', Equiv.symm_apply_apply] using h
  have hτdistance' : ∀ x y, roundDistance (τ' x) (τ' y) = roundDistance x y := by
    intro x y
    simpa only [τ', Equiv.apply_symm_apply] using hτdistance (e.symm x) (e.symm y)
  have hp' : Function.Surjective p' := by
    intro z
    obtain ⟨x, hx⟩ := hp z
    exact ⟨e x, by simpa only [p', Equiv.symm_apply_apply] using hx⟩
  have hfibers' : ∀ x y, p' x = p' y ↔ x = y ∨ x = τ' y := by
    intro x y
    rw [show p' x = p' y ↔ e.symm x = e.symm y ∨ e.symm x = τ (e.symm y) from
      hfibers (e.symm x) (e.symm y)]
    constructor
    · rintro (hxy | hxy)
      · exact Or.inl (e.symm.injective hxy)
      · right
        simpa only [τ', Equiv.apply_symm_apply] using congrArg e hxy
    · rintro (hxy | hxy)
      · exact Or.inl (congrArg e.symm hxy)
      · right
        simpa only [τ', Equiv.symm_apply_apply] using congrArg e.symm hxy
  have hdistance' : ∀ x y, scaledEDistance g a (p' x) (p' y) =
      ENNReal.ofReal (min (roundDistance x y) (roundDistance x (τ' y))) := by
    intro x y
    simpa only [p', τ', Equiv.apply_symm_apply] using
      hdistance (e.symm x) (e.symm y)
  exact ⟨a, ha, Or.inr (Or.inr (scaled_round_involution_quotient_is_projective
    g a τ' hτ' hτdistance' hfree' p' hp' hfibers' hdistance'))⟩

end

end PositiveEinsteinFour

end OAI

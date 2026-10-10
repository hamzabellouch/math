import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.BilateralBeta
import OAI.Analysis.RieszRectifiability.Flatness.ApproximatePlaneFits

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_bilateral_plane_error_lt {n d : ℕ} (hnd : n ≤ d)
    (μ : Measure (Ambient d)) (a : Ambient d) (r ε : ℝ)
    (hbeta : bilateralBeta n μ a r < ε) :
    ∃ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S ∧ bilateralPlaneError μ a r S < ε := by
  obtain ⟨S, hS⟩ := exists_affine_n_plane hnd
  have hne : {t : ℝ | ∃ T : AffineSubspace ℝ (Ambient d),
      IsAffineNPlane n T ∧ t = bilateralPlaneError μ a r T}.Nonempty :=
    ⟨bilateralPlaneError μ a r S, S, hS, rfl⟩
  obtain ⟨t, ⟨T, hT, ht⟩, hlt⟩ := exists_lt_of_csInf_lt hne hbeta
  exact ⟨T, hT, ht ▸ hlt⟩

theorem bilateralPlaneError_lt_pointwise {n d : ℕ}
    (μ : Measure (Ambient d)) (hμ : μ.support.Nonempty) (a : Ambient d)
    (r ε : ℝ) (hr : 0 < r) (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S)
    (he : bilateralPlaneError μ a r S < ε) :
    (∀ x ∈ ball a r, x ∈ μ.support → infDist x (S : Set (Ambient d)) < ε * r) ∧
    (∀ x ∈ ball a r, x ∈ S → infDist x μ.support < ε * r) := by
  have he' : directedBallDeviation μ.support (S : Set (Ambient d)) a r +
      directedBallDeviation (S : Set (Ambient d)) μ.support a r < ε * r :=
    (div_lt_iff₀ hr).mp he
  have h1 := directedBallDeviation_nonneg μ.support (S : Set (Ambient d)) a r
  have h2 := directedBallDeviation_nonneg (S : Set (Ambient d)) μ.support a r
  constructor
  · intro x hx hxs
    have hv : infDist x (S : Set (Ambient d)) ≤
        directedBallDeviation μ.support (S : Set (Ambient d)) a r :=
      le_csSup (directedBallDeviation_bddAbove μ.support (S : Set (Ambient d)) hS.1 a r)
        ⟨x, ⟨hx, hxs⟩, rfl⟩
    linarith
  · intro x hx hxs
    have hv : infDist x μ.support ≤ directedBallDeviation (S : Set (Ambient d)) μ.support a r :=
      le_csSup (directedBallDeviation_bddAbove (S : Set (Ambient d)) μ.support hμ a r)
        ⟨x, ⟨hx, hxs⟩, rfl⟩
    linarith

end

end RieszRectifiability

end OAI
